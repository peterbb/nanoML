
module type OP = sig
    type t
    val eq : t -> t -> bool
end

module type VAR = sig
    type t
    val fresh : unit -> t
    val eq : t -> t -> bool
end

module Var = struct
    type t = int

    let fresh =
        let k = ref 0 in
        fun () ->
        let i = !k in
        k := i + 1;
        i

    let eq i j = i = j
end

module type LANG = sig
    module O : OP
    module V : VAR

    type t =
        | Var of V.t
        | App of O.t * t list
end

module MakeLang (O : OP) = struct
    module O = O
    module V = Var

    type t =
        | Var of V.t
        | App of O.t * t list
end


module Make (L : LANG) = struct

    type term = L.t
    type term_var = L.V.t

    type var = int

    let fresh_tmvar = 
        let k = ref 0 in
        fun () -> 
            let i = !k in
            k := i + 1;
            i

    module General_constraints = struct
        type t = 
            | True
            | Eq    of term * term
            | And   of t * t
            | Ex    of term_var * t
            | Let   of int * term_var * t * t
            | App   of int * term

        let true_ = True

        let and_ c0 c1 = And (c0, c1)

        let eq_ t0 t1 = Eq (t0, t1)

        let ex_ f =
            let a = L.V.fresh () in
            Ex (a, f (L.Var a))

        let let_ c0 c1 =
            let x = fresh_tmvar () in
            let a = L.V.fresh () in
            Let (x, a, c0 (L.Var a), c1 x)

        let def_ a f =
            let_ (fun b -> Eq (a, b)) f

        let app_ x t = App (x, t)
    end

    include General_constraints

    (* Normal form *)
    module Normal_form = struct
        type t = {
            exs  : term_var list;
            lets : (int * term_var * t) list;
            eqs  : (term * term) list;
            apps : (int * term) list;
        }

        let true_ = { exs = []; lets = []; eqs = []; apps = []; }

        let and_ c0 c1 = {
            exs = c0.exs @ c1.exs;
            lets = c0.lets @ c1.lets;
            eqs = c0.eqs @ c1.eqs;
            apps = c0.apps @ c1.apps;
        }

        let ex_ x c = { c with exs = x :: c.exs }

        let eq_ t0 t1 = { exs = []; lets = []; eqs = [t0, t1]; apps = []; }

        let app_ x t = { exs = []; lets = []; eqs = []; apps = [x, t]; }

        let let_ x a c0 c1 =
            { c1 with
                lets = (x, a, c0) :: c1.lets;
            }

        let rec import = function
            | True -> true_
            | And (c0, c1) -> and_ (import c0) (import c1)
            | Eq (t0, t1) -> eq_ t0 t1
            | Ex (a, c) -> ex_ a (import c)
            | Let (x, a, c0, c1) -> let_ x a (import c0) (import c1)
            | App (x, t) -> app_ x t

        let rec sub_ty ty a = function
            | L.Var b when a = b -> ty
            | L.Var _ as t -> t
            | L.App (op, args) ->
                L.App (op, List.map (sub_ty ty a) args)

        let rec sub ty a { exs; lets; eqs; apps; } =

            let f (x, b, c) = (x, b, sub ty a c) in
            let lets = List.map f lets in

            let f (t0, t1) = (sub_ty ty a t0, sub_ty ty a t1) in
            let eqs = List.map f eqs in

            let f (x, t) = (x, sub_ty ty a t) in
            let apps = List.map f apps in

            { exs; lets; eqs; apps; }

        let join cs =
            let join f = List.concat (List.map f cs) in
            { exs = join (fun c -> c.exs);
              lets = join (fun c -> c.lets);
              eqs = join (fun c -> c.eqs);
              apps = join (fun c -> c.apps);
            }
              

        let rec inline_def x a c { exs; lets; eqs; apps; }= 
            let inline = inline_def x a c in

            let f (y, b, c0) = (y, b, inline c0) in
            let lets = List.map f lets in

            let f (x', _) = x = x' in 
            let to_be_inlined, apps = List.partition f apps in

            let f (_, ty) = sub ty a c in
            let inlined_constraints = List.map f to_be_inlined in

            join ({ exs; lets; eqs; apps; } :: inlined_constraints)
    end

    module Normal_form2 = struct
        type t = {
            exs : term_var list;
            eqs : (term * term) list;
        }

        let and_ c0 c1 = {
            exs = c0.exs @ c1.exs;
            eqs = c0.eqs @ c1.eqs;
        }
                

        module N1 = Normal_form

        let rec import c =
            match c with
            | N1.{ lets = []; apps = []; exs; eqs; } ->
                { exs; eqs }
            | N1.{ lets = (x, a, c) :: lets; exs; eqs; apps; } ->
                let c' = import c in
                import (N1.inline_def x a c N1.{ lets ; exs; eqs; apps; })
                |> and_ c'
                |> fun c -> { c with exs = a :: c.exs }
            | N1.{ lets =[]; apps = (x, _) :: _ } ->
                failwith "constraint contains free variable"


        let option_map f = function
            | Some x -> Some (f x)
            | None -> None

        let rec option_flatten = function
            | [] -> Some []
            | None :: _ -> None
            | Some xs :: rest ->
                option_map (fun ys -> xs @ ys) (option_flatten rest)


        let rec simplify = function
            | (L.Var x, L.Var y) when x = y ->
                Some []
            | L.App (op0, args0), L.App (op1, args1) ->
                if L.O.eq op0 op1 then
                    simplify_args args0 args1
                else
                    None
            | c -> Some [c]
        and simplify_args args0 args1 =
            match List.map2 (fun x y -> simplify (x, y)) args0 args1 with
            | xs -> option_flatten xs
            | exception Invalid_argument _ -> None

        let simp_all eqs =
            let rec loop acc = function
                | [] -> Some acc
                | None :: _ -> None
                | Some xs :: rest ->
                    loop (xs @ acc) rest
            in loop [] (List.map simplify eqs)


        let rec cyclic x = function
            | L.Var y -> x = y
            | L.App (_, args) -> List.exists (cyclic x) args


        let rec find_noncyclic candidates = function
            | [] -> None
            | (L.Var x, t) :: rest
                    when (not (cyclic x t)) && (List.mem x candidates) -> 
                Some (x, t, rest)
            | (t, L.Var x) :: rest
                    when (not (cyclic x t)) && (List.mem x candidates) -> 
                Some (x, t, rest)
            | eq :: rest ->
                begin match find_noncyclic candidates rest with
                | Some (x, t, rest) -> Some (x, t, eq :: rest)
                | None -> None
                end
                
        let solve c =
            let rec sub t x = function
                | L.Var y when x = y -> t
                | L.Var _ as u -> u
                | L.App (op, args) ->
                    L.App (op, List.map (sub t x) args)
            in
            let rec loop map exs eqs =
                match simp_all eqs with
                | None -> Error "error simplifying"
                | Some [] -> Ok (map, exs)
                | Some xs ->
                    begin match find_noncyclic exs xs with
                    | None ->
                        Error "cycle"
                    | Some (x, t, eqs) ->
                        let exs = List.filter (fun y -> x <> y) exs in

                        let f (y, s) = (y, sub t x s) in
                        let map = List.map f map in
                
                        let f (t0, t1) = (sub t x t0, sub t x t1) in
                        let eqs = List.map f eqs in
                        loop ((x, t) :: map) exs eqs
                    end
            
            in loop [] c.exs c.eqs
    end

    type subst = (term_var * term) list

    let solve c =
        Normal_form.import c
        |> Normal_form2.import
        |> Normal_form2.solve

end
