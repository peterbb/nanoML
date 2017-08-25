
module Type = struct
    type t =
        | Var   of int
        | Arrow of t * t
end

let rec type_to_string = function
    | Type.Var x ->
        Printf.sprintf "%d" x
    | Type.Arrow (t0, t1) ->
        Printf.sprintf "(%s -> %s)" (type_to_string t0) (type_to_string t1)

let fresh_tyvar = 
    let k = ref 0 in
    fun () ->
        let i = !k in
        k := i + 1;
        i

let fresh_tmvar = 
    let k = ref 0 in
    fun () -> 
        let i = !k in
        k := i + 1;
        i

type t = 
    | True
    | Eq    of Type.t * Type.t
    | And   of t * t
    | Ex    of int * t
    | Let   of int * int * t * t
    | App   of int * Type.t

let let1 c0 c1 =
    let x = fresh_tmvar () in
    let a = fresh_tyvar () in
    Let (x, a, c0 (Type.Var a), c1 x)

let def a f =
    let1 (fun b -> Eq (a, b)) f

let ex f =
    let a = fresh_tyvar () in
    Ex (a, f (Type.Var a))

let rec dump_type =
    let pf = Printf.printf in
    function
    | Type.Var a ->
        pf "'%d" a
    | Type.Arrow (t0, t1) ->
        pf "("; dump_type t0; pf " -> "; dump_type t1; pf ")"

let rec dump =
    let pf = Printf.printf in
    function
    | True -> pf "true"
    | Eq (t0, t1) ->
        pf "("; dump_type t0; pf " = "; dump_type t1; pf ")"
    | And (c0, c1) ->
        pf "("; dump c0; pf " & "; dump c1; pf ")"
    | Ex (a, c) ->
        pf "(ex '%d " a; dump c; pf ")"
    | Let (x, a, c0, c1) ->
        pf "(let %d = ('%d. " x a; dump c0; pf ") in "; dump c1; pf ")"
    | App (x, t) ->
        pf "(%d " x; dump_type t; pf ")"

(* Normal form *)
module Normal_form = struct
    type t = {
        exs  : int list;
        lets : (int * int * t) list;
        eqs  : (Type.t * Type.t) list;
        apps : (int * Type.t) list;
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
            

    let rec pw = function
        | n when n <= 0 -> ()
        | n -> Printf.printf " "; pw (n - 1)

    let dump =
        let spf = Printf.sprintf in
        let pf = Printf.printf in
        let rec dump n { exs; lets; eqs; apps; } =
            (if exs <> [] then begin
                pw n;
                pf "ex %s.\n" (String.concat " "(List.map (spf "%d") exs))
            end);
            (if lets <> [] then begin
                pw n; pf "lets \n";
                List.iter (fun (x, a, c) ->
                            pw (n + 2); pf "%d = %d.\n" x a;
                            dump (n + 4) c)
                        lets
            end);
            (if eqs <> [] then begin
                pw n; pf "eqs:\n";
                List.iter (fun (t0, t1) ->
                            let t0 = type_to_string t0 in
                            let t1 = type_to_string t1 in
                            pw (n + 2); pf "%s = %s\n" t0 t1)
                    eqs
            end);
            (if apps <> [] then begin
                List.iter (fun (x, t) ->
                            let t = type_to_string t in
                            pw (n + 2); pf "%d @ %s\n" x t)
                    apps
            end)
        in
        dump 0

    let rec sub_ty ty a = function
        | Type.Var b when a = b -> ty
        | Type.Var _ as t -> t
        | Type.Arrow (t0, t1) -> Type.Arrow (sub_ty ty a t0, sub_ty ty a t1)

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
        exs : int list;
        eqs : (Type.t * Type.t) list;
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

    let dump {exs; eqs; } =
        let open Printf in
        printf "ex %s\n" (List.map (sprintf "%d") exs |> String.concat " ");
        List.iter (fun (t0, t1) ->
                    printf "%s = %s\n" (type_to_string t0) (type_to_string t1))
            eqs

    open Type
    let rec simplify = function
        | (Var x, Var y) when x = y ->
            Some []
        | Arrow (t0, s0), Arrow (t1, s1) ->
            begin match simplify (t0, t1), simplify (s0, s1) with
            | Some c0, Some c1 -> Some (c0 @ c1)
            | _ -> None
            end
        | (Var _, Arrow _) as c -> Some [c]
        | (Arrow _ as t0), (Var _ as t1) -> Some [t1, t0]
        | (Var _, Var _) as c -> Some [c]

    let simp_all eqs =
        let rec loop acc = function
            | [] -> Some acc
            | None :: _ -> None
            | Some xs :: rest ->
                loop (xs @ acc) rest
        in loop [] (List.map simplify eqs)


    let rec cyclic x = function
        | Var y -> x = y
        | Arrow (t0, t1) -> cyclic x t0 || cyclic x t1


    let rec find_noncyclic candidates = function
        | [] -> None
        | (Var x, t) :: rest
                when (not (cyclic x t)) && (List.mem x candidates) -> 
            Some (x, t, rest)
        | (t, Var x) :: rest
                when (not (cyclic x t)) && (List.mem x candidates) -> 
            Some (x, t, rest)
        | eq :: rest ->
            begin match find_noncyclic candidates rest with
            | Some (x, t, rest) -> Some (x, t, eq :: rest)
            | None -> None
            end
            
    open Printf
        
    let solve c =
        let rec sub t x = function
            | Var y when x = y -> t
            | Var y -> Var y
            | Arrow (t0, t1) -> Arrow (sub t x t0, sub t x t1)
        in
        let rec loop map exs eqs =
            printf "------- debug --------\n";
            printf "map:\n";
            List.iter (fun (x, t) ->
                printf "\t%d = %s\n" x (type_to_string t))
                map;
            printf "exs:";
            List.iter (printf " %d") exs;
            printf "\n";
            printf "eqs:\n";
            List.iter (fun (t0, t1) ->
                    printf "\t%s = %s\n" (type_to_string t0)(type_to_string t1))
                eqs;
            match simp_all eqs with
            | None -> Error "error simplifying"
            | Some [] -> Ok (map, exs)
            | Some xs ->
                begin match find_noncyclic exs xs with
                | None ->
                    let f (t0, t1) = sprintf "\t%s = %s"
                        (type_to_string t0) (type_to_string t1)
                    in
                    Error (sprintf "only cycles.\n exs: %s\neqs:%s\n"
                            (List.map (sprintf "%d") exs |> String.concat " ")
                            (List.map f xs |> String.concat "\n"))
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

open Printf

let solve c =
    let cn = Normal_form.import c in
    let cn = Normal_form2.import cn in
    Normal_form2.solve cn

