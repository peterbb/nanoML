open Printf

module TypeOp = struct
    type t = Arrow
    let eq _ _ = true
end

module Type = Constraint.MakeLang(TypeOp)

let arrow t0 t1 = Type.App (TypeOp.Arrow, [t0; t1])

module C = Constraint.Make(Type)

let rec gen_term ctx term typ = 
    let open Surface_syntax.Term in
    match term with

    | Var x ->
        C.app_ (List.assoc x ctx) typ

    | App (t0, t1) ->
        C.ex_ (fun a ->
              (C.and_ (gen_term ctx t0 (arrow a typ))
                      (gen_term ctx t1 a)))
    | Fun (name, t) ->
        C.ex_ (fun a ->
        C.ex_ (fun b ->
            C.and_ (C.eq_ typ (arrow a b))
                   (C.def_ a (fun x -> gen_term ((name, x) :: ctx) t b))
        ))
    | Let (name, t0, t1) ->
        C.let_ (fun a -> gen_term ctx t0 a)
               (fun x -> gen_term ((name, x) :: ctx) t1 typ)



let to_string t =
    let open TypeOp in
    let open Type in
    let rec collect = function
        | Var x -> [x]
        | App (Arrow, [t0; t1]) -> collect t0 @ collect t1
        | App (Arrow, _) -> failwith "TypeOp.Arrow: wrong number of arguments"
    in

    let rec dedup = function
        | [] -> []
        | x :: xs ->
            if List.mem x xs then
                dedup xs
            else
                x :: dedup xs
    in

    let next_var =
        let k = ref 0 in
        let alph = "abcdefghijklmnopqrstuvwxyz" in
        let m = String.length alph in
        let a i = String.get alph (i mod m) in
        fun () ->
            let i = !k in
            k := i + 1;
            if (i / m) = 0 then sprintf "%c" (a i)
            else sprintf "%c%d" (a i) (i / m)
    in
    let vars = collect t |> List.rev |> dedup |> List.rev in
    let map = List.map (fun i -> (i, next_var ())) vars in
    let tr i = List.assoc i map in

    let rec display = function
        | Var i -> tr i 
        | App (Arrow, [Var i; t]) ->
            sprintf "%s -> %s" (tr i) (display t)
        | App (Arrow, [t0; t1]) ->
            sprintf "(%s) -> %s" (display t0) (display t1)
        | App (Arrow, _) ->
            failwith "TypeOp.Arrow: wrong number of arguments"
    in display t
    

let id_tyvar_map = ref []

let rec gen_program ctx = function
    | [] -> C.true_
    | (name, term) :: rest ->
        C.let_ (fun a ->
                    id_tyvar_map := (name, a) :: !id_tyvar_map;
                    gen_term ctx term a) 
               (fun x ->
                 gen_program ((name, x) :: ctx) rest)
        
let type_check program =
    let c = gen_program [] program in
    match C.solve c with
    | Ok (map, _) ->
        let f (a, t) = (Type.Var a, t) in
        let map = List.map f map in
        List.iter (fun (name, a) ->
                    let ty = List.assoc a map in
                    printf "%s : %s\n" name (to_string ty))
            !id_tyvar_map
        
    | Error msg ->
        eprintf "type checking error: %s\n" msg

