open Printf

module C = Constraint

let rec gen_term ctx term typ = 
    let open Surface_syntax.Term in
    match term with

    | Var x ->
        C.app_ (List.assoc x ctx) typ

    | App (t0, t1) ->
        C.ex_ (fun a ->
              (C.and_ (gen_term ctx t0 (C.Type.Arrow (a, typ)))
                      (gen_term ctx t1 a)))
    | Fun (name, t) ->
        C.ex_ (fun a ->
        C.ex_ (fun b ->
            C.and_ (C.eq_ typ (C.Type.Arrow (a, b)))
                   (C.def_ a (fun x -> gen_term ((name, x) :: ctx) t b))
        ))
    | Let (name, t0, t1) ->
        C.let_ (fun a -> gen_term ctx t0 a)
               (fun x -> gen_term ((name, x) :: ctx) t1 typ)


let id_tyvar_map = ref []

let to_string t =
    let open C.Type in
    let rec collect = function
        | Var x -> [x]
        | Arrow (t0, t1) -> collect t0 @ collect t1
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
        fun () ->
            let i = !k in
            k := i + 1;
            if (i / m) = 0 then
                sprintf "%c" (String.get alph (i mod m))
            else
                sprintf "%c%d" (String.get alph (i mod m)) (i / m)
        
    in
    let vars = collect t |> List.rev |> dedup |> List.rev in
    let map = List.map (fun i -> (i, next_var ())) vars in
    let tr i = List.assoc i map in

    let rec display = function
        | Var i -> tr i 
        | Arrow (Var i, t) ->
            sprintf "%s -> %s" (tr i) (display t)
        | Arrow (t0, t1) ->
            sprintf "(%s) -> %s" (display t0) (display t1)
    in display t
    
    

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
        let map = List.map (fun (a, t) -> (C.Type.Var a, t)) map in
        List.iter (fun (name, a) ->
                    let ty = List.assoc a map in
                    printf "%s : %s\n" name (to_string ty))
            !id_tyvar_map
        
    | Error msg ->
        eprintf "type checking error: %s\n" msg

