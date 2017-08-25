
module Term = struct
    type t =
        | Var of string
        | App of t * t
        | Let of string * t * t
        | Fun of string * t
end

module Program = struct
    type t = (string * Term.t) list
end


let rec dump_term = 
    let open Term in
    let open Printf in 
    function
    | Var x ->
        printf "%s" x
    | App (t0, t1) ->
        printf "(";
        dump_term t0;
        printf " ";
        dump_term t1;
        printf ")"
    | Fun (x, t) ->
        printf "(";
        printf "fun %s -> " x;
        dump_term t;
        printf ")"
    | Let (x, t0, t1) ->
        printf "(";
        printf "let %s = " x;
        dump_term t0;
        printf " in ";
        dump_term t1;
        printf ")"
        
let rec dump =
    let open Printf in
    function
    | [] -> ()
    | (name, term) :: rest ->
        printf "let %s = " name;
        dump_term term;
        printf "\n";
        dump rest
        
    

