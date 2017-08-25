
open Format

let compile_var ch x =
    fprintf ch "x%s" x

let rec compile_term ch =
    let open Surface_syntax.Term in
    function
    | Var x ->
        compile_var ch x
    | App (t0, t1) ->
        fprintf ch "@[<2>(%a@ %a)@]" compile_term t0 compile_term t1
    | Fun (x, t) ->
        fprintf ch "@[<2>(lambda (%a)@ %a)@]" compile_var x compile_term t
    | Let (x, t0, t1) ->
        fprintf ch "@[<2>(let@ ((%a %a))@ %a)@]"
            compile_var x
            compile_term t0
            compile_term t1

let rec compile ch = function
    | [] -> fprintf ch "\n"
    | (name, term) :: program ->
        fprintf ch "@[(define %a_@ %a)@]@."
            compile_var name
            compile_term term;
        compile ch program
