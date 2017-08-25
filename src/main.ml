
let open_in_with filename body =
    let ch = open_in filename in
    try
        let result = body ch in
        close_in ch;
        result
    with
    | e -> (close_in ch; raise e)

let set_filename pos_fname lexbuf =
    let open Lexing in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname };
    lexbuf

let (@) f g = fun x -> f (g x)

let parse_channel filename =
    Parser.program Lexer.read
    @ set_filename filename
    @ Lexing.from_channel


let parse filename =
    open_in_with filename (parse_channel filename)


let usage prog =
    Printf.eprintf "usage: %s <filename>\n" prog;
    exit 1

let main = function
    | [_; filename] ->
        let program = parse filename in
        Surface_syntax.dump program;
        Type_check.type_check program;
        let och = open_out (filename ^ ".s") in
        let form = Format.formatter_of_out_channel och in
        Backend.compile form program;
        close_out och;
        Printf.printf "done.\n"
    | _ -> usage "nanoml"

let () = Sys.argv |> Array.to_list |> main
