{
    open Lexing
    open Parser
}

let newline = "\r" | "\n" | "\r\n"
let white = " " | "\t"

let lchar = ['a'-'z']
let uchar = ['A'-'Z']
let char = lchar | uchar
let digit = ['0'-'9']
let idchar = char | digit | [ '_' ]
let lname = lchar idchar*

rule read = parse
    | newline       { new_line lexbuf; read lexbuf }
    | white+        { read lexbuf }
    | eof           { EOF }
    | "(*"          { comment lexbuf; read lexbuf }

    | "="           { EQ }
    | "->"          { ARROW }

    | "("           { LPAR }
    | ")"           { RPAR }
    
    | "let"         { LET }
    | "in"          { IN }
    | "fun"         { FUN }

    | lname as n    { LNAME n }

    
and comment = parse
    | "(*"          { comment lexbuf; comment lexbuf }
    | "*)"          { () }
    | newline       { new_line lexbuf; comment lexbuf }
    | _             { comment lexbuf }
    | eof           { failwith "lexer: comment not terminated" }
