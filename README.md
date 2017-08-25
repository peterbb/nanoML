# nanoML
An implementation of a minimalistic ML language.

## Syntax

    <program> ::= <eof>
                | "let" <name> "=" <expr> <program>

    <expr>    ::= <expr1>
                | "let" <name> "=" <expr> "in" <expr>
                | "fun" <name>+ "->" <expr>

    <expr1>   ::= <expr0>
                | <expr1> <expr0>

    <expr0>   ::= <name>
                | "(" <expr> ")"

