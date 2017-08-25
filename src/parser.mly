%token <string> LNAME
%token FUN IN LET
%token EQ ARROW
%token LPAR RPAR
%token EOF

%{
    open Surface_syntax.Term
%}

%start <Surface_syntax.Program.t> program
%%

program:
    | ds = list(decl); EOF
        { ds }

decl:
    | LET; n = LNAME; EQ t = term
        { (n, t) }

term:
    | LET; n = LNAME; EQ; t0 = term; IN; t1 = term
        { Let (n, t0, t1) }
    | FUN; xs = nonempty_list(LNAME); ARROW; t = term
        { let lam x t = Fun (x, t) in
          List.fold_right lam xs t }
    | t = term1
        { t }

term1:
    | t0 = term1; t1 = term0
        { App (t0, t1) }
    | t = term0
        { t }

term0:
    | x = LNAME
        { Var x }
    | LPAR; t = term; RPAR 
        { t }
    

