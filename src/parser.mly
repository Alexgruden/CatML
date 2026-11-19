%{
open Lang
%}

%token <int> INT
%token <string> ID
%token TRUE
%token FALSE
%token AND
%token OR
%token NOT
%token TIMES
%token PLUS
%token LPAREN
%token RPAREN
%token LET
%token EQUALS
%token COMMA
%token IN
%token IF
%token THEN
%token ELSE
%token EOF
%token FIRST
%token SECOND
%token FUN
%token ARROW
%token FIX
%token DOT
%token COLON
%token INT_TYPE
%token BOOL_TYPE

%nonassoc LOW_PREC
%nonassoc IN
%nonassoc ELSE
%left OR
%left AND
%nonassoc EQUALS
%left PLUS
%right ARROW
%left TIMES
%nonassoc NOT
%nonassoc FIRST
%nonassoc SECOND
(*%left APP*)

%start <Lang.expr> prog

%type <Lang.expr> expr
%type <Lang.arith_type> arith_type

%%

prog:
  | e = expr; EOF { e }
  ;

expr:
  | i    = INT { Int i }
  | x    = ID  { Var x }
  | TRUE       { Bool true }
  | FALSE      { Bool false }
  | e1 = expr; OR; e2 = expr { Or (e1, e2) }
  | e1 = expr; AND; e2 = expr { And (e1, e2) }
  | NOT; e = expr { Not e }
  | e1 = expr; EQUALS; e2 = expr { Equal (e1, e2) }
  | e1 = expr; TIMES;  e2 = expr { Mult(e1, e2) }
  | e1 = expr; PLUS;   e2 = expr { Plus(e1, e2) }
  | LET; x = ID; EQUALS; e1 = expr; IN; e2 = expr   { Let (x, e1, e2) }
  | IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr { If (e1, e2, e3) }
  | LPAREN; e=expr; RPAREN {e}
  | LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { Pair (e1, e2) }
  | FIRST; e = expr %prec FIRST { First e }
  | SECOND; e = expr %prec SECOND { Second e }
  (*| e1 = expr; e2 = expr %prec APP{ App (e1, e2) }*)
  | FUN; x = ID; COLON; t = arith_type; ARROW; e = expr %prec LOW_PREC { Fun (x, t, e) }
  | FIX; f = ID; DOT; x = ID; COLON; t1 = arith_type; COLON; t2 = arith_type; ARROW; e = expr %prec LOW_PREC { Fix (f, x, t1, t2, e) }
  ;

arith_type:
  | INT_TYPE  { Lang.INT }
  | BOOL_TYPE { Lang.BOOL }
  | t1 = arith_type; TIMES; t2 = arith_type { Lang.PAIR (t1, t2) }
  | t1 = arith_type; ARROW; t2 = arith_type { Lang.FUN (t1, t2) }
  ;