{
open Parser
}

let white = [' ' '\t']+
let digit = ['0'-'9']
let int = '-'? digit+
let letter = ['a'-'z' 'A'-'Z']
let id = letter+

rule read =
  parse
  | white { read lexbuf }
  | "True" { TRUE }
  | "False" { FALSE }
  | "And" { AND }
  | "Or" { OR }
  | "Not" { NOT }
  | "*" { TIMES }
  | "+" { PLUS }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "Let" { LET }
  | "=" { EQUALS }
  | "," { COMMA }
  | "In" { IN }
  | "If" { IF }
  | "Then" { THEN }
  | "Else" { ELSE }
  | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | eof { EOF }
  | "First" { FIRST }
  | "Second" { SECOND }
  | "Fun" { FUN }
  | "->" { ARROW }
  | "Fix" { FIX }
  | "." { DOT }
  | ":" { COLON }
  | "Int" { INT_TYPE }
  | "Bool" { BOOL_TYPE }
  | id { ID (Lexing.lexeme lexbuf) }
