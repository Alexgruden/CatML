(*
Problem 3
Alexander Gruden and Tre Oconnell

References:
CS 3110 textbook - OCaml Programming: Correct + Efficient + Beautiful
https://cs3110.github.io/textbook/cover.html
*)
open Lang

(* parse is from textbook 10.2.4.5 *)
let parse (s : string) : expr =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast

