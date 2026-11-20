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

(* arith_type to string*)
let rec string_of_type(t : arith_type) : string =
  match t with
  | INT -> "Int"
  | BOOL -> "Bool"
  (* includes parenthises for nested types*)
  | FUN (t1, t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | PAIR (t1, t2) -> "(" ^ string_of_type t1 ^ " * " ^ string_of_type t2 ^ ")"


(* file name to whole file in a string , from_channel also from 10.2.4.6*)
let parse_file (filename : string) : expr =
  let input = open_in filename in
  let lexbuf = Lexing.from_channel input in
  let ast = Parser.prog Lexer.read lexbuf in
  close_in input;
  ast


(* takes a program and parses it, type checks it, and evaluates it. Try with from textbook 3.10*)
let run (filename : string) : unit =
  try
    (* start type checking: *)
    let ast = parse_file filename in
    begin match type_of_expr (empty_context, ast) with
    | None -> print_endline "Program type error: not well typed"
    | Some _ -> let v = multistep ast in
      (* Well typed used from 10.5.3 *)
      if is_val v then print_endline (string_of_expr v)
      else print_endline ("Stucj at runtime error: " ^ string_of_expr v)
    end
  with
  (* token error handling *)
  | Parser.Error -> print_endline("Error: Parser issue")
  (* character error handling *)
  | Failure msg -> print_endline ("Error during lexing: " ^ msg)
  (* file error handling *)
  | Sys_error msg -> print_endline ("Error with file : " ^ msg)
