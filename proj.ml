(* Marian Sigler
 * Projet de programmation
 * UPS Toulouse, L3 Informatique, 2013/14
 * License: WTFPL
 *)

(* questions:
    * entier = integer?
    * batteries
 *)

open Printf

(* helper functions *)
let println_string s =
    printf "%s\n%!" s (* flush to ensure proper output ordering *)
;;

(* stores variables' values *)
module Environment = Map.Make(Char);;

exception DivZero;;
exception InvalidVariable;;

(* / helper functions *)

type expr = Int of int
          | Var of char
          | Sum of expr * expr
          | Diff of expr * expr
          | Prod of expr * expr
          | Div of expr * expr (* integer division *)
          | Neg of expr;;

let fig1 = Sum (Sum (Prod (Var 'x', Int 1), Neg (Var 'y')),
                Diff (Int 5, Int 7));;
let fig2 = Sum (Sum (Var 'x', Var 'y'), Int 5);;
let circumf_rectangle = Sum (Prod (Int 2, Var 'x'), Prod (Int 2, Var 'y'));;

(* show : expr -> string *)
let rec show =
    let showop op l r = "(" ^ show l ^ op ^ show r ^ ")" in
    function
        | Int i -> string_of_int i
        | Var v -> String.make 1 v
        | Sum (l,r) -> showop "+" l r
        | Diff (l,r) -> showop "-" l r
        | Prod (l,r) -> showop "*" l r
        | Div (l,r) -> showop "/" l r
        | Neg e -> "(-" ^ show e ^ ")"
;;

let print_expr e = println_string (show e);;

print_expr fig1;;
print_expr fig2;;
print_expr circumf_rectangle;;


(* eval : expr -> int *)
let rec eval env =
    let evalop op l r = op (eval env l) (eval env r) in
    function
        | Int i -> i
        | Var v -> if Environment.mem v env
                      then Environment.find v env
                      else raise InvalidVariable
        | Sum (l,r) -> evalop (+) l r
        | Diff (l,r) -> evalop (-) l r
        | Prod (l,r) -> evalop ( * ) l r
        | Div (l,r) -> if (eval env r) <> 0
                        then evalop (/) l r
                        else raise DivZero
        | Neg e -> -(eval env e)
;;

let env1 = Environment.add 'x' 2 (Environment.add 'y' 4 (Environment.empty));;

print_int (eval env1 fig1);;
