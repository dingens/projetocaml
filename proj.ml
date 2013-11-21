(* Marian Sigler
 * Projet de programmation
 * UPS Toulouse, L3 Informatique, 2013/14
 * License: WTFPL
 *)

(* questions:
    * entier = integer?
    *
 *)

(* helper functions *)
let println_string s =
    print_string (s ^ "\n")
;;

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
        | Neg e -> "(-" ^ show e
;;

let print_expr e = println_string (show e);;

print_expr fig1;;
print_expr fig2;;
print_expr circumf_rectangle;;



