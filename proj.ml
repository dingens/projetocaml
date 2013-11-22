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
let fig3 = Sum (Sum (Prod (Var 'x', Int 1), Neg (Diff (Int 0, Var 'y'))),
                Diff(Int 5, Prod(Int 0, Var 'z')))
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

let print_expr ?n e = match n with
    | None -> println_string (show e)
    | Some note -> println_string (note ^ ": " ^ show e);;

print_expr fig1 ~n:"Fig. 1";;
print_expr fig2 ~n:"Fig. 2";;
print_expr circumf_rectangle ~n:"Circumference of a rectangle";;


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
print_string "\n\n";;

(* simplify1 : expr -> expr *)
let rec simplify1 = function
    (* neutral elements *)
    | Sum (Int 0, r) -> simplify1 r
    | Sum (l, Int 0) -> simplify1 l
    | Prod (Int 1, r) -> simplify1 r
    | Prod (l, Int 1) -> simplify1 l
    | Diff (l, Int 0) -> simplify1 l
    | Diff (Int 0, r) -> simplify1 (Neg r)
    (* absorbing elements *)
    | Prod (Int 0, _) -> Int 0
    | Prod (_, Int 0) -> Int 0
    | Div (Int 0, _) -> Int 0
    (* negation elimination *)
    | Neg (Neg a) -> simplify1 a
    | Sum (l, Neg r) -> simplify1 (Diff (l, r))
    | Diff (l, Neg r) -> simplify1 (Sum (l, r))
    (* defaults *)
    | Int i -> Int i
    | Var v -> Var v
    | Sum (l, r) -> Sum (simplify1 l, simplify1 r)
    | Prod (l, r) -> Prod (simplify1 l, simplify1 r)
    | Diff (l, r) -> Diff (simplify1 l, simplify1 r)
    | Div (l, r) -> Div (simplify1 l, simplify1 r)
    | Neg e -> Neg (simplify1 e)
;;
(* I don't detect division by zero, because I consider it more beautiful
 * when such runtime errors appear only in one place. This way simplify always
 * succeeds.
 *)

(* Because it is "too late" for simplification opportunities that only appear
 * after we have changed something "downwards" the calculation tree, we have to
 * do this simplification process several times until the expression doesn't
 * change anymore.
 *
 * Possible optimisation: use flags to mark changes so we don't have to recheck
 * all subtrees in every round. #TODO
 * Or: Proceed from bottom to top. That way it should be doable in one run.
*)

(* simplify : expr -> expr *)
let rec simplify e =
    let e' = simplify1 e in
    if e = e' then e else simplify e'
;;

print_expr fig3 ~n:"Fig. 3 (original)";;
print_expr (simplify fig3) ~n:"Fig. 3 (simplified)";;

let test = Neg (Diff (Int 0, Int 3));;
print_expr (simplify1 test);;
print_expr (simplify test);;
let test = Prod (Int 3, Sum (Int 0, Int 0));;
print_expr (simplify1 test);;
print_expr (simplify test);;

let test = Sum (Prod (Int 0, Int 5), (Neg (Int 4)));;
print_expr (simplify test);;
let test = Sum (Prod (Int 1, Int 5), (Neg (Int 4)));;
print_expr (simplify test);;
let test = Sum (Prod (Int 2, Int 5), (Neg (Int 4)));;
print_expr (simplify test);;
