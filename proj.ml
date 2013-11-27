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
module Environment = Map.Make(Char);;
module CSet = Set.Make(Char);;

exception DivZero;;
exception InvalidVariable;;
exception EmptyList;;

let println_string s =
    printf "%s\n%!" s (* flush to ensure proper output ordering *)
;;

let print_cset s = println_string (String.concat " " (List.map (String.make 1)
(CSet.elements s)));;

let print_environment e = Environment.iter (printf "%c=%d ") e;;
let println_environment e = print_environment e; print_newline ();;

(* / helper functions *)

type expr = Int of int
          | Var of char
          | Add of expr * expr
          | Sub of expr * expr
          | Mul of expr * expr
          | Div of expr * expr (* integer division *)
          | Neg of expr;;

let fig1 = Add (Add (Mul (Var 'x', Int 1), Neg (Var 'y')),
                Sub (Int 5, Int 7));;
let fig2 = Add (Add (Var 'x', Var 'y'), Int 5);;
let fig3 = Add (Add (Mul (Var 'x', Int 1), Neg (Sub (Int 0, Var 'y'))),
                Sub(Int 5, Mul(Int 0, Var 'z')))
let circumf_rectangle = Add (Mul (Int 2, Var 'x'), Mul (Int 2, Var 'y'));;
let num_fingers = Mul (Int 2, Int 5);;

(* show : expr -> string *)
let rec show =
    let showop op l r = "(" ^ show l ^ op ^ show r ^ ")" in
    function
        | Int i -> string_of_int i
        | Var v -> String.make 1 v
        | Add (l,r) -> showop "+" l r
        | Sub (l,r) -> showop "-" l r
        | Mul (l,r) -> showop "*" l r
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
        | Add (l,r) -> evalop (+) l r
        | Sub (l,r) -> evalop (-) l r
        | Mul (l,r) -> evalop ( * ) l r
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
    | Add (Int 0, r) -> simplify1 r
    | Add (l, Int 0) -> simplify1 l
    | Mul (Int 1, r) -> simplify1 r
    | Mul (l, Int 1) -> simplify1 l
    | Sub (l, Int 0) -> simplify1 l
    | Sub (Int 0, r) -> simplify1 (Neg r)
    (* absorbing elements *)
    | Mul (Int 0, _) -> Int 0
    | Mul (_, Int 0) -> Int 0
    | Div (Int 0, _) -> Int 0
    (* negation elimination *)
    | Neg (Neg a) -> simplify1 a
    | Add (l, Neg r) -> simplify1 (Sub (l, r))
    | Sub (l, Neg r) -> simplify1 (Add (l, r))
    (* defaults *)
    | Int i -> Int i
    | Var v -> Var v
    | Add (l, r) -> Add (simplify1 l, simplify1 r)
    | Mul (l, r) -> Mul (simplify1 l, simplify1 r)
    | Sub (l, r) -> Sub (simplify1 l, simplify1 r)
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
print_newline ();;

let test = Neg (Sub (Int 0, Int 3));;
print_expr (simplify1 test);;
print_expr (simplify test);;
let test = Mul (Int 3, Add (Int 0, Int 0));;
print_expr (simplify1 test);;
print_expr (simplify test);;

let test = Add (Mul (Int 0, Int 5), (Neg (Int 4)));;
print_expr (simplify test);;
let test = Add (Mul (Int 1, Int 5), (Neg (Int 4)));;
print_expr (simplify test);;
let test = Add (Mul (Int 2, Int 5), (Neg (Int 4)));;
print_expr (simplify test);;


(* find_variables : expr -> CSet (* set of chars *) *)
let rec find_variables = function
    | Int _ -> CSet.empty
    | Var v -> CSet.singleton v
    | Add (l, r) -> CSet.union (find_variables l) (find_variables r)
    | Sub (l, r) -> CSet.union (find_variables l) (find_variables r)
    | Mul (l, r) -> CSet.union (find_variables l) (find_variables r)
    | Div (l, r) -> CSet.union (find_variables l) (find_variables r)
    | Neg e -> find_variables e
;;

print_newline ();;

(* generate_environments : CSet -> int Environment.t list *)
let generate_environments vars =
    (* generate_environments_ : char list -> int Environment.t list *)
    let rec generate_environments_ =
        (* addv : char -> int Environment.t -> int Environment.t list *)
        let addv v env = [Environment.add v 0 env; Environment.add v 1 env] in
        function
            | [] -> [Environment.empty]
            | v :: vs ->
                List.concat (List.map (addv v) (generate_environments_ vs))
    in
    generate_environments_ (CSet.elements vars)
;;
List.iter println_environment (generate_environments (find_variables fig1));;

(* evaluate_environments : int Environment.t list -> expr -> (int Environment.t, int) list*)
let evaluate_environments envs expr =
    let f env rest = ((env, eval env expr) :: rest) in
    List.fold_right f envs []
;;

let maximize expr =
    let rec max2 (env, res) (env', res') =
        if res > res' then (env, res) else (env', res')
    in
    let rec maximize' envs = match envs with
        | [] -> maximize' [Environment.empty]
        | [e] -> (e, eval e expr)
        | e::es -> max2 (e, eval e expr) (maximize' es)
    in
    maximize' (generate_environments (find_variables expr))
;;

let print_maximize expr =
    let (env, res) = maximize expr in
    print_string "maximization of ";
    print_expr expr;
    print_environment env;
    printf "= %d\n" res
;;

print_newline ();;
print_maximize fig1;;
print_maximize fig2;;
print_maximize fig3;;
print_maximize num_fingers;;
