(* Marian Sigler
 * Projet de programmation
 * UPS Toulouse, L3 Informatique, 2013/14
 * License: WTFPL
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

let print_environment e =
    if Environment.is_empty e
        then printf "{} "
        else Environment.iter (printf "%c=%d ") e;;
let println_environment e = print_environment e; print_newline ();;

(* / helper functions *)


(* 2.1 | definition of types *)

type expr = Int of int
          | Var of char
          | Add of expr * expr
          | Sub of expr * expr
          | Mul of expr * expr
          | Div of expr * expr (* integer division *)
          | Neg of expr;;

(* 2.2 | represent an expression as a string *)

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

(* 2.3 | evaluation of an expression *)

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


(* 2.4 | simplification *)

(* _height : expr -> int *)
let rec height = function
    | Int _ -> 0
    | Var _ -> 0
    | Add (l, r) -> 1 + max (height l) (height r)
    | Sub (l, r) -> 1 + max (height l) (height r)
    | Mul (l, r) -> 1 + max (height l) (height r)
    | Div (l, r) -> 1 + max (height l) (height r)
    | Neg e -> 1 + (height e)
;;


(* we need to force simplification to be made from bottom to top, because some
 * simplification opportunities only appear after some simplification has been
 * done downwards the calculation tree (e.g. a - (0-3) -> a-(-3) -> a+3 )
 *)

(* simplify_level : int -> expr -> expr *)
let rec simplify_level n expr =
(* only simplify expressions at a certain depth *)
    let simpl = simplify_level (n-1) in
    match (n, expr) with
    (* neutral elements *)
    | (0, Add (Int 0, r)) -> simpl r
    | (0, Add (l, Int 0)) -> simpl l
    | (0, Mul (Int 1, r)) -> simpl r
    | (0, Mul (l, Int 1)) -> simpl l
    | (0, Sub (l, Int 0)) -> simpl l
    | (0, Sub (Int 0, r)) -> simpl (Neg r)
    (* absorbing elements *)
    | (0, Mul (Int 0, _)) -> Int 0
    | (0, Mul (_, Int 0)) -> Int 0
    | (0, Div (Int 0, _)) -> Int 0
    (* negation elimination *)
    | (0, Neg (Neg a)) -> simpl a
    | (0, Add (l, Neg r)) -> simpl (Sub (l, r))
    | (0, Sub (l, Neg r)) -> simpl (Add (l, r))
    (* defaults *)
    | (_, Int i) -> Int i
    | (_, Var v) -> Var v
    | (_, Add (l, r)) -> Add (simpl l, simpl r)
    | (_, Mul (l, r)) -> Mul (simpl l, simpl r)
    | (_, Sub (l, r)) -> Sub (simpl l, simpl r)
    | (_, Div (l, r)) -> Div (simpl l, simpl r)
    | (_, Neg e) -> Neg (simpl e)
;;
(* I don't detect division by zero, because I consider it more beautiful
 * when such runtime errors appear only in one place. This way simplify always
 * succeeds.
 *)

(* simplify : expr -> expr *)
let simplify e =
(* completely simplify an expression, level by level starting at the bottom *)
    let rec simplify' e = function
        | -1 -> e
        | n -> simplify' (simplify_level n e) (n-1)
    in
    simplify' e (height e)
;;


(* 2.5 | environments *)

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


(* evaluate_environments : int Environment.t list -> expr -> (int Environment.t, int) list*)
let evaluate_environments envs expr =
    let f env rest = ((env, eval env expr) :: rest) in
    List.fold_right f envs []
;;

(* maximize : expr -> int Environment.t * int *)
let maximize expr =
    let rec max2 (env, res) (env', res') =
        if res > res' then (env, res) else (env', res')
    in
    let rec maximize' envs = match envs with
          (* if expr has no variables, the empty environment is the maximum: *)
        | [] -> maximize' [Environment.empty]
        | [e] -> (e, eval e expr)
        | e::es -> max2 (e, eval e expr) (maximize' es)
    in
    maximize' (generate_environments (find_variables expr))
;;


(* nullify : expr -> int Environment.t option *)
let nullify expr =
    let rec nullify' envs = match envs with
          (* if expr has no variables, we see if is zero by itself: *)
        | [] -> nullify' [Environment.empty]
        | [e] -> if eval e expr = 0 then Some e else None
        | e::es -> if eval e expr = 0 then Some e else nullify' es
    in
    nullify' (generate_environments (find_variables expr))
;;


(* 2.6 | application in depth *)

let rec apply f expr = match expr with
    | Int _ -> f expr
    | Var _ -> f expr
    | Add (l, r) -> f (Add (apply f l, apply f r))
    | Sub (l, r) -> f (Sub (apply f l, apply f r))
    | Mul (l, r) -> f (Mul (apply f l, apply f r))
    | Div (l, r) -> f (Div (apply f l, apply f r))
    | Neg e -> f (Neg (apply f e))
;;

let var2code expr = match expr with
    | Var v -> Int (Char.code v)
    | _ -> expr
;;

let var2exp var exp expr = match expr with
    | Var v -> if v = var then exp else expr
    | _ -> expr
;;

let exch_addmul expr = match expr with
    | Add (l, r) -> Mul (l, r)
    | Mul (l, r) -> Add (l, r)
    | _ -> expr
;;

let mirror expr = match expr with
    | Add (l, r) -> Add (r, l)
    | Sub (l, r) -> Sub (r, l)
    | Mul (l, r) -> Mul (r, l)
    | Div (l, r) -> Div (r, l)
    | _ -> expr
;;








(* DEMONSTRATION OUTPUT *)

(* all expressions I will need *)

let fig1 = Add (Add (Mul (Var 'x', Int 1), Neg (Var 'y')),
                Sub (Int 5, Int 7))
let fig2 = Add (Add (Var 'x', Var 'y'), Int 5)
let fig3 = Add (Add (Mul (Var 'x', Int 1), Neg (Sub (Int 0, Var 'y'))),
                Sub(Int 5, Mul(Int 0, Var 'z')))
let fig3' = Add (Add (Mul (Var 'x', Int 1), Neg (Sub (Int 0, Var 'y'))),
                 Sub(Mul(Int 0, Var 'z'), Int 5))
let fig4a = Add (Var 'x', Int 3)
let fig4b = Mul (Add (Var 'x', Int 3), Var 'y')
let fig5 = Add (Add (Mul (Var 'a', Int 1), Neg (Sub (Int 0, Var 'a'))),
                Sub (Int 5, Mul (Int 0, Var 'b')))
let circumf_rectangle = Add (Mul (Int 2, Var 'x'), Mul (Int 2, Var 'y'))
let num_fingers = Mul (Int 2, Int 5)
let zero = Add (Int 1, Neg (Int 1))

(* 2.2 *)

let print_expr ?n e = match n with
    | None -> println_string (show e)
    | Some note -> println_string (note ^ ": " ^ show e);;

print_expr fig1 ~n:"Fig. 1";;
print_expr fig2 ~n:"Fig. 2";;
print_expr circumf_rectangle ~n:"Circumference of a rectangle";;

(* 2.3 *)

let env1 = Environment.add 'x' 2 (Environment.add 'y' 4 (Environment.empty));;

print_int (eval env1 fig1);;
print_string "\n\n";;

(* 2.4 *)

print_expr fig3 ~n:"Fig. 3 (original)";;
print_expr (simplify fig3) ~n:"Fig. 3 (simplified)";;
print_expr fig3' ~n:"Fig. 3' (original)";;
print_expr (simplify fig3') ~n:"Fig. 3' (simplified)";;
print_newline ();;

let test = Neg (Sub (Int 0, Int 3));;
print_expr (simplify test);;
let test = Mul (Int 3, Add (Int 0, Int 0));;
print_expr (simplify test);;

let test = Add (Mul (Int 0, Int 5), (Neg (Int 4)));;
print_expr (simplify test);;
let test = Add (Mul (Int 1, Int 5), (Neg (Int 4)));;
print_expr (simplify test);;
let test = Add (Mul (Int 2, Int 5), (Neg (Int 4)));;
print_expr (simplify test);;
print_newline ();;

(* 2.5 *)

List.iter println_environment (generate_environments (find_variables fig1));;
print_newline ();;

let print_maximize expr =
    let (env, res) = maximize expr in
    printf "null environment of %s:  " (show expr);
    print_environment env;
    printf "= %d\n" res
;;

print_maximize fig1;;
print_maximize fig2;;
print_maximize fig3;;
print_maximize fig4a;;
print_maximize fig4b;;
print_maximize num_fingers;;

(* nullify : expr -> int Environment.t option *)
let nullify expr =
    let rec nullify' envs = match envs with
          (* if expr has no variables, we see if is zero by itself *)
        | [] -> nullify' [Environment.empty]
        | [e] -> if eval e expr = 0 then Some e else None
        | e::es -> if eval e expr = 0 then Some e else nullify' es
    in
    nullify' (generate_environments (find_variables expr))
;;

let print_nullify expr =
    printf "null environment of %s:  " (show expr);
    match nullify expr with
        | Some env -> print_environment env; print_newline ();
        | None -> printf "none\n"
;;

print_newline ();;
print_nullify fig1;;
print_nullify fig2;;
print_nullify fig3;;
print_nullify fig4a;;
print_nullify fig4b;;
print_nullify zero;;
print_nullify num_fingers;;

(* 2.6 *)

print_newline ();;
print_expr ~n:"Fig. 5" fig5;;
print_expr ~n:"Fig. 5, var2code" (apply var2code fig5);;
let exp = Add (Var 'c', Int 3) in
print_expr ~n:"Fig. 5, a->c+3" (apply (var2exp 'a' exp) fig5);;
print_expr ~n:"Fig. 5, +->* *->+" (apply exch_addmul fig5);;
print_expr ~n:"Fig. 5, mirror" (apply mirror fig5);;
