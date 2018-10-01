open Utils

type 'a t =
  | And of 'a t list
  | Var of 'a
  | Or of 'a t list
  | True
  | False
  | Implies of 'a t * 'a t

let rec (&&&) x y = match x, y with
  | False, _ | _, False -> False
  | True, y | y, True -> y
  | And a, And b -> List.fold_left (&&&) (all a) b
  | And a, y | y, And a -> And (y :: a)
  | x, y when x = y -> x
  | x, y -> And [x;y]

and all =
  function
  | [] -> True
  | [x] -> x
  | x :: q -> x &&& all q

let rec (|||) x y = match x, y with
  | False, x | x, False -> x
  | True, _ | _, True -> True
  | Or a, Or b -> List.fold_left (|||) (any a) b
  | Or a, b | b, Or a -> Or (b :: a)
  | x, y when x = y -> x
  | x, y -> Or [x;y]

and any  = function
  | [] -> True
  | [x] -> x
  | x :: q -> x ||| any q

let rec (|-) x y = match x, y with
  | False, _ -> True
  | True, x -> x
  | _x, True -> True
  | x, Implies(y,z) -> (x &&& y) |- z
  | Implies(x,y), z -> (x==>y) |- z
  | x, y -> Implies(x,y)

and (==>) x y = match x, y with
  | Var x, Var y when x = y -> True
  | Implies(x,y), z -> (x==>y) ==> z
  | x, y -> x |- y



type precedence = I | P | M

let rec pp precedence var ppf = function
  | And l ->
    Format.fprintf ppf "@[%a@]"
      (pp_list M var @@ format_of_string "∧") l
  | Or l ->
    Format.fprintf ppf
      (if precedence > P then "@[(%a)@]" else "@[%a@]")
      (pp_list P var "∨") l
  | True -> const "⊤" ppf
  | False -> const "⊥" ppf
  | Var x -> var ppf x
  | Implies (x,y) ->
    Format.fprintf ppf
      (if precedence = I then "%a ⊢ %a" else "(%a ⇒ %a)")
      (pp I var) x (pp I var) y
and pp_list precedence var s =
  Format.pp_print_list ~pp_sep:(sep @@ "@ "^^ s ^^"@ ") (pp precedence var)

let pp x = pp I x

let rec simplify assign = function
  | True | False as x -> x
  | Implies(x,y) -> simplify assign x |- simplify assign y
  | And x -> all (List.map (simplify assign) x)
  | Or x -> any (List.map (simplify assign) x)
  | Var x as v ->
    match assign x with
    | None -> v
    | Some x -> x
and simplify_list current (%) f  = function
  | [] -> current
  | x :: q ->
    simplify_list (current % simplify f x) (%) f q
and simplify_and f = simplify_list True (&&&) f
and simplify_or f = simplify_list False (|||) f

let simplif x = simplify (fun _ -> None) x
let ( %=% ) value lit = simplify (fun x -> if x = value then Some lit else None)

let rec free = function
  | Var x -> [x]
  | True | False -> []
  | And l | Or l -> Utils.bind free l
  | Implies(x,y) -> free x @ free y

type 'a set = (module Set.S with type elt = 'a)
let make_iff (type elt) ((module S): elt set): elt t -> elt list  =
  let rec iff = function
  | False | True | Or [] -> S.empty
  | Var x -> S.singleton x
  | And x -> List.fold_left (fun s x -> S.union (iff x) s) S.empty x
  | Or (x::q) ->
    List.fold_left (fun s x -> S.inter s (iff x)) (iff x) q
  | Implies(_,y) -> iff y in
  fun f -> S.elements (iff f)

let iff = make_iff (module Ident.Set)

let rec required positive = function
  | Var x -> [x]
  | True | False -> []
  | And l | Or l -> Utils.bind (required positive) l
  | Implies(x,y) ->
    if positive then required false x else required true y

let required x = required true x
