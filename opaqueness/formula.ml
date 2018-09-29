let debug fmt = Format.fprintf Format.err_formatter
    ("@[debug:@ " ^^ fmt ^^ "@]@.")

type 'a t =
  | And of 'a t list
  | Var of 'a
  | Or of 'a t list
  | True
  | False

let (&&&) x y = match x, y with
  | False, _ -> False
  | True, y -> y
  | And a, And b -> And (a @ b)
  | And a, y | y, And a -> And (y :: a)
  | x, y when x = y -> x
  | x, y -> And [x;y]

let (|||) x y = match x, y with
  | False, x -> x
  | True, _ -> True
  | Or a, Or b -> Or (a @ b)
  | Or a, b | b, Or a -> Or (b :: a)
  | x, y when x = y -> x
  | x, y -> Or [x;y]


let rec all  = function
  | [] -> True
  | [x] -> x
  | x :: q -> x &&& all q

let rec any  = function
  | [] -> True
  | [x] -> x
  | x :: q -> x ||| any q

let const s ppf = Format.fprintf ppf "%(%)" s
let sep s ppf () = const s ppf

let rec pp var ppf = function
  | And l -> Format.fprintf ppf "@[[%a]@]"
               (pp_list var @@ format_of_string "∧") l
  | Or l -> Format.fprintf ppf "@[[%a]@]" (pp_list var "∨") l
  | True -> const "true" ppf
  | False -> const "false" ppf
  | Var x -> var ppf x
and pp_list var s =
  Format.pp_print_list ~pp_sep:(sep @@ "@ "^^ s ^^"@ ") (pp var)

let rec simplify assign = function
  | True | False as x -> x
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
