let debug fmt = Format.fprintf Format.err_formatter
    ("@[debug:@ " ^^ fmt ^^ "@]@.")

type vertex = Ident.t

type 'a formula =
  | And of 'a formula list
  | Var of 'a
  | Or of 'a formula list
  | True
  | False

let const s ppf = Format.fprintf ppf "%(%)" s
let sep s ppf () = const s ppf

let rec pp_formula var ppf = function
  | And l -> Format.fprintf ppf "@[[%a]@]"
               (pp_list var @@ format_of_string "∧") l
  | Or l -> Format.fprintf ppf "@[[%a]@]" (pp_list var "∨") l
  | True -> const "true" ppf
  | False -> const "false" ppf
  | Var x -> var ppf x
and pp_list var s =
  Format.pp_print_list ~pp_sep:(sep @@ "@ "^^ s ^^"@ ") (pp_formula var)
let pp_ident ppf id = Format.fprintf ppf "%s" (Ident.name id)
let pp_edge = pp_formula pp_ident


let rec simplify assign = function
  | True | False as x -> x
  | And [] | Or [] -> True
  | And [x] -> x
  | Or [x] -> x
  | And l -> simplify_and assign [] l
  | Or l -> simplify_or assign [] l
  | Var x as v ->
    match assign x with
    | None -> v
    | Some x -> x
and simplify_list max absorbing best f rest  = function
  | [] -> if best then max else And rest
  | x :: q ->
    let x = simplify f x in
    if x = absorbing then absorbing
    else if x = max then simplify_list max absorbing true f (x::rest) q
    else simplify_list max absorbing false f (x::rest) q
and simplify_and f = simplify_list True False true f
and simplify_or f = simplify_list False True true f

let simplify f x =
  let y = simplify f x in
  debug "[%a] => [%a]" pp_edge x pp_edge y;
  y

let simplif = simplify (fun _ -> None)
let ( %=% ) value lit = simplify (fun x -> if x = value then Some lit else None)


type edge = Ident.t formula
type status =
  | Unknown
  | Connected
  | Marked
type info =
  { loc: Location.t; edges: edge list; status: status }
type t = (vertex, info) Hashtbl.t

let init () = Hashtbl.create 20

let add_vertex loc v tbl =
  Hashtbl.replace tbl v {loc; edges = []; status = Unknown}
let add_edge_simple v edge tbl =
  match Hashtbl.find_opt tbl v with
  | None -> ()
  | Some info ->
    Hashtbl.replace tbl v
      { info with status = max Connected info.status;
                  edges =  edge :: info.edges }

let rec remove_vertices vs tbl =
  match vs with
  | [] -> ()
  | v :: q ->
    Hashtbl.remove tbl v;
    let stack = ref q in
    Hashtbl.filter_map_inplace (fun _w info ->
        let edges = List.map (v %=% True) info.edges in
        if info.status = Connected
        && List.exists ( (=) True ) edges then
          (stack := v :: !stack; None)
        else Some { info with edges }
      ) tbl;
    remove_vertices !stack tbl

let add_edge tbl vertex edge =
  debug "Add edge:[%a]" pp_edge edge;
  if edge = True then remove_vertices [vertex] tbl
  else add_edge_simple vertex edge tbl

let add_arrow (res,ls) graph =
  let rec filter edge = function
    | [] ->  add_edge graph res (simplif @@ And edge)
    | arg :: q ->
      let edge = if Hashtbl.mem graph arg then Var arg::edge else edge in
      filter edge q in
  if Hashtbl.mem graph res then
    filter [] ls
  else ()

type view = { graph:t; mutable vertices: (Location.t * vertex) list }

let add_arrow (res,ls) view =
  add_arrow (res,ls) view.graph

let add_abstract loc id view =
  add_vertex loc id view.graph;
  view.vertices <- (loc,id) :: view.vertices

let mark id tbl =
  Hashtbl.replace tbl id { (Hashtbl.find tbl id) with status = Marked }

let unreachable tbl = Hashtbl.fold (fun key info l ->
    if info.status = Marked then
      l
    else
      (info.loc, key) :: l
  ) tbl []
