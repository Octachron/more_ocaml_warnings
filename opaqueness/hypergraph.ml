open Utils
type vertex = Ident.t

type edges = Ident.t Formula.t
type status =
  | Unknown
  | Connected
  | Marked
type info =
  { loc: Location.t; edges: edges; status: status }
type t = (vertex, info) Hashtbl.t

let init () = Hashtbl.create 20

let add_vertex loc v tbl =
  Hashtbl.replace tbl v {loc; edges = False ; status = Unknown}
let add_edge_simple v edge tbl =
  match Hashtbl.find_opt tbl v with
  | None -> ()
  | Some info ->
    Hashtbl.replace tbl v
      { info with status = max Connected info.status;
                  edges =  Formula.( edge ||| info.edges ) }

let pp_edge = Formula.pp Utils.pp_ident

let rec remove_vertices vs tbl =
  match vs with
  | [] -> ()
  | v :: q ->
    Hashtbl.remove tbl v;
    let stack = ref q in
    Hashtbl.filter_map_inplace (fun _w info ->
        let edges = Utils.capture pp_edge Formula.(v %=% True) info.edges in
        if info.status = Connected
        && edges = Formula.True then
          (stack := v :: !stack; None)
        else Some { info with edges }
      ) tbl;
    remove_vertices !stack tbl

let add_edge tbl vertex edge =
  Utils.debug "Add edge: %a ⇒ %a" pp_edge edge pp_ident vertex;
  if edge = Formula.True then remove_vertices [vertex] tbl
  else add_edge_simple vertex edge tbl

let add_arrow (res,ls) graph =
  let ls = Utils.capture pp_edge (Formula.simplify
      (fun arg ->
         if Hashtbl.mem graph arg then None
         else Some True
      )) (Formula.all ls) in
  if Hashtbl.mem graph res then
    add_edge graph res (Utils.capture pp_edge Formula.simplif ls);

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
      (info.loc, key, Formula.free info.edges) :: l
  ) tbl []
