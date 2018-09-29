type vertex = Ident.t
module Edge = Set.Make(struct type t = vertex let compare = compare end)
type edge = Edge.t
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
        let edges = List.map (Edge.remove v) info.edges in
        if info.status = Connected
        && List.exists (fun e -> e = Edge.empty) edges then
          (stack := v :: !stack; None)
        else Some { info with edges }
      ) tbl;
    remove_vertices !stack tbl

let add_edge tbl vertex edge =
  if edge = Edge.empty then remove_vertices [vertex] tbl
  else add_edge_simple vertex edge tbl

let add_arrow (res,ls) graph =
  let rec filter edge = function
    | [] ->  add_edge graph res edge
    | arg :: q ->
      let edge = if Hashtbl.mem graph arg then Edge.add arg edge else edge in
      filter edge q in
  if Hashtbl.mem graph res then
    filter Edge.empty ls
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
