let debug fmt = Format.fprintf Format.err_formatter
    ("@[debug:@ " ^^ fmt ^^ "@]@.")

type info =
  { id: Ident.t;
    loc: Location.t;
    view: Hypergraph.view
  }
type elt =
  | Signature of info
  | Module_type

module Data = struct
  let state = ref []
end
let get () = !Data.state
let set x = Data.state := x
let cons x = Data.state := x :: get ()

let init id loc =
  let view = Hypergraph.{ graph = init (); vertices = []} in
  set [Signature {id;loc;view} ]


let _update f = match get () with
  | [] -> ()
  | a :: q -> set @@ f a :: q

let mutate f = match get () with
  | [] -> ()
  | Module_type :: _ -> ()
  | Signature x :: _ -> f x.view

let in_modtype () = match get() with
  | Module_type :: _ -> true
  | _ -> false

let pop () =
  match get () with
  | [] -> assert false
  | x :: q ->
    set q;
    match x with
    | Signature x ->
      debug "pop: %d" (List.length q );
      Some x
    | Module_type ->
      debug "pop: mt %d" (List.length q );
      None

let push id loc () =
  debug "Entering analysis: %s |%d+1" (Ident.name id) (List.length @@ get ());
  match get () with
  | x :: _ ->
    let graph = match x with
      | Module_type -> Hypergraph.init ()
      | Signature s -> s.view.graph in
    let view = { Hypergraph.graph; vertices = [] } in
    cons @@ Signature { id; loc; view }
  | [] -> assert false

let push_mt () =
  debug "Entering analysis: mt| %d + 1" (List.length @@ get ());
  cons Module_type
