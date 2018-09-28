let debug fmt = Format.ifprintf Format.err_formatter
    ("@[debug:@ " ^^ fmt ^^ "@]@.")

module Hypergraph = struct
  type vertex = Ident.t
  module Edge = Set.Make(struct type t = vertex let compare = compare end)
  type edge = Edge.t
  type info =
    { loc: Location.t; edges: edge list; connected: bool }
  type t = (vertex, info) Hashtbl.t

  let init () = Hashtbl.create 20

  let add_vertex loc v tbl =
    Hashtbl.replace tbl v {loc; edges = []; connected = false}
  let add_edge_simple v edge tbl =
    match Hashtbl.find_opt tbl v with
    | None -> ()
    | Some info ->
      Hashtbl.replace tbl v
        { info with connected = true; edges =  edge :: info.edges }


  let rec remove_vertices vs tbl =
    match vs with
    | [] -> ()
    | v :: q ->
      Hashtbl.remove tbl v;
      let stack = ref q in
        Hashtbl.filter_map_inplace (fun _w info ->
              let edges = List.map (Edge.remove v) info.edges in
              if info.connected
              && List.exists (fun e -> e = Edge.empty) edges then
                (stack := v :: !stack; None)
              else Some { info with edges }
          ) tbl;
        remove_vertices !stack tbl


  let add_edge tbl vertex edge =
    if edge = Edge.empty then remove_vertices [vertex] tbl
    else add_edge_simple vertex edge tbl

  let add_arrow ls graph =
    let rec filter edge = function
      | [] -> ()
      | [t] -> if Hashtbl.mem graph t then add_edge graph t edge else ()
      | arg :: q ->
        let edge = if Hashtbl.mem graph arg then Edge.add arg edge else edge in
        filter edge q in
    filter Edge.empty ls

  let unreachable tbl = Hashtbl.fold (fun key info x ->
      (info.loc, key) :: x) tbl []

end

open Typedtree
module type iter = sig
      val iter_structure : structure -> unit
      val iter_signature : signature -> unit
      val iter_structure_item : structure_item -> unit
      val iter_signature_item : signature_item -> unit
      val iter_expression : expression -> unit
      val iter_module_type : module_type -> unit
      val iter_pattern : pattern -> unit
      val iter_class_expr : class_expr -> unit
    end

module type arg = sig
  include TypedtreeIter.IteratorArgument
  val init: Location.t -> unit
end

let pp_ident ppf s = Format.fprintf ppf "%s" (Ident.name s)

let subwarn (loc,id) =
  Location.errorf ~loc "type %a cannot be constructed" pp_ident id

let warn loc = function
  | [] -> ()
  | l ->
    Location.report_error Format.err_formatter @@
    Location.errorf ~loc ~sub:(List.map subwarn l)
      "some abstract types cannot be constructed"

module Arg: arg = struct

  type data = { mutable count: int; loc: Location.t; graph: Hypergraph.t }
  type elt =
    | On of data
    | Neg
    | Off

  let state = ref []

  let init loc = state := [On { count = 0; loc; graph = Hypergraph.init () }]

  include TypedtreeIter.DefaultIteratorArgument

  let _update f = match !state with
    | [] -> ()
    | a :: q -> state := f a :: q

  let mutate f = match !state with
    | [] -> ()
    | (Off|Neg) :: _ -> ()
    | On x :: _ -> f x

  let mutate_graph f = mutate (fun x -> f x.graph)

  let _in_modtype () = match !state with
    | Off :: _ -> true
    | _ -> false

  let pop () = match !state with
    | [] -> assert false
    | On a :: q ->
      debug "pop %d" a.count;
      if a.count = 1 then
        (state := q; Some a) else
        begin
          a.count <- a.count - 1;
          None
        end
    | (Off|Neg) :: _ -> None

  let pop_mt () = match !state with
    | [] -> assert false
    | On _ :: _ -> assert false
    | (Off|Neg) :: q ->
      debug "Leaving module type declaration";
      state := q

  let push loc =
    debug "Entering analysis: me";
    match !state with
    | Off :: _ | [] ->
      state := On { loc; count=1; graph = Hypergraph.init () } :: !state
    | Neg :: q -> state := Off :: q
    | On x :: _ ->
      debug "Count %d" x.count;
      x.count <- x.count + 1

    let push_mt () =
    debug "Entering analysis: mt";
    state := Neg :: !state

  let enter_signature _ = push Location.none
  let enter_module_expr modexp =
    match modexp.mod_desc with
    | Tmod_constraint (_, _, Tmodtype_explicit _ , _)
    | Tmod_constraint (_,_, Tmodtype_implicit , _) -> push modexp.mod_loc
    | _ -> ()

  let leave_module_expr modexp =
    match modexp.mod_desc with
    |  Tmod_constraint _ ->
      debug "Leaving";
      begin match pop () with
        | None -> debug "Nested?"
        | Some x ->
          let unreachable = Hypergraph.unreachable x.graph in
          warn modexp.mod_loc unreachable
      end
    | _ -> ()

  let leave_signature _s =
    match pop () with
    | None -> debug "Leaving signature: None";
    | Some h ->
      debug "Leaving signature: Analysis";
      let unreachable = Hypergraph.unreachable h.graph in
      warn h.loc unreachable

  let enter_type_declaration (tyd:type_declaration) =
    debug "type %a" Ident.print tyd.typ_id;
    match tyd.typ_kind, tyd.typ_manifest with
    | Ttype_abstract, None ->
      debug "abstract";
      mutate_graph (Hypergraph.add_vertex tyd.typ_loc tyd.typ_id)
    | _ -> ()

  let rec extract_arrow x = match x.ctyp_desc with
    | Ttyp_arrow (_,x,y) -> x :: extract_arrow y
    | _ -> [x]


  let bind f l = List.fold_right (fun x acc -> (f x) @ acc) l []
  let ( >>= ) l f = bind f l

  let rec extract_typ x = match x.ctyp_desc with
    | Ttyp_constr (Path.Pident p,_,_cts) -> [p]

    | Ttyp_constr (p,_,_cts) ->
      debug "Seen %s" (Path.name p);
      [] (* ? *)

    | Ttyp_tuple ct -> ct >>= extract_typ
    | Ttyp_alias (ct,_) -> extract_typ ct
    | Ttyp_poly (_,ct) -> extract_typ ct

    | Ttyp_any -> []
    | Ttyp_var _ -> []

    (* not yet implemented *)
    | Ttyp_variant _ -> []
    | Ttyp_arrow _ -> []
    | Ttyp_class _ -> []
    | Ttyp_object _ -> []
    | Ttyp_package _ -> []

  let enter_value_description (x:value_description) =
    debug "val %a" Ident.print x.val_id;
    x.val_desc
    |> extract_arrow
    >>= extract_typ
    |> (fun x -> mutate_graph (Hypergraph.add_arrow x) )


  let enter_module_type_declaration _ = push_mt ()
  let leave_module_type_declaration _ = pop_mt ()

end

module Iter = TypedtreeIter.MakeIterator(Arg)

let str info ((s,_) as arg) =
  Arg.init (Location.in_file info.Misc.sourcefile);
  Iter.iter_structure s; arg
let sign info x =
  Arg.init (Location.in_file info.Misc.sourcefile);
  Iter.iter_signature x;
  x


let () =
  Typemod.ImplementationHooks.add_hook
    "opaqueness warning"
    str

let () =
  Typemod.InterfaceHooks.add_hook
    "opaqueness warning"
    sign
