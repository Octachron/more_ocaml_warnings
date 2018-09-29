let debug fmt = Format.fprintf Format.err_formatter
    ("@[debug:@ " ^^ fmt ^^ "@]@.")

module Print = struct

  let print_main ppf =
    Misc.Color.setup !Clflags.color;
    Format.fprintf ppf
      "@[@{<warning>Warning [opaqueness]:@}@ \
       some abstract types cannot be constructed@]@,"

  let print_sub ppf (loc,id) =
    Format.fprintf ppf
      "%a@ @[Type @{<warning>%s@} cannot be constructed@]"
      Location.print_loc loc (Ident.name id)

  let print_subs =
    Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.fprintf ppf "@,")
      print_sub

  let warning l =
    Format.eprintf "@[<v>%t%a@]@." print_main print_subs l
end

module Hypergraph = struct
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


  let mark_abstract id tbl =
    Hashtbl.replace tbl id { (Hashtbl.find tbl id) with status = Marked }

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

  let unreachable tbl = Hashtbl.fold (fun key info l ->
      if info.status = Marked then
        l
      else
        (info.loc, key) :: l
    ) tbl []

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
end

let warn _loc = function
  | [] -> ()
  | l -> Print.warning l

let early_error loc {Hypergraph.graph; vertices} =
  let early acc (_,id as x) =
    if Hashtbl.mem graph id then begin
      Hypergraph.mark_abstract id graph;
      x :: acc
    end
    else
      acc in
  List.fold_left early [] vertices |> warn loc



module Extract = struct
  open Types

  let rec arrow x = match x.desc with
    | Tarrow (_,x,y,_) ->
      let res, args = arrow y in
      res, x :: args
    | _ -> x, []


  let bind f l = List.fold_right (fun x acc -> (f x) @ acc) l []
  let ( >>= ) l f = bind f l

  let rec typ x = match x.desc with
    | Tconstr (Path.Pident p,_,_cts) -> [p]

    | Tconstr (p,_,_cts) ->
      debug "Seen %s" (Path.name p);
      [] (* ? *)

    | Ttuple ct -> ct >>= typ

    | Tlink ct | Tsubst ct -> typ ct

    | Tpoly _
    | Tvar _ | Tunivar _
    | Tnil -> []

    (* not yet implemented *)
    | Tvariant _ -> []
    | Tarrow _ -> []
    | Tfield _ -> []
    | Tobject _ -> []
    | Tpackage _ -> []

  let arrow_typ ty =
    let res, args = arrow ty in
    let args = args >>= typ in
    List.map (fun x -> x, args) (typ res)
end

module Data = struct

  type info =
    { id: Ident.t;
      loc: Location.t;
      view: Hypergraph.view
    }
  type elt =
    | Signature of info
    | Module_type

  let state = ref []

  let init id loc = state :=
      [Signature {
          id;
          loc;
          view = { graph = Hypergraph.init (); vertices = []}
        }
      ]


  let _update f = match !state with
    | [] -> ()
    | a :: q -> state := f a :: q

  let mutate f = match !state with
    | [] -> ()
    | Module_type :: _ -> ()
    | Signature x :: _ -> f x.view

  let in_modtype () = match !state with
    | Module_type :: _ -> true
    | _ -> false

  let pop () =
    match !state with
    | [] -> assert false
    | x :: q ->
      state := q;
      match x with
      | Signature x ->
        debug "pop: %d" (List.length q );
        Some x
      | Module_type ->
        debug "pop: mt %d" (List.length q );
        None

  let push id loc () =
    debug "Entering analysis: %s |%d+1" (Ident.name id) (List.length !state);
    match !state with
    | x :: _ ->
      let graph = match x with
        | Module_type -> Hypergraph.init ()
        | Signature s -> s.view.graph in
      let view = { Hypergraph.graph; vertices = [] } in
      state := Signature { id; loc; view } :: !state
    | [] -> assert false

    let push_mt () =
    debug "Entering analysis: mt| %d + 1" (List.length !state);
    state := Module_type :: !state
end

module TypesIter = struct

  open Types
  open Data
  let value_description id ty =
    debug "val %a" Ident.print id;
    ty
    |> Extract.arrow_typ
    |> List.iter (fun x -> mutate (Hypergraph.add_arrow x) )

  let decl id loc kind manifest =
    if kind &&  manifest = None then
      debug "abstract";
      mutate (Hypergraph.add_abstract loc id)

  let item = function
    | Sig_value (id, vd) ->
      debug "Types.val";
      value_description id vd.val_type
    | Sig_type (id,td,_) ->
      debug "Types.type";
      decl id td.type_loc (td.type_kind=Type_abstract) td.type_manifest
    | Sig_typext _ ->  ()

    | Sig_module _ -> ()
    | Sig_modtype _ -> ()
    | Sig_class _ -> ()
    | Sig_class_type _ -> ()

  let signature s =  List.iter item s

end

module Arg = struct

  open Data
  include TypedtreeIter.DefaultIteratorArgument

  let scrape env ty =
    debug "scrape";
    let ty = Env.scrape_alias env  ty in
    begin match ty with
      | Mty_signature s ->
        debug "scrape successful";
        TypesIter.signature s
      | _ -> ()
    end

  let enter_signature_item s = match s.sig_desc with
    | Tsig_module ({md_type = { mty_desc = Tmty_signature _; _}; _ } as m)  ->
      push m.md_id m.md_loc ();
      enter_signature_item s
    | Tsig_module  m  ->
      push m.md_id m.md_loc ();
      scrape s.sig_env m.md_type.mty_type
    | _ -> enter_signature_item s


  let last () = match !state with
    | Module_type :: _ -> debug "Module type before"; true
    | [] -> debug "last"; true
    | _ -> false


  let warning h =
    if last () then
      warn h.loc (Hypergraph.unreachable h.view.Hypergraph.graph)
    else
      early_error h.loc h.view

  let leave_signature_item s =
    match s.sig_desc with
    | Tsig_module m ->
      begin match pop () with
        | None -> debug "Leaving signature: None";
        | Some h ->
          debug "Leaving signature: %s -> analysis" (Ident.name m.md_id);
          warning h
      end
    | _ -> ()

  let leave_signature _ = match !state with
    | [Signature last] ->
      warn last.loc (Hypergraph.unreachable last.view.graph)
    | _ -> ()

  (*
  let enter_module_expr modexp =
    let env = modexp.mod_env in
    match modexp.mod_desc with
    | Tmod_constraint (_, _, Tmodtype_explicit ty , _) ->
      begin match ty.mty_desc with
        | Tmty_signature _ -> push modexp.mod_loc ()
        | _ -> scrape modexp.mod_loc env ty.mty_type
      end
    | Tmod_constraint (_,_, Tmodtype_implicit , _) ->
      push modexp.mod_loc
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
*)


  let enter_type_declaration (tyd:type_declaration) =
    debug "type %a" Ident.print tyd.typ_id;
    TypesIter.decl tyd.typ_id tyd.typ_loc
      (tyd.typ_kind = Ttype_abstract) tyd.typ_manifest


  let enter_value_description s =
    TypesIter.value_description s.val_id s.val_desc.ctyp_type


  let enter_module_type_declaration _ = push_mt ()
  let leave_module_type_declaration _ = ignore @@ pop ()

end

module Iter: iter = TypedtreeIter.MakeIterator(Arg)

let str info ((s,_) as arg) =
  let src = info.Misc.sourcefile in
  let id = Ident.create src in
  Data.init id (Location.in_file src);
  Iter.iter_structure s; arg
let sign info x =
  let src = info.Misc.sourcefile in
  let id = Ident.create src in
  Data.init id (Location.in_file src);
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
