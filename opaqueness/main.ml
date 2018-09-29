let debug fmt = Format.fprintf Format.err_formatter
    ("@[debug:@ " ^^ fmt ^^ "@]@.")

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
  | l -> Printer.warning l

let early_warning loc {Hypergraph.graph; vertices} =
  let early acc (_,id as x) =
    if Hashtbl.mem graph id then begin
      Hypergraph.mark id graph;
      x :: acc
    end
    else
      acc in
  List.fold_left early [] vertices |> warn loc



module Extract = struct
  open Types

  let rec arrow expand env x = match x.desc with
    | Tarrow (_,x,y,_) ->
      let res, args = arrow true env y in
      res, x :: args
    | Tconstr _ when not expand -> x, []
    | Tconstr _  -> arrow false env (Ctype.expand_head env x)
    | _ -> x, []

  let arrow = arrow true

  let bind f l = List.fold_right (fun x acc -> (f x) @ acc) l []
  let ( >>= ) l f = bind f l

  let rec typ x = match x.desc with
    | Tconstr (Path.Pident p,_,_cts) -> [Hypergraph.Var p]

    | Tconstr (p,_,_cts) ->
      debug "Seen %s" (Path.name p);
      [] (* ? *)

    | Ttuple ct -> ct >>= typ

    | Tlink ct | Tsubst ct -> typ ct

    | Tpoly _
    | Tvar _ | Tunivar _
    | Tnil -> []

    (* not yet implemented *)
    | Tvariant r -> [Or (r.row_fields>>= row_field)]
    | Tarrow _ -> []
    | Tfield _ -> []
    | Tobject _ -> []
    | Tpackage _ -> []

  and row_field (_, r) = match r with
    | Rpresent (Some t) -> typ t
    | Rpresent None | Rabsent -> []
    | Reither _ -> assert false
  
  let arrow_typ env ty =
    let res, args = arrow env ty in
    let args = args >>= typ in
    List.fold_left (fun l -> function
        | Hypergraph.Var x -> (x, args) :: l
        | _ -> l
      ) [] (typ res)
end

module TypesIter = struct

  open Types
  let value_description env id ty =
    debug "val %a" Ident.print id;
    ty
    |> Extract.arrow_typ env
    |> List.iter (fun x -> State.mutate (Hypergraph.add_arrow x) )

  let decl id loc kind manifest =
    if kind &&  manifest = None then
      (
        debug "abstract: %s" (Ident.name id);
        State.mutate (Hypergraph.add_abstract loc id)
      )

  let item env = function
    | Sig_value (id, vd) ->
      debug "Types.val";
      value_description env  id vd.val_type
    | Sig_type (id,td,_) ->
      debug "Types.type";
      decl id td.type_loc (td.type_kind=Type_abstract) td.type_manifest
    | Sig_typext _ ->  ()

    | Sig_module _ -> ()
    | Sig_modtype _ -> ()
    | Sig_class _ -> ()
    | Sig_class_type _ -> ()

  let signature env s =  List.iter (item env) s

end

module Arg = struct

  include TypedtreeIter.DefaultIteratorArgument

  let scrape env ty =
    debug "scrape";
    let ty = Env.scrape_alias env  ty in
    begin match ty with
      | Mty_signature s ->
        debug "scrape successful";
        TypesIter.signature env s
      | _ -> ()
    end

  let enter_signature_item s = match s.sig_desc with
    | Tsig_module ({md_type = { mty_desc = Tmty_signature _; _}; _ } as m)  ->
      State.push m.md_id m.md_loc ();
      enter_signature_item s
    | Tsig_module  m  ->
      State.push m.md_id m.md_loc ();
      scrape s.sig_env m.md_type.mty_type
    | _ -> enter_signature_item s


  let last () = match State.get () with
    | Module_type :: _ -> debug "Module type before"; true
    | [] -> debug "last"; true
    | _ -> false


  let warning h =
    if last () then
      warn h.State.loc (Hypergraph.unreachable h.view.Hypergraph.graph)
    else
      early_warning h.loc h.view

  let leave_signature_item s =
    match s.sig_desc with
    | Tsig_module m ->
      begin match State.pop () with
        | None -> debug "Leaving signature: None";
        | Some h ->
          debug "Leaving signature: %s -> analysis" (Ident.name m.md_id);
          warning h
      end
    | _ -> ()

  let leave_signature _ = match State.get () with
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
    TypesIter.value_description
      s.val_desc.ctyp_env s.val_id s.val_desc.ctyp_type


  let enter_module_type_declaration _ = State.push_mt ()
  let leave_module_type_declaration _ = ignore @@ State.pop ()

end

module Iter: iter = TypedtreeIter.MakeIterator(Arg)

let str info ((s,_) as arg) =
  let src = info.Misc.sourcefile in
  let id = Ident.create src in
  State.init id (Location.in_file src);
  Iter.iter_structure s; arg
let sign info x =
  let src = info.Misc.sourcefile in
  let id = Ident.create src in
  State.init id (Location.in_file src);
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
