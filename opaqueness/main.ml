open Utils

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

let warn loc ctx = function
  | [] -> ()
  | l -> Printer.warning loc ctx l

let early_warning loc ctx {Hypergraph.graph; vertices} =
  let early acc (loc,id) =
    if Hashtbl.mem graph id then begin
      Hypergraph.mark id graph;
      (loc, id, Formula.free (Hashtbl.find graph id).edges)  :: acc
    end
    else
      acc in
  List.fold_left early [] vertices |> warn loc ctx




module Extract = struct
  open Types

  type 'a arrow = { res: 'a; args: 'a list }
  let is_abstract ty =
    ty.type_kind = Type_abstract
    && ty.type_manifest = None

  let rec arrow expand env res = match res.desc with
    | Tarrow (_,x,y,_) ->
      let r = arrow true env y in
      { r with args = x :: r.args }
    | Tconstr _ when not expand -> { res; args = [] }
    | Tconstr _  -> arrow false env (Ctype.full_expand env res)
    | _ -> { res; args = [] }

  and typ visited env x = match x.desc with
    | Tconstr (Path.Pident p,params,_cts) ->
      if List.mem x visited then [Formula.False] else
      begin try
          let t = Env.find_type (Path.Pident p) env in
          if is_abstract t then
            (debug "constr: %s" (Ident.name p);
             [Formula.Var p])
          else
            [deconstruct (x :: visited) env params t]
        with Not_found -> []
      end
    | Tconstr (p,params,_cts) ->
      debug "Seen %s" (Path.name p);
      let t = Env.find_type p env in
      debug "deconstructing %s" (Path.name p);
      [deconstruct visited env params t]

    | Ttuple ct -> debug "tuple"; ct >>= typ visited env
    | Tpoly (ct, _) | Tlink ct | Tsubst ct -> typ visited env ct

    | Tvar _ | Tunivar _
    | Tnil -> debug "variables"; []

    | Tvariant r -> [Formula.any (r.row_fields>>= row_field visited env)]

    | Tarrow _ ->
      debug "inner arrow";
      let r = arrow true env x in typ visited env r.res
    | Tfield (s,_,ty,rest) ->
      debug "field %s" s;
      typ visited env ty @ typ visited env rest
    | Tobject (ty, _c) (*when !c = None*) ->
      debug "object";
      typ visited env ty

    (* not yet implemented *)
    (*| Tobject _ -> []  ? *)
    | Tpackage (p,_nl,_) ->
      let modtypedecl = Env.find_modtype p env in
      modtype visited env modtypedecl.mtd_type

  and row_field visited env (_, r) = match r with
    | Rpresent (Some t) -> [Formula.all (typ visited env t)]
    | Rpresent None | Rabsent -> []
    | Reither _ -> assert false

  and deconstruct (visited: _ list) (env:Env.t) params tyd =
    let back = Btype.snapshot () in
    let f =
      try begin
        List.iter2 (fun x y -> Ctype.unify env x y) params tyd.type_params;
          match tyd.type_kind with
          | Type_record (l,_) -> labels visited env l
          | Type_variant l ->
            let constr (x:constructor_declaration) =
              debug "constructor: %a" pp_ident x.cd_id;
              echo "arg, " Hypergraph.pp_edge @@
              match x.cd_args with
              | Cstr_tuple t -> Formula.all (t >>= typ visited env)
              | Cstr_record ld-> labels visited env ld in
            Formula.any (List.map constr l)
          | Type_abstract | Type_open -> True
        end with Ctype.Unify _ -> False in
    Btype.backtrack back;
    debug "Deconstructing to %a" Hypergraph.pp_edge f;
    f

  and modtype  visited env = function
      | None -> []
      | Some mtd ->
        begin match Env.scrape_alias env mtd with
          | Mty_signature s -> bind (signature_item visited env) s
          | _ -> []
        end
  and signature_item visited env = function
    | Sig_value (_,v) -> typ visited env v.val_type
    | Sig_module (_,md,_) -> modtype visited env (Some md.md_type)

    (* not implemented *)
    | Sig_class _ -> []

    (* *)
    | Sig_class_type _ -> []
    | Sig_modtype _ -> []
    | Sig_typext _ -> []
    | Sig_type _ -> []

  and labels visited env l =
    Formula.all (bind (fun x -> typ visited env x.ld_type) l)

  let arrow_typ env ty =
    let r = arrow true env ty in
    let args = r.args >>= typ [] env in
    List.map (fun implied -> (implied, args) )
    @@ Formula.(iff @@ all @@ typ [] env r.res)
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

  let rec item loc env = function
    | Sig_value (id, vd) ->
      debug "Types.val";
      value_description env  id vd.val_type
    | Sig_type (id,td,_) ->
      debug "Types.type";
      decl id loc (td.type_kind=Type_abstract) td.type_manifest
    | Sig_typext _ ->  ()

    | Sig_module (_,md,_) -> modtype env loc md.md_type

    (* not implemented *)
    | Sig_class _ -> ()

    (* Type level only *)
    | Sig_modtype _ -> ()
    | Sig_class_type _ -> ()

  and modtype env loc s =
    match Env.scrape_alias env s with
    | Mty_signature s -> List.iter (item loc env) s
    | _ -> ()

end

module Arg = struct

  include TypedtreeIter.DefaultIteratorArgument

  let enter_signature_item s = match s.sig_desc with
    | Tsig_module ({md_type = { mty_desc = Tmty_signature _; _}; _ } as m)  ->
      State.push ~id:m.md_id m.md_loc ();
      enter_signature_item s
    | Tsig_module  m  ->
      State.push ~id:m.md_id m.md_loc ();
      TypesIter.modtype s.sig_env s.sig_loc m.md_type.mty_type
    | _ -> enter_signature_item s


  let last () = match State.get () with
    | Module_type :: _ -> debug "Module type before"; true
    | [] -> debug "last"; true
    | _ -> false


  let warning h =
    if last () then
      warn h.State.loc h.id (Hypergraph.unreachable h.view.graph)
    else
      early_warning h.loc h.id h.view

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
      warn last.loc last.id (Hypergraph.unreachable last.view.graph)
    | _ -> ()

  let enter_module_expr modexp =
    let env = modexp.mod_env in
    match modexp.mod_desc with
    | Tmod_constraint (_, _, Tmodtype_explicit ty , _) ->
      begin match ty.mty_desc with
        | Tmty_signature _ -> State.push modexp.mod_loc ()
        | _ -> TypesIter.modtype env modexp.mod_loc ty.mty_type
      end
    | Tmod_constraint (_,_, Tmodtype_implicit , _) ->
      State.push modexp.mod_loc ()
    | _ -> ()

  let leave_module_expr modexp =
    match modexp.mod_desc with
    |  Tmod_constraint _ ->
      debug "Leaving";
      begin match State.pop () with
        | None -> debug "Nested?"
        | Some x ->
          let unreachable = Hypergraph.unreachable x.view.graph in
          warn modexp.mod_loc None unreachable
      end
    | _ -> ()


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
