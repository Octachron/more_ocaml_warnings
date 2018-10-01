open Types
open Utils
open Formula

let is_abstract ty =
  ty.type_kind = Type_abstract
  && ty.type_manifest = None

module VSet = Ident.Set
module VMap = Ident.Map

type formula = Ident.t Formula.t
type state =
  { arrows: formula list;
    ids: Location.t VMap.t;
    abstracts: VSet.t
  }

let simplif_and x =
  let x = all x in
  match Formula.simplif x with
  | And l -> l
  | x -> [x]

let simplify state =
  let find_satisfied arrows =
    List.fold_left (fun s -> function
        | Var t -> VSet.add t s
        | _ -> s
      ) VSet.empty arrows in
  let rec work s arrows  =
    let s' = find_satisfied @@ simplif_and arrows in
    let s = VSet.union s s' in
    let satisfied x = if VSet.mem x s' then Some True else None in
    if s' = VSet.empty then s, arrows else
      work s @@ List.map(Formula.simplify satisfied) arrows
  in
  let satisfieds, arrows = work VSet.empty state.arrows in
  let ids = VSet.fold VMap.remove satisfieds state.ids in
  let abstracts = VSet.diff state.abstracts state.abstracts in
  { ids; arrows; abstracts  }

let empty = {
  arrows = [];
  ids = VMap.empty;
  abstracts = VSet.empty;
}
let arrows a = { empty with arrows = a }

let unknown abstracts = { empty with abstracts }


let abstracts ids =
  let abstracts = VSet.of_list @@ List.map fst ids in
  let ids = List.fold_left (fun m (x,y) -> VMap.add x y m) VMap.empty ids in
  { empty with ids; abstracts }

let merge x y = {
  arrows= x.arrows @ y.arrows;
  ids = VMap.union (fun _k _x y -> Some y) x.ids y.ids;
  abstracts = VSet.union x.abstracts y.abstracts
}

let fusion =
  List.fold_left (fun acc x -> merge x acc)
    empty

let step_fusion f =
  List.fold_left (fun acc x -> merge (f x) acc)
    empty

let thread ctx state f l =
  List.fold_left (f ctx) state l

let reduce (%) f = function
  | [] -> True
  | a :: q ->
    List.fold_left (fun fs x -> fs % f x) (f a) q


let lift state f x (%) y =
  let state, x = f state x in
  let state, y = f state y in
  state, x % y

module T = Types
(*type state = { env: Env.t; data: slice list }*)
type loc_state =
  { unknowns: VSet.t;
    visited: type_expr list;
    env: Env.t }

type ctx = {
  id: Ident.t option;
  loc: Location.t;
  env: Env.t
}

let local ctx state : loc_state =
  { env= ctx.env; visited = []; unknowns = state.abstracts }
let pp_arrow = Formula.pp pp_ident

let assign_all state =
  let assign map rule =
    let required = Formula.required rule in
    List.fold_left (fun map id -> VMap.add id required map) map
      (Formula.iff rule) in
  let depend_on = List.fold_left assign VMap.empty state.arrows in
  let dependencies id = match VMap.find id depend_on with
    | exception Not_found -> []
    | x -> x in
  VMap.fold (fun id loc l -> (loc, id, dependencies id) :: l)
    state.ids []


let rec signature arrow_only exit ctx abstracts (s:signature) =
  let result = thread ctx (unknown abstracts) sig_item s in
  begin if exit then
    let result = simplify result in
    if not (VMap.is_empty result.ids) then
      Printer.warning ctx.loc ctx.id (assign_all result);
  end;
  if arrow_only then arrows result.arrows else result

and sig_item ctx state  = function
  | Sig_value (id,vd) -> debug"val %a" pp_ident id; value ctx state vd.val_type
  | Sig_type (id,tdl,_) -> debug "type %a" pp_ident id; type' state (id,tdl)

  | Sig_typext _
  | Sig_class_type _ -> state

  | Sig_module (id,m,_) -> module' ctx state id m
  | Sig_modtype (id,mt) -> module_type ctx state id mt
  | Sig_class (_,cd,_) -> class' ctx state cd

and value ctx state ty =
  let x = typ (local ctx state) ty in
  debug "val: %a" pp_arrow x;
  merge state @@ arrows [x]

and typ (ls:loc_state) x = typ0 ls (Ctype.full_expand ls.env x)
and typ_constr ls = function
  | Path.Pident p  when VSet.mem p ls.unknowns ->
    debug "ident %s: unknown" (Ident.name p);
    Formula.Var p
  | p ->
    debug "path %s: T " (Path.name p);
    True
 and typ0 ls x = match x.desc with
    | Tconstr (p,params,_cts) ->
      if List.mem x ls.visited then Formula.False else
      begin try
          let t = Env.find_type p ls.env in
          if is_abstract t then
            typ_constr ls p
          else
            deconstruct { ls with visited= x :: ls.visited } params t
        with Not_found ->
          debug "Not found %s" (Path.name p);
          Formula.False
      end

    | Ttuple ct -> debug "tuple"; tuples ls ct
    | Tpoly (ct, _) | Tlink ct | Tsubst ct -> typ ls ct

    | Tvar _ | Tunivar _
    | Tnil -> debug "variables"; True

    | Tvariant r -> Formula.any (r.row_fields>>= row_field ls)

    | Tarrow (_,x,y,_) ->
      debug "inner arrow";
      typ ls x |- typ ls y
    | Tfield (s,_,ty,rest) ->
      debug "field %s" s;
      typ ls ty &&& typ ls rest
    | Tobject (ty, _c) (*when !c = None*) ->
      debug "object";
      typ ls ty

    (* not yet implemented *)
    (*| Tobject _ -> []  ? *)
    | Tpackage (p,_nl,_) ->
      let modtypedecl = Env.find_modtype p ls.env in
      let ctx = { env = ls.env; id = None; loc = Location.none } in
      let state =
        modtype false ctx (unknown ls.unknowns) modtypedecl.mtd_type in
      all (state.arrows)

  and row_field ls (_, r) = match r with
    | Rpresent (Some t) -> [typ ls t]
    | Rpresent None | Rabsent -> []
    | Reither _ -> assert false

  and deconstruct ls params tyd =
    let back = Btype.snapshot () in
    let f =
      try begin
        List.iter2 (fun x y -> Ctype.unify ls.env x y) params tyd.type_params;
          match tyd.type_kind with
          | Type_record (l,_) -> labels ls l
          | Type_variant l ->
            let constr (x:constructor_declaration) =
              debug "constructor: %a" pp_ident x.cd_id;
              echo "arg, " pp_arrow @@
              match x.cd_args with
              | Cstr_tuple t -> tuples ls t
              | Cstr_record ld-> labels ls ld in
            Formula.any (List.map constr l)
          | Type_abstract | Type_open -> True
        end with Ctype.Unify _ -> False in
    Btype.backtrack back;
    debug "Deconstructing to %a" pp_arrow f;
    f

and modtype exit ctx state = function
  | None -> state
  | Some mtd ->
    begin match Env.scrape_alias ctx.env mtd with
      | Mty_signature s ->
        let arrows = signature true exit ctx state.abstracts s in
        merge state arrows
      | _ -> state
    end
and module_type ctx state _id mt =
  let () =
    ignore @@
    modtype false { ctx with id = None; loc = mt.mtd_loc } empty mt.mtd_type in
  state

and type' state (id,t) =
  if is_abstract t then
    merge state @@ abstracts [id, t.type_loc]
  else
    state
and module' ctx state id md =
  modtype true
    { ctx with id=Some id; loc=md.md_loc} state (Some md.md_type)

(*and modtype _state _vd = assert false*)
and class' ctx state (c:class_declaration) =
  merge state @@ arrows [ class_typ (local ctx state) c.cty_type ]

and class_typ ls (x:class_type) = match x with
  | Cty_arrow (_,ty, c) -> typ ls ty |- class_typ ls c
  | Cty_constr (_,_,c) -> class_typ ls c
  | Cty_signature cty -> typ ls cty.csig_self

and labels ls l =
    reduce (&&&) (fun x -> typ ls x.ld_type) l
and tuples ls l =
    reduce (&&&) (typ ls) l

open Typedtree
let rec tsignature exit ctx abstracts (s:signature) =
  let env = s.sig_final_env in
  let result =
    thread {ctx with env} (unknown abstracts) tsig_item s.sig_items in
  begin if exit then
      let result = simplify result in
      if not (VMap.is_empty result.ids) then
        Printer.warning ctx.loc ctx.id (assign_all result);
  end;
  result

and tsig_item ctx state (si:signature_item)  =
  let ctx = { ctx with env = si.sig_env } in
  match si.sig_desc with
  | Tsig_value vd -> debug"val %a" pp_ident vd.val_id;
    value ctx state vd.val_desc.ctyp_type
  | Tsig_type (_,tdl) ->
    List.fold_left (fun state (td:type_declaration) ->
        type' state (td.typ_id, td.typ_type)
      ) state tdl
  | Tsig_typext _
  | Tsig_class_type _ -> state

  | Tsig_module m -> tmodule ctx state m
  | Tsig_modtype mt -> tmodule_type ctx state mt
  | Tsig_class cd -> thread ctx state tclass cd

  | Tsig_recmodule ml -> List.fold_left (tmodule ctx) state ml

  | Tsig_open _ | Tsig_exception _ | Tsig_attribute _ -> state
  | Tsig_include i -> include' ctx state i

and tmodule ctx state md =
  tmodtype true true
    { ctx with id=Some md.md_id; loc=md.md_loc}
    state (Some md.md_type)
and tmodtype arrow_only exit ctx state = function
  | None -> state
  | Some mtd -> match mtd.mty_desc with
    | Tmty_signature s ->
      let state' = tsignature exit ctx state.abstracts s in
      merge state (if arrow_only then arrows state'.arrows else state')
    | _ ->
      begin match Env.scrape_alias ctx.env mtd.mty_type with
        | Mty_signature s ->
          let arrows = signature arrow_only exit ctx state.abstracts s in
          merge state arrows
        | _ -> state
      end

and tmodule_type ctx state mt =
  let () =
    ignore @@
    tmodtype true false
      { ctx with id = None; loc = mt.mtd_loc }
      empty mt.mtd_type in
  state
and tclass ctx state (c:_ class_infos ) =
  merge state @@ arrows [class_typ (local ctx state) c.ci_expr.cltyp_type]
and include' ctx state (i: _ include_infos) =
  tmodtype false false { ctx with id = None; loc = i.incl_loc }
    state (Some i.incl_mod)

let rec structure exit ctx abstracts (s:structure) =
  let env = s.str_final_env in
  let result =
    thread {ctx with env} (unknown abstracts) str_item s.str_items in
  begin if exit then
    let result = simplify result in
    if not (VMap.is_empty result.ids) then
      Printer.warning ctx.loc ctx.id (assign_all result);
  end;
  result.arrows

and str_item ctx state (si:structure_item)  =
  let ctx = { ctx with env = si.str_env } in
  match si.str_desc with
  | Tstr_value (_, vbs) ->
    List.fold_left (fun state vb ->
        value ctx state vb.vb_pat.pat_type
      ) state vbs
  | Tstr_primitive vd -> value ctx state vd.val_desc.ctyp_type
  | Tstr_type (_,tdl) ->
    List.fold_left (fun state (td:type_declaration) ->
        type' state (td.typ_id, td.typ_type)
      ) state tdl
  | Tstr_typext _
  | Tstr_class_type _ -> state

  | Tstr_module m -> smodule ctx state m
  | Tstr_modtype mt -> tmodule_type ctx state mt
  | Tstr_class cd ->
    List.fold_left (fun state (x,_) -> sclass state x) state cd

  | Tstr_recmodule ml -> List.fold_left (smodule ctx) state ml

  | Tstr_open _ | Tstr_exception _ | Tstr_attribute _
  | Tstr_eval _ -> state
  | Tstr_include i -> sinclude ctx state i

and sclass _x _y = assert false
and smodule _ctx _state _m = assert false
and sinclude _ctx _state _i = assert false

let signature ctx s = tsignature true ctx VSet.empty s
let structure ctx s = structure true ctx VSet.empty s
