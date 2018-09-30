open Utils

module Digraph = Strongly_connected_components.Make(Ident)


let components l =
  Array.to_list
  @@ Digraph.connected_components_sorted_from_roots_to_leaf
  @@ List.fold_left (fun m (_,k,edges) ->
      let edges = Ident.Set.of_list edges in
      Ident.Map.add k edges m)
    Ident.Map.empty l

let locs l =
  List.fold_left (fun m (loc,k,_) -> Ident.Map.add k loc m) Ident.Map.empty l

let print_main ppf =
    Misc.Color.setup !Clflags.color;
    Format.fprintf ppf
      "@[@{<warning>Warning [opaqueness]:@}@ \
       some abstract types cannot be constructed@]@,"

type subwarning =
  { start: Location.t; locs: Location.t list; component : Digraph.component }

let with_warning printer ppf x= Format.fprintf ppf "@{<warning>%a@}" printer x

let extract_subwarning locs component =
  let ids = match component with
    | Digraph.No_loop id -> [id]
    | Has_loop x -> x in
  let locs =
    List.sort compare @@ List.map (fun id -> Ident.Map.find id locs) ids in
  let start = List.hd locs in
  { start; locs; component }

let subcompare x y = compare x.start y.start
let print_sub ppf sub =
  let pp_ident = with_warning pp_ident in
  let p x = Format.fprintf ppf x in
  List.iter (Location.print ppf) sub.locs;
  match sub.component with
   | Digraph.No_loop id -> p "Type %a is never built by a function." pp_ident id
   | Has_loop [id]  -> p "Type %a depends on itself." pp_ident id
   | Has_loop l ->
     p "@[All types in the set@ {%a}@ depends on another type in this set@]"
            (Format.pp_print_list ~pp_sep:(sep ";@ ") pp_ident) l

let print_subs =
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.fprintf ppf "@,")
    print_sub

let warning l =
  let subs =
    List.sort subcompare
    @@ List.map (extract_subwarning @@ locs l)
    @@ components l in
  Format.eprintf "@[<v>%t%a@]@." print_main print_subs subs
