open Utils

let print_main ppf =
    Misc.Color.setup !Clflags.color;
    Format.fprintf ppf
      "@[@{<warning>Warning [opaqueness]:@}@ \
       some abstract types cannot be constructed@]@,"


let with_warning printer ppf x= Format.fprintf ppf "@{<warning>%a@}" printer x
let print_sub ppf (loc,id,free) =
  let pp_ident = with_warning pp_ident in
  let p x = Format.fprintf ppf x in
  Location.print ppf loc;
  match free with
   | [] -> p "Type %a is never built by a function." pp_ident id
   | l when List.mem id l -> p "Type %a depends on itself." pp_ident id
   | l -> p "@[Type %a depends on@ %a@]" pp_ident id
            (Format.pp_print_list ~pp_sep:(sep ",@ ") pp_ident) l

let print_subs =
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.fprintf ppf "@,")
    print_sub

let warning l =
  Format.eprintf "@[<v>%t%a@]@." print_main print_subs l
