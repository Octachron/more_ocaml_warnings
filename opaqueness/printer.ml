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
