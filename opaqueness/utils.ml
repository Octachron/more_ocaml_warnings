let bind f l = List.fold_right (fun x acc -> (f x) @ acc) l []
let ( >>= ) l f = bind f l

let debug fmt = Format.ifprintf Format.err_formatter
    ("@[debug: @[" ^^ fmt ^^ "@]@]@.")


let echo pre pp x = debug (pre ^^ "%a") pp x; x
let capture pp f x =
  let y = f x in
  debug "%a@ => %a" pp x pp y;
  y

let pp_ident ppf id = Format.fprintf ppf "%s" (Ident.name id)

let const s ppf = Format.fprintf ppf "%(%)" s
let sep s ppf () = const s ppf
