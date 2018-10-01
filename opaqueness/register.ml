open Typedtree
open Transl

let str info ((str: structure), _ as arg) =
  let src = info.Misc.sourcefile in
  let id = Ident.create src in
  let _ =
    structure
      { id = Some id; loc = Location.in_file src; env = str.str_final_env}
      str
  in
  arg

let sign info s =
  let src = info.Misc.sourcefile in
  let id = Ident.create src in
  let _ =
    signature
      { id = Some id; loc = Location.in_file src; env = s.sig_final_env}
      s
  in
  s


let () =
  Typemod.ImplementationHooks.add_hook
    "opaqueness warning"
    str

let () =
  Typemod.InterfaceHooks.add_hook
    "opaqueness warning"
    sign
