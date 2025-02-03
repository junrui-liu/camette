open Base
include Z

let t_of_sexp = Fn.compose of_string Sexp.to_string
let sexp_of_t = Fn.compose Parsexp.Single.parse_string_exn to_string
let pp ppf x = Stdlib.Format.fprintf ppf "%s" (to_string x)
