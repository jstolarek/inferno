open Core

let verbose = true

let log desc data =
  if verbose then
    Printf.printf desc data

let log_message message =
  log "%s\n" message

let log_sexp desc sexp =
  let s = Sexp.to_string_hum sexp in
  log desc s
