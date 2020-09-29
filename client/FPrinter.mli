(* A pretty-printer for F. *)

open PPrint
open F

val print_type: nominal_type -> document
val print_term: nominal_term -> document

val print_debruijn_type: debruijn_type -> document
val print_debruijn_term: debruijn_term -> document
