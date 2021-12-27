open Core

module T =
  struct
    type t = string [@@deriving show, compare, sexp]

  end


include T
include Comparator.Make(T)
