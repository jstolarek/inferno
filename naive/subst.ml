open Core

type t = (Tyvar.t, Tyvar.comparator_witness, Types.t) Map.t

let empty = Map.empty (module Tyvar)
