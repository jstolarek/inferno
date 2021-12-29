open Core

module T = struct
  type t = Shared.Ml.tevar [@@deriving compare, sexp]
end

module Comparable = struct
  include T
  include Comparator.Make (T)
end

include Comparable

module Env = struct
  type 'a t = (T.t, 'a, comparator_witness) Map.t

  let get env tevar = Map.find_exn env tevar
  let empty = Map.empty (module Comparable)
  let set env var ty = Map.set env ~key:var ~data:ty
end
