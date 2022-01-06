open Core

module T = struct
  type t = Shared.Types.tyvar [@@deriving compare, sexp, eq]
end

module Comparable = struct
  include T
  include Comparator.Make (T)
end

include Comparable

(* Fresh tyvar names *)
let set_initial_tyvar, fresh_tyvar =
  let counter = ref 0 in
  let set_start min = counter := min in
  let postincrement r =
    let v = !r in
    r := v + 1;
    v
  in
  let fresh () = postincrement counter in
  (set_start, fresh)

module Set = Set.Make (Comparable)

type set = Set.t

let empty_set = Set.empty
let set_of_list l = Set.of_list l
let singleton_set v = Set.singleton v
