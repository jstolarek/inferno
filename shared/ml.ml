type ty = Types.nominal_type

type tevar = string

(* Fresh tevar names *)
let fresh_tevar =
  let postincrement r =
    let v = !r in
    r := v + 1;
    v
  in
  let counter = ref 0 in
  fun () -> "_x" ^ string_of_int (postincrement counter)

type term =
  | Var of tevar
  | FrozenVar of tevar
  | Abs of tevar * ty option * term
  | App of term * term
  | Let of tevar * ty option * term * term
  | Pair of term * term
  | Proj of int * term
  | Int of int
  | Bool of bool
