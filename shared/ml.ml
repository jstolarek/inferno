(* This file is in part taken from François Pottier's Inferno implementation *)

open Core

type ty = Types.nominal_type


type tevar = string [@@deriving compare, eq, sexp]

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


let rec is_val = function
  | App _            -> false
  | Let (_, _, n, m) -> is_val n && is_val m
  | Pair (n, m) -> is_val n && is_val m
  | Proj (_, m) ->  is_val m
  | _                   -> true

(* Value restriction *)
let rec is_gval = function
  | App _ | FrozenVar _ -> false
  | Let (_, _, n, m) -> is_val n && is_gval m
  | Pair (n, m) -> is_val n && is_val m
  | Proj (_, m) ->  is_gval m
  | _                         -> true
