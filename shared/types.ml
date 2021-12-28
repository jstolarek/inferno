 open Core

module type Type_constr =
  sig
    type t [@@deriving compare, eq]

    val show : t -> string
    val arity : t -> int

    val int : t
    val bool : t
    val list : t
  end

module Type_constr : Type_constr =
  struct
    type t = string * int [@@deriving compare, eq]

    let show = fst
    let arity = snd

    let int = ("int", 0)
    let bool = ("bool", 0)
    let list = ("list", 1)
  end


type ('a, 'b) typ =
  | TyVar of 'a
  | TyArrow of ('a, 'b) typ * ('a, 'b) typ
  | TyProduct of ('a, 'b) typ * ('a, 'b) typ
  | TyForall of 'b * ('a, 'b) typ
  | TyMu of 'b * ('a, 'b) typ
  | TyConstrApp of Type_constr.t * ('a, 'b) typ list

type tyvar = int

type nominal_type = (tyvar, tyvar) typ

type debruijn_type = (DeBruijn.index, unit) typ

let int_t = TyConstrApp (Type_constr.int, [])
let bool_t = TyConstrApp (Type_constr.bool, [])
let list_t t = TyConstrApp (Type_constr.list, [t])
