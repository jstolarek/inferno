 open Core

module type Type_constr =
  sig
    type t [@@deriving compare, eq, sexp]

    val show : t -> string
    val arity : t -> int

    val int : t
    val bool : t
    val list : t
  end

module Type_constr : Type_constr =
  struct
    type t = string * int [@@deriving compare, eq, sexp]

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

type tyvar = int [@@deriving compare, eq, sexp]

type nominal_type = (tyvar, tyvar) typ

type debruijn_type = (DeBruijn.index, unit) typ

let int_t = TyConstrApp (Type_constr.int, [])
let bool_t = TyConstrApp (Type_constr.bool, [])
let list_t t = TyConstrApp (Type_constr.list, [t])


let rec string_of_typ (t : nominal_type)  =
  match t with
  | TyVar a -> "TyVar " ^ string_of_int a
  | TyArrow (a, b) -> "(" ^ string_of_typ a ^ " -> " ^ string_of_typ b ^ ")"
  | TyProduct (a, b) -> "(" ^ string_of_typ a ^ "×" ^ string_of_typ b ^ ")"
  | TyForall (q, t) -> "∀ " ^ string_of_int q ^ ". " ^ string_of_typ t
  | TyMu (q, t) -> "μ " ^ string_of_int q ^ ". " ^ string_of_typ t
  | TyConstrApp (constr, []) -> Type_constr.show constr
  | TyConstrApp (constr, args) ->
    let c_name = Type_constr.show constr in
    let arg_strings = List.map ~f:string_of_typ args in
    c_name ^ " [" ^ String.concat ~sep:", " arg_strings ^ "]"
