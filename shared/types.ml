type ('a, 'b) typ =
  | TyVar of 'a
  | TyArrow of ('a, 'b) typ * ('a, 'b) typ
  | TyProduct of ('a, 'b) typ * ('a, 'b) typ
  | TyForall of 'b * ('a, 'b) typ
  | TyMu of 'b * ('a, 'b) typ
  | TyInt
  | TyBool

type tyvar =
    int

type nominal_type =
    (tyvar, tyvar) typ

type debruijn_type =
    (DeBruijn.index, unit) typ
