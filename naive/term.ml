type tevar = Tevar.t [@@deriving sexp]


type t = Shared.Ml.term =
  | Var of tevar
  | FrozenVar of tevar
  | Abs of tevar * Types.t option * t
  | App of t * t
  | Let of tevar * Types.t option * t * t
  | Pair of t * t
  | Proj of int * t
  | Int of int
  | Bool of bool

let is_val = Shared.Ml.is_val
let is_gval = Shared.Ml.is_gval
