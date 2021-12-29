open Core

type t =
  | True
  | And of t * t
  | Equiv of Types.t * Types.t
  | Freeze of Term.tevar * Types.t
  | Inst of Term.tevar * Types.t
  | Exists of Tyvar.t * t
  | Forall of Tyvar.t * t
  | Def of Term.tevar * Types.t * t
  | Let of Types.restriction * Term.tevar * Tyvar.t * t * t

let is_true = function True -> true | _ -> false
