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

let forall (qs, c) = List.fold_right ~f:(fun q c -> Forall (q, c)) ~init:c qs
let exists (qs, c) = List.fold_right ~f:(fun q c -> Exists (q, c)) ~init:c qs
let conj = function
    | [] -> True
    | [c] -> c
    | c :: cs ->  List.fold_right ~f:(fun conj c -> And (conj, c)) ~init:c cs

let is_true = function True -> true | _ -> false
