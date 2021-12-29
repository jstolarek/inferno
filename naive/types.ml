open Core

type ('a, 'b) typ = ('a, 'b) Shared.Types.typ =
  | TyVar of 'a
  | TyArrow of ('a, 'b) typ * ('a, 'b) typ
  | TyProduct of ('a, 'b) typ * ('a, 'b) typ
  | TyForall of 'b * ('a, 'b) typ
  | TyMu of 'b * ('a, 'b) typ
  | TyConstrApp of Shared.Types.Type_constr.t * ('a, 'b) typ list

type t = (Shared.Types.tyvar, Shared.Types.tyvar) typ
type restriction = Mono | Poly

let rec free_flexible_variables ty to_ignore =
  let ftv ty = free_flexible_variables ty to_ignore in
  match ty with
  | TyVar v ->
      if Set.mem to_ignore v then Tyvar.empty_set else Tyvar.singleton_set v
  | TyArrow (t1, t2) | TyProduct (t1, t2) -> Set.union (ftv t1) (ftv t2)
  | TyForall (v, t') | TyMu (v, t') ->
      let to_ignore = Set.add to_ignore v in
      free_flexible_variables t' to_ignore
  | TyConstrApp (_constr, args) ->
      List.fold_left
        ~f:(fun set arg -> Set.union set (ftv arg))
        ~init:Tyvar.empty_set args

let is_monomorphic ty rigid_vars flex_mono_vars =
  let rec is_mono ty all_mono_vars =
    match ty with
    | TyVar v -> Set.mem all_mono_vars v
    | TyArrow (t1, t2) | TyProduct (t1, t2) ->
        is_mono t1 all_mono_vars && is_mono t2 all_mono_vars
    | TyForall (v, t') -> false
    | TyMu (v, t') ->
        let mono_vars = Set.add all_mono_vars v in
        is_mono t' mono_vars
    | TyConstrApp (_constr, args) ->
        List.for_all ~f:(fun t -> is_mono t all_mono_vars) args
  in
  is_mono ty (Set.union rigid_vars flex_mono_vars)

module Subst = struct
  type nonrec t = (Tyvar.t, t, Tyvar.comparator_witness) Map.t

  let empty = Map.empty (module Tyvar)
  let get (subst : t) var = Map.find_exn subst var
  let set subst var ty = Map.set subst ~key:var ~data:ty

  let can_demote (subst : t) rigid_vars flex_mono_vars vars_to_check =
    let rec cd var = is_monomorphic (get subst var) rigid_vars flex_mono_vars in
    Set.for_all vars_to_check ~f:cd

  (* This is not capture avoiding, but relies on the user to ensure this *)
  let rec apply subst t =
    let app = apply subst in
    if Map.is_empty subst then t
    else
      match t with
      | TyVar v -> (
          match Map.find subst v with
          | None -> t
          | Some replacement -> replacement)
      | TyArrow (t1, t2) -> TyArrow (app t1, app t2)
      | TyProduct (t1, t2) -> TyProduct (app t1, app t2)
      | TyForall (v, t') ->
          let subst = Map.remove subst v in
          TyForall (v, apply subst t')
      | TyMu (v, t') ->
          let subst = Map.remove subst v in
          TyForall (v, apply subst t')
      | TyConstrApp (constr, args) -> TyConstrApp (constr, List.map ~f:app args)

  let singleton var ty = Map.singleton (module Tyvar) var ty

  let range_contains subst rigid_vars var =
    let ftv ty = free_flexible_variables ty rigid_vars in
    Map.exists subst ~f:(fun ty -> Tyvar.Set.mem (ftv ty) var)
end

(* Assuming iso-recursive types here, where mu types need to be explicitly
   unrolled to yield forall type *)
let rec split_toplevel_quantifiers = function
  | TyForall (q, ty) ->
      let qs', ty' = split_toplevel_quantifiers ty in
      (q :: qs', ty')
  | ty -> ([], ty)

let freshen_quantifiers ty =
  let qs, h = split_toplevel_quantifiers ty in
  let fresh_qs = List.map ~f:(fun _ -> Tyvar.fresh_tyvar ()) qs in
  let subst =
    List.fold2_exn
      ~f:(fun subst old_q new_q -> Subst.set subst old_q (TyVar new_q))
      ~init:Subst.empty qs fresh_qs
  in
  (fresh_qs, Subst.apply subst h)
