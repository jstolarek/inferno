open Core

type ('a, 'b) typ = ('a, 'b) Shared.Types.typ =
  | TyVar of 'a
  | TyArrow of ('a, 'b) typ * ('a, 'b) typ
  | TyProduct of ('a, 'b) typ * ('a, 'b) typ
  | TyForall of 'b * ('a, 'b) typ
  | TyMu of 'b * ('a, 'b) typ
  | TyConstrApp of Shared.Types.Type_constr.t * ('a, 'b) typ list
[@@deriving sexp]

type t = (Shared.Types.tyvar, Shared.Types.tyvar) typ [@@deriving sexp]
type restriction = Mono | Poly [@@deriving sexp]

class ['a] fold_visitor =
  object (o)
    method visit (acc : 'a) (ty : t) =
      match ty with
      | TyVar v -> o#visit_var acc v
      | TyArrow (t1, t2) -> o#visit_arrow acc t1 t2
      | TyProduct (t1, t2) -> o#visit_product acc t1 t2
      | TyForall (v, t') -> o#visit_forall acc v t'
      | TyMu (v, t') -> o#visit_mu acc v t'
      | TyConstrApp (constr, args) -> o#visit_constr_app acc constr args

    method visit_var acc v = acc
    method visit_product acc t1 t2 = o#visit (o#visit acc t1) t2
    method visit_arrow acc t1 t2 = o#visit (o#visit acc t1) t2
    method visit_forall acc v t' = o#visit acc t'
    method visit_mu acc v t' = o#visit acc t'

    method visit_constr_app acc constr args =
      List.fold_left ~f:o#visit ~init:acc args
  end

let all_variables t =
  let bind_and_visit visit set v body =
    Shared.Logging.log "found type variable %d\n" v;
    visit (Set.add set v) body
  in
  let visitor =
    object (o)
      inherit [Tyvar.Set.t] fold_visitor
      method! visit_var = Set.add
      method! visit_forall = bind_and_visit o#visit
      method! visit_mu = bind_and_visit o#visit
    end
  in
  visitor#visit Tyvar.Set.empty t

let ftv_ordered ty to_ignore =
  let rec collect_ftvs ty to_ignore =
    let ftv t = collect_ftvs t to_ignore in
    match ty with
    | TyVar v -> if Set.mem to_ignore v then [] else [ v ]
    | TyArrow (t1, t2) | TyProduct (t1, t2) -> List.append (ftv t1) (ftv t2)
    | TyForall (v, t') | TyMu (v, t') ->
        let to_ignore = Set.add to_ignore v in
        collect_ftvs t' to_ignore
    | TyConstrApp (_constr, args) ->
        List.fold_left
          ~f:(fun ftvs arg -> List.append ftvs (ftv arg))
          ~init:[] args
  in
  let dedup l =
    List.fold_right
      ~f:(fun el (res_list, set) ->
        let list = if Set.mem set el then res_list else el :: res_list in
        let set = Set.add set el in
        (list, set))
      ~init:([], Tyvar.Set.empty) l
    |> fst
  in
  collect_ftvs ty to_ignore |> dedup

(* TODO: rename this to free_type_variables *)
let rec ftv ty to_ignore = Tyvar.Set.of_list (ftv_ordered ty to_ignore)

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

type tt = t [@@deriving sexp]

module Subst = struct
  type t = (Tyvar.t, tt, Tyvar.comparator_witness) Map.t
  type subst_alist = (Tyvar.t * tt) list [@@deriving sexp]

  let sexp_of_t subst = Map.to_alist subst |> sexp_of_subst_alist
  let t_of_sexp _ = failwith "not implemented"
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
    let ftv' ty = ftv ty rigid_vars in
    Map.exists subst ~f:(fun ty -> Set.mem (ftv' ty) var)

  let compose ~first ~second = Map.map ~f:(apply second) first
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

let forall vars ty =
  List.fold_right ~f:(fun v ty -> TyForall (v, ty)) ~init:ty vars

module Builtin = struct
  let int = Shared.Types.int_t
  let bool = Shared.Types.bool_t
end

let nominal_of_debruijn t =
  let rec nod t map =
    let app t = nod t map in
    match t with
    | TyVar v -> TyVar (List.nth_exn map v)
    | TyArrow (t1, t2) -> TyArrow (app t1, app t2)
    | TyProduct (t1, t2) -> TyProduct (app t1, app t2)
    | TyForall ((), t') ->
        let fresh = Tyvar.fresh_tyvar () in
        TyForall (fresh, nod t' (fresh :: map))
    | TyMu ((), t') ->
        let fresh = Tyvar.fresh_tyvar () in
        TyForall (fresh, nod t' (fresh :: map))
    | TyConstrApp (constr, args) -> TyConstrApp (constr, List.map ~f:app args)
  in
  nod t []
