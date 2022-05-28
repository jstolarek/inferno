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
[@@deriving sexp]

let forall (qs, c) = List.fold_right ~f:(fun q c -> Forall (q, c)) ~init:c qs
let exists (qs, c) = List.fold_right ~f:(fun q c -> Exists (q, c)) ~init:c qs

let conj = function
  | [] -> True
  | [ c ] -> c
  | c :: cs -> List.fold_right ~f:(fun conj c -> And (conj, c)) ~init:c cs

let is_true = function True -> true | _ -> false
let is_exists = function Exists _ -> true | _ -> false
let is_freeze = function Freeze _ -> true | _ -> false

let freshen_binders constr =
  let module Tyvar_state (State : sig
    type t
  end) =
  struct
    type state = State.t
    type 'a t = state -> state * 'a

    let return v s = (s, v)

    let bind : 'a t -> ('a -> 'b t) -> 'b t =
     fun sm f s ->
      let s', v' = sm s in
      f v' s'

    let ( let* ) = bind
  end in
  let rec freshen_type tyvar_map ty =
    let freshen t all_tyvars = freshen_type tyvar_map t all_tyvars in
    let open Types in
    let open Tyvar_state (Tyvar.Set) in
    match ty with
    | TyVar v -> (
        match Map.find tyvar_map v with
        | Some v' -> return (TyVar v')
        | None -> return ty)
    | TyArrow (t1, t2) ->
        let* t1 = freshen t1 in
        let* t2 = freshen t2 in
        return (TyArrow (t1, t2))
    | TyProduct (t1, t2) ->
        let* t1 = freshen t1 in
        let* t2 = freshen t2 in
        return (TyProduct (t1, t2))
    | TyForall (v, t') ->
        let* v, tyvar_map =
         fun all_tyvars ->
          let v, tyvar_map =
            if Set.mem all_tyvars v then
              let fresh = Tyvar.fresh_tyvar () in
              (fresh, Map.set tyvar_map ~key:v ~data:fresh)
            else (v, tyvar_map)
          in
          let all_tyvars = Set.add all_tyvars v in
          (all_tyvars, (v, tyvar_map))
        in
        let* t' = freshen_type tyvar_map t' in
        return (TyForall (v, t'))
    | TyMu _ -> failwith "not supported"
    | TyConstrApp (constr, args) ->
        let* args tyvars =
          List.fold_right
            ~f:(fun t (vars, args) ->
              let new_vars, arg = freshen t vars in
              (new_vars, arg :: args))
            ~init:(tyvars, []) args
        in
        return (TyConstrApp (constr, args))
  in
  let module Vars = struct
    type t = Tevar.Set.t * Tyvar.Set.t
  end in
  let open Tyvar_state (Vars) in
  let rec handle_tyvar_binding binder constr tevar_map tyvar_map =
    let* binder, tyvar_map =
     fun (all_tevars, all_tyvars) ->
      let res =
        if Set.mem all_tyvars binder then
          let fresh = Tyvar.fresh_tyvar () in
          let tyvar_map = Map.set tyvar_map ~key:binder ~data:fresh in
          (fresh, tyvar_map)
        else (binder, tyvar_map)
      in
      let all_tyvars = Set.add all_tyvars binder in
      ((all_tevars, all_tyvars), res)
    in
    let* constr = freshen_constraint tyvar_map tevar_map constr in
    return (binder, constr)
  and handle_tevar_binding binder constr tevar_map tyvar_map =
    let* binder, tevar_map =
     fun (all_tevars, all_tyvars) ->
      let res =
        if Set.mem all_tevars binder then
          let fresh = Tevar.fresh_tevar () in
          let tevar_map = Map.set tevar_map ~key:binder ~data:fresh in
          (fresh, tevar_map)
        else (binder, tevar_map)
      in
      let all_tevars = Set.add all_tevars binder in
      ((all_tevars, all_tyvars), res)
    in
    let* constr = freshen_constraint tyvar_map tevar_map constr in
    return (binder, constr)
  and freshen_constraint tyvar_map tevar_map constr =
    let recurse constr = freshen_constraint tyvar_map tevar_map constr in
    let handle_type t (all_tevars, tyvars) =
      let tyvars, t = freshen_type tyvar_map t tyvars in
      ((all_tevars, tyvars), t)
    in
    match constr with
    | True -> return constr
    | And (c1, c2) ->
        let* c1 = recurse c1 in
        let* c2 = recurse c2 in
        return (And (c1, c2))
    | Equiv (t1, t2) ->
        let* t1 = handle_type t1 in
        let* t2 = handle_type t2 in
        return (Equiv (t1, t2))
    | Freeze (x, t) | Inst (x, t) ->
        let* t = handle_type t in
        let x = match Map.find tevar_map x with None -> x | Some y -> y in
        if is_freeze constr then return (Freeze (x, t))
        else return (Inst (x, t))
    | Exists (a, constr') | Forall (a, constr') ->
        let* a, constr' = handle_tyvar_binding a constr' tevar_map tyvar_map in
        if is_exists constr then return (Exists (a, constr'))
        else return (Forall (a, constr'))
    | Def (x, ty, constr') ->
        let* ty = handle_type ty in
        let* x, constr' = handle_tevar_binding x constr' tevar_map tyvar_map in
        return (Def (x, ty, constr'))
    | Let (restr, x, a, constr1, constr2) ->
        let* a, constr1 = handle_tyvar_binding a constr1 tevar_map tyvar_map in
        let* x, constr2 = handle_tevar_binding x constr2 tevar_map tyvar_map in
        return (Let (restr, x, a, constr1, constr2))
  in
  freshen_constraint Types.Subst.empty Tevar.Env.empty constr
    (Tevar.Set.empty, Tyvar.Set.empty)
  |> snd
