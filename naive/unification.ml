open Core

(**
    As a minor diversion from the paper, we get the initial substitution
    [subst] and return an updated version of it, instead of returning something
    that needs to be composed with the initial substitution.
    The first return value (if Ok) indicates whether the types were already
    equal. *)
let rec unify_and_check_equal ~ordered rigid_vars mono_flex_vars subst ty1 ty2 =
  let open Types in
  let unify = unify_and_check_equal ~ordered in
  let try_unify state_res ty1 ty2 =
    Result.bind state_res ~f:(fun (equal, flex, subst) ->
        let ty1 = Subst.apply subst ty1 in
        let ty2 = Subst.apply subst ty2 in
        let unify_res = unify rigid_vars flex subst ty1 ty2 in
        Result.map unify_res ~f:(fun (a, b, c) -> (a && equal, b, c)))
  in
  let unify_list args1 args2 =
    List.fold2_exn ~f:try_unify
      ~init:(Result.Ok (true, mono_flex_vars, subst))
      args1 args2
  in

  (* let is_same_var a = function *)
  (*   | TyVar b -> Tyvar.equal a b *)
  (*   | Forall _ as other when not ordered -> *)
  (*     (\* When ordered quantifiers are disabled, a and ∀ b_1, ... b_n. a are *)
  (*        equivalent (assuming that all b_i <> a)  *\) *)
  (*     (match Types.freshen_quantifiers other with *)
  (*     | (_, TyVar b) -> Tyvar.equal a b *)
  (*     | _ -> false) *)
  (* in *)

  (* Naive, but effective:
     In unordered mode, if tyi is of the form ∀ b_1, ... b_n.t', then we
     remove all b_i that do not appear in t' *)
  let ty1, ty2 =
    if ordered then (ty1, ty2)
    else
      ( Types.strip_useless_toplevel_forall ty1,
        Types.strip_useless_toplevel_forall ty2 )
  in

  match (ty1, ty2) with
  | TyVar a, other_ty | other_ty, TyVar a -> (
      let free_flex () = Types.ftv other_ty rigid_vars in
      match other_ty with
      | TyVar b when Tyvar.equal a b -> Result.Ok (true, mono_flex_vars, subst)
      | TyVar b
        when (not (phys_equal ty1 other_ty))
             && Set.mem rigid_vars a
             && not (Set.mem rigid_vars b) ->
          (* Trying to unify a ~ b, where a is rigid and b is flexible.
             Just do b ~ a instead, to trigger one of the cases below *)
          unify rigid_vars mono_flex_vars subst ty2 ty1
      | _ when Set.mem rigid_vars a ->
          (* Unifying rigid var with something that isn't itself or a flexible variable *)
          Result.Error Tc_errors.Unification_clash_failure
      | _ when Set.mem (free_flex ()) a ->
          Result.Error Tc_errors.Unification_occurs_failure
      | _ ->
          (* Actual unifcation. update all mappings, including the a -> a one *)
          let singleton = Types.Subst.singleton a other_ty in
          let subst = Map.map ~f:(Types.Subst.apply singleton) subst in

          let mono_flex_vars =
            if Set.mem mono_flex_vars a then
              Tyvar.Set.union mono_flex_vars (free_flex ())
            else mono_flex_vars
          in
          if
            Set.mem mono_flex_vars a
            && not (Types.is_monomorphic other_ty rigid_vars mono_flex_vars)
          then Result.Error Tc_errors.Cannot_monomorphise
          else Result.Ok (false, mono_flex_vars, subst))
  | TyProduct (tya1, tya2), TyProduct (tyb1, tyb2)
  | TyArrow (tya1, tya2), TyArrow (tyb1, tyb2) ->
      unify_list [ tya1; tya2 ] [ tyb1; tyb2 ]
  | TyConstrApp (constr1, args1), TyConstrApp (constr2, args2)
    when Shared.Types.Type_constr.equal constr1 constr2 ->
      unify_list args1 args2
  | TyForall (a, ty'), other_ty | other_ty, TyForall (a, ty') ->
      if ordered then
        unify_forall_ordered rigid_vars mono_flex_vars subst (a, ty') other_ty
      else
        unify_forall_unordered rigid_vars mono_flex_vars subst (a, ty') other_ty
  | TyMu (_q1, _ty1), _ | _, TyMu (_q1, _ty1) ->
      failwith "not implemented at the moment"
  | _ -> Result.Error Tc_errors.Unification_clash_failure

and unify_forall_ordered rigid_vars mono_flex_vars subst (q1, ty1) other_ty =
  let open Types in
  match other_ty with
  | TyForall (q2, ty2) ->
      let fresh = Tyvar.fresh_tyvar () in
      let subst1 = Types.Subst.singleton q1 (TyVar fresh) in
      let subst2 = Types.Subst.singleton q2 (TyVar fresh) in
      let ty1 = Types.Subst.apply subst1 ty1 in
      let ty2 = Types.Subst.apply subst2 ty2 in

      let check_escape ((equal, new_flex_mono_vars, new_subst) as result) =
        let escapes = Types.Subst.range_contains new_subst rigid_vars fresh in
        if escapes then Result.Error Tc_errors.Quantifier_escape
        else Result.Ok result
      in
      let rigid_vars = Set.add rigid_vars fresh in
      Result.bind
        (unify_and_check_equal ~ordered:true rigid_vars mono_flex_vars subst ty1
           ty2)
        ~f:check_escape
  | _ -> Result.Error Tc_errors.Unification_clash_failure

and unify_forall_unordered rigid_vars mono_flex_vars subst (q1, ty1) other_ty =
  failwith "todo"

type unifier_state = State.unifier_state = {
  mono_flex_vars : Tyvar.Set.t;
  subst : Types.Subst.t;
}

let mk_equal ~ordered ty1 ty2 =
  let res =
    unify_and_check_equal ~ordered Tyvar.Set.empty Tyvar.Set.empty
      Types.Subst.empty ty1 ty2
  in
  match res with Result.Ok (equal, _, _) -> equal | Result.Error _ -> false

let mk_unify ~ordered ~rigid_vars:rv u_state ty1 ty2 =
  Result.map
    ~f:(fun (equal, mono_flex_vars, subst) -> { mono_flex_vars; subst })
    (unify_and_check_equal ~ordered rv u_state.mono_flex_vars u_state.subst ty1
       ty2)

module type Unifier = sig
  val equal : Types.t -> Types.t -> bool

  val unify :
    rigid_vars:Tyvar.Set.t ->
    unifier_state ->
    Types.t ->
    Types.t ->
    (unifier_state, Tc_errors.errors) Result.t
end

module Ordered : Unifier = struct
  let equal = mk_equal ~ordered:true
  let unify = mk_unify ~ordered:true
end

module Unordered : Unifier = struct
  let equal = mk_equal ~ordered:false
  let unify = mk_unify ~ordered:false
end
