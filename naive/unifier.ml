open Core

(** This assumes that [subst] has already been applied to [ty1] and [ty2].
    The first return value (if Ok) indicates whether the types were already
    equal. *)
let rec unify_and_check_equal rigid_vars mono_flex_vars subst ty1 ty2 =
  let open Types in
  let unify = unify_and_check_equal in
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
  match (ty1, ty2) with
  | TyVar a, other_ty | other_ty, TyVar a -> (
      let free_flex () = Types.ftv other_ty rigid_vars in
      match other_ty with
      | TyVar b when Tyvar.equal a b -> Result.Ok (true, mono_flex_vars, subst)
      | _ when Set.mem rigid_vars a ->
          (* Unifying rigid var with something that isn't itself *)
          Result.Error Tc_errors.Unification_clash_failure
      | _ when Set.mem (free_flex ()) a ->
          Result.Error Tc_errors.Unification_occurs_failure
      | _ ->
          let subst = Types.Subst.set subst a other_ty in
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
  | TyForall (q1, ty1), TyForall (q2, ty2) ->
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
        (unify rigid_vars mono_flex_vars subst ty1 ty2)
        ~f:check_escape
  | TyMu (_q1, _ty1), TyForall (_q2, _ty2) ->
      failwith "not implemented at the moment"
  | _ -> Result.Error Tc_errors.Unification_clash_failure

let equal ty1 ty2 =
  let res =
    unify_and_check_equal Tyvar.Set.empty Tyvar.Set.empty Types.Subst.empty ty1
      ty2
  in
  match res with Result.Ok (equal, _, _) -> equal | Result.Error _ -> false

let unify rv mfv s ty1 ty2 =
  Result.map
    ~f:(fun (equal, mono_flex_vars, subst) -> (mono_flex_vars, subst))
    (unify_and_check_equal rv mfv s ty1 ty2)
