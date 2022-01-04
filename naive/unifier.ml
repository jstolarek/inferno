open Core

(* TODO: no, this doesn't correctly implement \theta' \comp \theta*)

(** This assumes that [subst] has already been applied to [ty1] and [ty2] *)
let rec unify rigid_vars mono_flex_vars subst ty1 ty2 =
  let open Types in
  let try_unify state_res ty1 ty2 =
    Result.bind state_res ~f:(fun (flex, subst) ->
        unify rigid_vars flex subst ty1 ty2)
  in
  let unify_list args1 args2 =
    List.fold2_exn ~f:try_unify
      ~init:(Result.Ok (mono_flex_vars, subst))
      args1 args2
  in
  match (ty1, ty2) with
  | TyVar a, other_ty | other_ty, TyVar a -> (
      let free_flex () = Types.ftv other_ty rigid_vars in
      match other_ty with
      | TyVar b when Tyvar.equal a b -> Result.Ok (mono_flex_vars, subst)
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
          else Result.Ok (mono_flex_vars, subst))
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

      let check_escape ((new_flex_mono_vars, new_subst) as result) =
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
