open Core

type failure = Clash_failure | Occurs_failure | Quantifier_escape

(** This assumes that [subst] has already been applied to [ty1] and [ty2] *)
let rec unify rigid_vars mono_flex_vars subst ty1 ty2 =
  let open Types in
  let try_unify state_res ty1 ty2 =
    Result.bind state_res ~f:(fun (flex, subst) ->
        unify rigid_vars flex subst ty1 ty2)
  in
  let unify_constr_args args1 args2 =
    List.fold2_exn ~f:try_unify
      ~init:(Result.Ok (mono_flex_vars, subst))
      args1 args2
  in
  match (ty1, ty2) with
  | TyVar a, other_ty | other_ty, TyVar a ->
      if Tyvar.Set.mem rigid_vars a then
        match other_ty with
        | TyVar b when Tyvar.equal a b -> Result.Ok (mono_flex_vars, subst)
        | _ -> Result.Error Tc_errors.Unification_clash_failure
      else
        (* TODO: if ty2 is not equal to ty2, then do occurs check *)
        let subst = Types.Subst.set subst a other_ty in
        let mono_flex_vars =
          if Tyvar.Set.mem mono_flex_vars a then
            let to_demote = Types.free_flexible_variables ty2 rigid_vars in
            Tyvar.Set.union mono_flex_vars to_demote
          else mono_flex_vars
        in
        Result.Ok (mono_flex_vars, subst)
  | TyProduct (tya1, tya2), TyProduct (tyb1, tyb2)
  | TyArrow (tya1, tya2), TyArrow (tyb1, tyb2) ->
      unify_constr_args [ tya1; tya2 ] [ tyb1; tyb2 ]
  | TyConstrApp (constr1, args1), TyConstrApp (constr2, args2)
    when Shared.Types.Type_constr.equal constr1 constr2 ->
      unify_constr_args args1 args2
  | TyForall (q1, ty1), TyForall (q2, ty2) ->
      let fresh = Tyvar.fresh_tyvar () in
      let subst1 = Types.Subst.singleton q1 (TyVar fresh) in
      let subst2 = Types.Subst.singleton q2 (TyVar fresh) in
      let ty1 = Types.Subst.apply subst1 ty1 in
      let ty2 = Types.Subst.apply subst1 ty2 in
      (* TODO: check quantifier escape *)
      let check_escape (new_flex_mono_vars, new_subst) =
        failwith "implement me"
      in
      Result.bind (unify rigid_vars mono_flex_vars subst ty1 ty2) check_escape
  | TyMu (_q1, _ty1), TyForall (_q2, _ty2) ->
      failwith "not implemented at the moment"
  | _ -> Result.Error Tc_errors.Unification_clash_failure
