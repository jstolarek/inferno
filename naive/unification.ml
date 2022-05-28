open Core

let ( let* ) v f = Result.bind v ~f

(**
    As a minor diversion from the paper, we get the initial substitution
    [subst] and return an updated version of it, instead of returning something
    that needs to be composed with the initial substitution.
    The first return value (if Ok) indicates whether the types were already
    equal.
    [dummy_vars] contains flexible variables that we may unify with other dummy
    vars without considering the types not equal

 *)
let rec unify_and_check_equal ~ordered ~dummy_vars rigid_vars mono_flex_vars
    subst ty1 ty2 =
  let open Types in
  let unify = unify_and_check_equal ~ordered ~dummy_vars in
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
          (* Actual unification. update all mappings, including the a -> a one *)
          let singleton = Types.Subst.singleton a other_ty in
          let subst = Map.map ~f:(Types.Subst.apply singleton) subst in

          let is_dummy_var = function
            | TyVar c -> Set.mem dummy_vars c
            | _ -> false
          in
          let types_equal =
            (* In unordered mode, unifying two dummy vars lets us still consider
               the types equal *)
            (not ordered) && Set.mem dummy_vars a && is_dummy_var other_ty
          in

          let mono_flex_vars =
            if Set.mem mono_flex_vars a then
              Tyvar.Set.union mono_flex_vars (free_flex ())
            else mono_flex_vars
          in
          if
            Set.mem mono_flex_vars a
            && not (Types.is_monomorphic other_ty rigid_vars mono_flex_vars)
          then Result.Error Tc_errors.Cannot_monomorphise
          else Result.Ok (types_equal, mono_flex_vars, subst))
  | TyProduct (tya1, tya2), TyProduct (tyb1, tyb2)
  | TyArrow (tya1, tya2), TyArrow (tyb1, tyb2) ->
      unify_list [ tya1; tya2 ] [ tyb1; tyb2 ]
  | TyConstrApp (constr1, args1), TyConstrApp (constr2, args2)
    when Shared.Types.Type_constr.equal constr1 constr2 ->
      unify_list args1 args2
  | TyForall (a, ty'), other_ty | other_ty, TyForall (a, ty') ->
      if ordered then
        unify_forall_ordered ~dummy_vars rigid_vars mono_flex_vars subst
          (a, ty') other_ty
      else
        unify_forall_unordered ~dummy_vars rigid_vars mono_flex_vars subst ty1
          ty2
  | TyMu (_q1, _ty1), _ | _, TyMu (_q1, _ty1) ->
      failwith "not implemented at the moment"
  | _ -> Result.Error Tc_errors.Unification_clash_failure

and check_escape rigid_vars to_check
    ((_equal, _new_flex_mono_vars, new_subst) as result) =
  let escapes =
    List.exists to_check ~f:(Types.Subst.range_contains new_subst rigid_vars)
  in
  if escapes then Result.Error Tc_errors.Quantifier_escape else Result.Ok result

and unify_forall_ordered ~dummy_vars rigid_vars mono_flex_vars subst (q1, ty1)
    other_ty =
  let open Types in
  match other_ty with
  | TyForall (q2, ty2) ->
      let fresh = Tyvar.fresh_tyvar () in
      let subst1 = Types.Subst.singleton q1 (TyVar fresh) in
      let subst2 = Types.Subst.singleton q2 (TyVar fresh) in
      let ty1 = Types.Subst.apply subst1 ty1 in
      let ty2 = Types.Subst.apply subst2 ty2 in

      let new_rigid_vars = Set.add rigid_vars fresh in
      Result.bind
        (unify_and_check_equal ~ordered:true ~dummy_vars new_rigid_vars
           mono_flex_vars subst ty1 ty2)
        ~f:(check_escape rigid_vars [ fresh ])
  | _ -> Result.Error Tc_errors.Unification_clash_failure

and unify_forall_unordered ~dummy_vars rigid_vars mono_flex_vars subst ty1 ty2 =
  (* We unify two types ∀ qs1. H1 and ∀ qs2. H2, where H1 and H2 are guarded types.
     We replace qs and qs' with fresh flexible dummy variables in H and H',
     resp. We then unify the resulting H and H' and test that the resulting
     substitution on qs1 and qs2 is injective.
  *)
  let qs1, h1 = Types.freshen_quantifiers ty1 in
  let qs2, h2 = Types.freshen_quantifiers ty2 in
  let all_qs = List.append qs1 qs2 in
  let add_identity_mapping map tyvar =
    Map.set map ~key:tyvar ~data:(Types.TyVar tyvar)
  in
  let subst = List.fold ~f:add_identity_mapping ~init:subst all_qs in
  let dummy_vars =
    Set.union dummy_vars (Tyvar.Set.of_list qs1)
    |> Set.union (Tyvar.Set.of_list qs2)
  in
  let* types_equal, mono_vars, full_subst =
    unify_and_check_equal ~ordered:false ~dummy_vars rigid_vars mono_flex_vars
      subst h1 h2
  in
  let subst = List.fold ~f:Map.remove ~init:full_subst all_qs in
  let* result =
    check_escape rigid_vars all_qs (types_equal, mono_vars, subst)
  in
  let initial_counts =
    List.fold all_qs
      ~init:(Map.empty (module Int))
      ~f:(fun map var -> Map.set map ~key:var ~data:0)
  in
  let check_injective qs =
    let check counts var =
      match Map.find_exn full_subst var with
      | Types.TyVar v -> (
          match Map.find counts v with
          | Some count ->
              if count >= 1 then
                Result.Error Tc_errors.Unification_clash_failure
              else Result.Ok (Map.set counts ~key:v ~data:(count + 1))
          | None -> Result.Error Tc_errors.Unification_clash_failure)
      | _ -> Result.Error Tc_errors.Unification_clash_failure
    in
    List.fold_result qs ~init:initial_counts ~f:check
  in
  let* _ = check_injective qs1 in
  let* _ = check_injective qs2 in
  Result.Ok result

type unifier_state = State.unifier_state = {
  mono_flex_vars : Tyvar.Set.t;
  subst : Types.Subst.t;
}

let mk_equal ~ordered ty1 ty2 =
  let empty = Tyvar.Set.empty in
  let res =
    unify_and_check_equal ~ordered ~dummy_vars:empty empty empty
      Types.Subst.empty ty1 ty2
  in
  match res with Result.Ok (equal, _, _) -> equal | Result.Error _ -> false

let mk_unify ~ordered ~rigid_vars:rv u_state ty1 ty2 =
  let empty = Tyvar.Set.empty in
  Result.map
    ~f:(fun (_equal, mono_flex_vars, subst) -> { mono_flex_vars; subst })
    (unify_and_check_equal ~ordered ~dummy_vars:empty rv u_state.mono_flex_vars
       u_state.subst ty1 ty2)

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
