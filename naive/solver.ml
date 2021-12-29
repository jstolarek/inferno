open Core

let handle_constraint state =
  let open Constraint in
  let open State in
  (* let stack = state.stack in *)
  let c = state.State.cnstrnt in
  assert (not (Constraint.is_true c));
  let push frame constr =
    Result.Ok (push_and_set_constraint state frame constr)
  in
  match c with
  (* S-ConjPush*)
  | Constraint.And (c1, c2) -> push (Stack.Conj c2) c1
  (* S-ExistsPush*)
  | Constraint.Exists (var, c) ->
      let state = push_and_set_constraint state (Stack.Exists [ var ]) c in
      let subst = Types.Subst.set state.subst var (TyVar var) in
      let state = State.with_unifier_state state state.flex_mono_vars subst in
      Result.Ok state
  (* S-ForallPush*)
  | Constraint.Forall (var, c) -> push (Stack.Forall [ var ]) c
  (* S-DefPush*)
  | Constraint.Def (var, ty, c) ->
      let rigid_vars = State.rigid_vars state in
      let free_flexible = Types.free_flexible_variables ty rigid_vars in
      let flex_mono_vars = Set.union state.flex_mono_vars free_flexible in
      let can_demote_all_ftv =
        Types.Subst.can_demote state.subst rigid_vars flex_mono_vars
          free_flexible
      in
      if can_demote_all_ftv then
        let state = State.with_flex_mono_vars state flex_mono_vars in
        Result.Ok (push_and_set_constraint state (Stack.Def (var, ty)) c)
      else Result.Error Tc_errors.Def_cannot_monomorphise
  (* S-LetPush *)
  | Constraint.Let (restr, var, tyvar, c1, c2) ->
      push (Stack.Let (restr, var, tyvar, c2)) c1
  (* S-Eq *)
  | Constraint.Equiv (ty1, ty2) ->
      let theta = state.subst in
      let unifier_res =
        Unifier.unify (State.rigid_vars state) state.flex_mono_vars theta
          (Types.Subst.apply theta ty1)
          (Types.Subst.apply theta ty2)
      in
      Result.bind unifier_res ~f:(fun (new_flex_mono_vars, new_subst) ->
          Result.Ok
            (State.with_unifier_state state new_flex_mono_vars new_subst))
  (* S-Freeze *)
  | Constraint.Freeze (var, ty) ->
      let gamma = State.tevar_env state in
      let var_ty = Tevar.Env.get gamma var in
      Result.Ok (State.with_constraint state (Constraint.Equiv (var_ty, ty)))
  (* S-Inst *)
  | Constraint.Inst (var, ty) ->
      let fresh_quantifiers, freshened_body = Types.freshen_quantifiers ty in
      let equiv = Constraint.Equiv (freshened_body, ty) in
      let constr =
        List.fold_right
          ~f:(fun q c -> Constraint.Exists (q, c))
          ~init:equiv fresh_quantifiers
      in
      Result.Ok (State.with_constraint state constr)
  | True -> assert false

let handle_stack state =
  let stack = state.State.stack in
  let pop_and_set c = Result.Ok (State.pop_and_set_constraint state c) in
  let handle_let_frame vars restr tevar tyvar c2 = failwith "todo" in
  match ([], stack) with
  (* S-ConjPop *)
  | _, Conj c2 :: _ -> pop_and_set c2
  (* S-DefPop *)
  | _, Def _ :: _ -> pop_and_set Constraint.True
  (* S-ForallPop *)
  | _, Forall vars :: _ ->
      let any_escapes =
        (* TODO: change range_contains to just take "ignore" param, instead of "rigid vars" *)
        List.exists
          ~f:(fun var ->
            Types.Subst.range_contains state.subst Tyvar.Set.empty var)
          vars
      in
      if any_escapes then Result.Error Tc_errors.Unification_quantifier_escape
      else pop_and_set Constraint.True
  (* S-Let[Poly|Mono]Pop*)
  | _, Exists vars :: Let (restr, tevar, tyvar, c2) :: _
  | vars, Let (restr, tevar, tyvar, c2) :: _ ->
      handle_let_frame vars restr tevar tyvar c2
  | _, Exists _ :: Exists _ :: _ -> failwith "ill-formed stack"
  (* S-ExistsLower *)
  | _, Exists _vars :: _ -> failwith "todo"
  | _, [] -> failwith "illegal stack"

let perform_step state =
  assert (not (State.is_final state));
  (* let st = state.stack in *)
  let constr = state.cnstrnt in
  if Constraint.is_true constr then handle_stack state
  else handle_constraint state

type solution = { mono_vars : State.tyvar_set; subst : Types.Subst.t }

let rec solve state =
  if State.is_final state then
    Result.Ok { mono_vars = state.flex_mono_vars; subst = state.subst }
  else Result.bind (perform_step state) ~f:solve
