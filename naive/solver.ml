open Core

let handle_constraint state =
  let open Constraint in
  let open State in
  let stack = state.stack in
  let c = state.State.cnstrnt in
  assert (not (Constraint.is_true c));
  let push frame constr =
    Result.Ok (push_and_set_constraint state frame constr)
  in
  match c with
  (* S-ConjPush*)
  | Constraint.And (c1, c2) -> push (Stack.Conj c2) c1
  (* S-ExistsPush*)
  | Constraint.Exists (var, c) -> push (Stack.Exists [ var ]) c
  (* S-ForallPush*)
  | Constraint.Forall (var, c) -> push (Stack.Forall [ var ]) c
  (* S-DefPush*)
  | Constraint.Def (var, ty, c) ->
      let rigid_vars = State.rigid_vars state in
      let free_flexible = Types.free_flexible_variables ty rigid_vars in
      let flex_mono_vars = Set.union state.flex_mono_vars free_flexible in
      if
        not
          (Subst.can_demote state.subst rigid_vars flex_mono_vars free_flexible)
      then Result.Error Tc_errors.Def_cannot_monomorphise
      else
        let state = State.with_flex_mono_vars state flex_mono_vars in
        Result.Ok (push_and_set_constraint state (Stack.Def (var, ty)) c)
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
  | Constraint.Inst (var, ty) -> failwith "todo"
  | True -> assert false

let perform_step state =
  assert (not (State.is_final state));
  let st = state.stack in
  failwith "todo"

type solution = { mono_vars : State.tyvar_set; subst : Subst.t }

let rec solve state =
  if State.is_final state then
    Result.Ok { mono_vars = state.flex_mono_vars; subst = state.subst }
  else Result.bind (perform_step state) ~f:solve
