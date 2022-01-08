open Core

module Make (U : Unification.Unifier) = struct
  let handle_constraint state =
    let open Constraint in
    let open State in
    (* let stack = state.stack in *)
    let c = state.State.cnstrnt in
    assert (not (Constraint.is_true c));
    let push frame constr =
      Result.Ok (push_and_set_constraint state frame constr)
    in
    let push_extend_unifier_state frame constr new_var =
      let state = push_and_set_constraint state frame constr in
      let subst =
        Types.Subst.set state.unifier_state.subst new_var (TyVar new_var)
      in
      let state = State.with_subst state subst in
      Result.Ok state
    in
    let with_constraint = Fn.flip State.with_constraint in
    let with_unifier_state mono_flex_vars subst state =
      State.with_unifier_state state { mono_flex_vars; subst }
    in
    match c with
    (* S-ConjPush*)
    | Constraint.And (c1, c2) -> push (Stack.Conj c2) c1
    (* S-ExistsPush*)
    | Constraint.Exists (var, c) ->
        push_extend_unifier_state (Stack.Exists [ var ]) c var
    (* S-ForallPush*)
    | Constraint.Forall (var, c) -> push (Stack.Forall [ var ]) c
    (* S-DefPush*)
    | Constraint.Def (var, ty, c) ->
        let rigid_vars = State.rigid_vars state in
        let free_flexible = Types.ftv ty rigid_vars in

        let ty_substed = Types.Subst.apply state.unifier_state.subst ty in
        let free_flexible_substed = Types.ftv ty_substed rigid_vars in

        let flex_mono_vars =
          Set.union state.unifier_state.mono_flex_vars free_flexible_substed
        in
        let can_demote_all_ftv =
          Types.Subst.can_demote state.unifier_state.subst rigid_vars
            flex_mono_vars free_flexible
        in
        if can_demote_all_ftv then
          let state = State.with_flex_mono_vars state flex_mono_vars in
          Result.Ok (push_and_set_constraint state (Stack.Def (var, ty)) c)
        else Result.Error Tc_errors.Cannot_monomorphise
    (* S-LetPush *)
    | Constraint.Let (restr, var, tyvar, c1, c2) ->
        push_extend_unifier_state (Stack.Let (restr, var, tyvar, c2)) c1 tyvar
    (* S-Eq *)
    | Constraint.Equiv (ty1, ty2) ->
        (* let open Unifier in *)
        let theta = state.unifier_state.subst in

        let rigid_vars = State.rigid_vars state in
        let unifier_res =
          U.unify ~rigid_vars state.unifier_state
            (Types.Subst.apply theta ty1)
            (Types.Subst.apply theta ty2)
        in
        Result.bind unifier_res ~f:(fun Unification.{ mono_flex_vars; subst } ->
            (* See comment in unifier, no neeed to compose (as the paper would) *)
            let state =
              with_unifier_state mono_flex_vars subst state
              |> with_constraint Constraint.True
            in
            Result.Ok state)
    (* S-Freeze *)
    | Constraint.Freeze (var, ty) ->
        let gamma = State.tevar_env state in
        let var_ty = Tevar.Env.get gamma var in
        Result.Ok (State.with_constraint state (Constraint.Equiv (var_ty, ty)))
    (* S-Inst *)
    | Constraint.Inst (var, ty) ->
        let gamma = State.tevar_env state in
        let var_ty = Tevar.Env.get gamma var in
        let fresh_quantifiers, freshened_body =
          Types.freshen_quantifiers var_ty
        in
        let equiv = Constraint.Equiv (freshened_body, ty) in
        let constr =
          List.fold_right
            ~f:(fun q c -> Constraint.Exists (q, c))
            ~init:equiv fresh_quantifiers
        in
        Result.Ok (State.with_constraint state constr)
    | True -> assert false

  let split vars subst =
    let vars_set = Tyvar.Set.of_list vars in
    let outer_ftvs =
      Map.fold
        ~f:(fun ~key ~data ftvs ->
          if Set.mem vars_set key then ftvs
          else
            let new_ftvs = Types.ftv data Tyvar.Set.empty in
            Tyvar.Set.union ftvs new_ftvs)
        ~init:Tyvar.Set.empty subst
    in
    let not_referenced_by_outer var = not (Set.mem outer_ftvs var) in
    List.partition_tf ~f:not_referenced_by_outer vars

  let handle_stack state =
    let stack = state.State.stack in
    let pop_and_set c = Result.Ok (State.pop_and_set_constraint state c) in
    let with_stack = Fn.flip State.with_stack in
    let with_constraint = Fn.flip State.with_constraint in
    let with_unifier_state mono_flex_vars subst state =
      State.with_unifier_state state { mono_flex_vars; subst }
    in

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
              Types.Subst.range_contains state.unifier_state.subst
                Tyvar.Set.empty var)
            vars
        in
        if any_escapes then Result.Error Tc_errors.Quantifier_escape
        else pop_and_set Constraint.True
    (* S-Let[Poly|Mono]Pop*)
    | _, Exists vars :: Let (restr, tevar, tyvar, c2) :: stack'
    | vars, Let (restr, tevar, tyvar, c2) :: stack' ->
        let non_referenced, referenced =
          split (tyvar :: vars) state.unifier_state.subst
        in
        let non_referenced = Tyvar.Set.of_list non_referenced in

        let c1_ty = Types.Subst.apply state.unifier_state.subst (TyVar tyvar) in
        let c1_ty_fftv = Types.ftv_ordered c1_ty (State.rigid_vars state) in
        let generalizable =
          List.filter c1_ty_fftv ~f:(Set.mem non_referenced)
        in

        let to_remove, to_quantify_ex, var_type =
          match restr with
          | Mono ->
              ( Set.diff non_referenced (Tyvar.Set.of_list generalizable),
                List.append generalizable referenced,
                c1_ty )
          | Poly ->
              (non_referenced, referenced, Types.forall generalizable c1_ty)
        in

        let mono_vars = Set.diff state.unifier_state.mono_flex_vars to_remove in
        let subst =
          Set.fold ~f:Map.remove ~init:state.unifier_state.subst to_remove
        in

        let stack = State.Stack.merge [ Exists to_quantify_ex ] stack' in
        let state =
          with_stack stack state
          |> with_unifier_state mono_vars subst
          |> with_constraint (Constraint.Def (tevar, var_type, c2))
        in
        Result.Ok state
    | _, Exists _ :: Exists _ :: _ -> failwith "ill-formed stack"
    (* S-ExistsLower *)
    | _, Exists vars :: lower_frame :: stack' ->
        let to_remove, referenced_vars = split vars state.unifier_state.subst in
        let to_remove = Tyvar.Set.of_list to_remove in

        let mono_vars = Set.diff state.unifier_state.mono_flex_vars to_remove in
        let subst =
          Set.fold ~f:Map.remove ~init:state.unifier_state.subst to_remove
        in

        let stack =
          State.Stack.merge [ lower_frame; Exists referenced_vars ] stack'
        in
        let state =
          with_stack stack state |> with_unifier_state mono_vars subst
        in
        Result.Ok state
    | _, [ Exists _ ] | _, [] -> failwith "state is already final"

  let perform_step state =
    Shared.Logging.log_sexp "Performing step on state:\n%s\n"
      (State.sexp_of_t state);
    assert (not (State.is_final state));
    (* let st = state.stack in *)
    let constr = state.cnstrnt in
    if Constraint.is_true constr then handle_stack state
    else handle_constraint state

  let rec solve state =
    if State.is_final state then (
      Shared.Logging.log_sexp "Final state:\n%s\n" (State.sexp_of_t state);
      Result.Ok state.unifier_state)
    else Result.bind (perform_step state) ~f:solve

  module Unifier = U
end

type solution = State.unifier_state

let state_of_constraint = State.empty

module type Solver = sig
  module Unifier : Unification.Unifier

  val solve : State.t -> (solution, Tc_errors.errors) Result.t
end

module Ordered : Solver = Make (Unification.Ordered)
module Unordered : Solver = Make (Unification.Unordered)
