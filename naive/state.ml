open Core

module Stack = struct
  type frame =
    | Forall of Tyvar.t list
    | Exists of Tyvar.t list
    | Conj of Constraint.t
    | Def of Term.tevar * Types.t
    | Let of Types.restriction * Term.tevar * Tyvar.t * Constraint.t

  type t = frame list
  (** Head of the list is top of stack (= innermost constraint) *)

  let is_existential_frame = function Exists _ -> true | _ -> false
  let is_forall_frame = function Forall _ -> true | _ -> false

  let push stack new_frame =
    match (new_frame, stack) with
    | Exists vars, Exists vars' :: stack' ->
        Exists (List.append vars vars') :: stack'
    | Forall vars, Forall vars' :: stack' ->
        Forall (List.append vars vars') :: stack'
    | _ -> new_frame :: stack

  module Invariants = struct
    exception Bad_stack of string

    let rec quantifiers_compacted = function
      | f :: (f' :: fs as tail) ->
          if is_existential_frame f && is_existential_frame f' then
            raise (Bad_stack "neighboring existential frames in stack!")
          else if is_forall_frame f && is_forall_frame f' then
            raise (Bad_stack "neighboring forall frames in stack!")
          else quantifiers_compacted tail
      | _ -> ()
  end
end

type tyvar_set = Tyvar.Set.t

type t = {
  stack : Stack.t;
  flex_mono_vars : tyvar_set;
  subst : Subst.t;
  cnstrnt : Constraint.t;
  (* cached information that can be obtained from earlier fields *)
  mutable rigid_vars : Tyvar.set option;
  mutable tevar_env : Types.t Tevar.Env.t option;
}

let rigid_vars state =
  match state.rigid_vars with
  | Some rv -> rv
  | None ->
      let rec collect = function
        | [] -> []
        | Stack.Forall rvs :: stack' -> List.append rvs (collect stack')
        | _ :: stack' -> collect stack'
      in
      let vars = collect state.stack |> Tyvar.set_of_list in
      state.rigid_vars <- Some vars;
      vars

let tevar_env state =
  match state.tevar_env with
  | Some env -> env
  | None ->
      let rec collect = function
        | [] -> Tevar.Env.empty
        | Stack.Def (x, ty) :: stack' -> Tevar.Env.set (collect stack') x ty
        | f :: stack' -> collect stack'
      in
      let env = collect state.stack in
      state.tevar_env <- Some env;
      env

let empty cnstrnt =
  {
    stack = [];
    flex_mono_vars = Tyvar.Set.empty;
    subst = Subst.empty;
    cnstrnt;
    rigid_vars = None;
    tevar_env = None;
  }

let is_final s =
  match s.stack with
  | [ Exists _; Forall _ ] | [ Exists _ ] | [ Forall _ ] | [] -> true
  | _ -> false

let with_constraint state constr = { state with cnstrnt = constr }

let push_and_set_constraint state new_frame new_constraint =
  let new_stack = Stack.push state.stack new_frame in
  let new_state = { state with stack = new_stack; cnstrnt = new_constraint } in
  match new_frame with
  | Def _ -> { new_state with tevar_env = None }
  | Forall _ -> { new_state with rigid_vars = None }
  | _ -> new_state

let with_flex_mono_vars state flex_mono_vars = { state with flex_mono_vars }

let with_unifier_state state flex_mono_vars subst =
  { state with flex_mono_vars; subst }
