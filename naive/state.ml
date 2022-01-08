open Core

module Stack = struct
  type frame =
    | Forall of Tyvar.t list
    | Exists of Tyvar.t list
    | Conj of Constraint.t
    | Def of Term.tevar * Types.t
    | Let of Types.restriction * Term.tevar * Tyvar.t * Constraint.t
  [@@deriving sexp]

  type t = frame list [@@deriving sexp]
  (** Head of the list is top of stack (= innermost constraint) *)

  let is_existential_frame = function Exists _ -> true | _ -> false
  let is_forall_frame = function Forall _ -> true | _ -> false

  let push stack new_frame =
    match (new_frame, stack) with
    | Exists [], _ | Forall [], _ -> stack
    | Exists vars, Exists vars' :: stack' ->
        Exists (List.append vars vars') :: stack'
    | Forall vars, Forall vars' :: stack' ->
        Forall (List.append vars vars') :: stack'
    | _ -> new_frame :: stack

  let merge upper_stack lower_stack =
    List.fold_right ~f:(Fn.flip push) ~init:lower_stack upper_stack

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

type tyvar_set = Tyvar.Set.t [@@deriving sexp]

type unifier_state = { mono_flex_vars : tyvar_set; subst : Types.Subst.t }
[@@deriving sexp]

type t = {
  stack : Stack.t;
  unifier_state : unifier_state;
  cnstrnt : Constraint.t;
  (* cached information that can be obtained from earlier fields *)
  mutable rigid_vars : (Tyvar.set option[@sexp.opaque]);
  mutable tevar_env : (Types.t Tevar.Env.t option[@sexp.opaque]);
}
[@@deriving sexp]

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
    unifier_state =
      { mono_flex_vars = Tyvar.Set.empty; subst = Types.Subst.empty };
    cnstrnt;
    rigid_vars = None;
    tevar_env = None;
  }

let is_final s =
  if Constraint.is_true s.cnstrnt then
    match s.stack with
    | [ Exists _; Forall _ ] | [ Exists _ ] | [ Forall _ ] | [] -> true
    | _ -> false
  else false

let with_constraint state constr = { state with cnstrnt = constr }

let invalidate_caches state =
  let open Stack in
  function
  | Def _ -> { state with tevar_env = None }
  | Forall _ -> { state with rigid_vars = None }
  | _ -> state

let push_and_set_constraint state new_frame new_constraint =
  let new_stack = Stack.push state.stack new_frame in
  let new_state = { state with stack = new_stack; cnstrnt = new_constraint } in
  invalidate_caches new_state new_frame

let pop_and_set_constraint state constr =
  match state.stack with
  | frame :: stack ->
      let state = { state with stack; cnstrnt = constr } in
      invalidate_caches state frame
  | _ -> failwith "illegal argument"

let with_flex_mono_vars state mono_flex_vars =
  let unifier_state = { state.unifier_state with mono_flex_vars } in
  { state with unifier_state }

let with_subst state subst =
  let unifier_state = { state.unifier_state with subst } in
  { state with unifier_state }

let with_unifier_state state unifier_state = { state with unifier_state }

let with_stack state stack =
  { state with stack; tevar_env = None; rigid_vars = None }
