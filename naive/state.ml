open Core
open Shared

module Stack = struct
  type frame =
    | Forall of Tyvar.t
    | Exists of Tyvar.t
    | Conj of Constraint.t
    | Def of Ml.tevar
    | Let of Ml.tevar * Tyvar.t * Constraint.t

  type t = frame list
end

type tyvar_set = (Tyvar.t, Tyvar.comparator_witness) Set.t

type t = {
  stack : Stack.t;
  mono_vars : tyvar_set;
  subst : Subst.t;
  constr : Constraint.t;
}
