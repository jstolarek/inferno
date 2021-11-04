(******************************************************************************)
(*                                                                            *)
(*                                  Inferno                                   *)
(*                                                                            *)
(*                       François Pottier, Inria Paris                        *)
(*                                                                            *)
(*  Copyright Inria. All rights reserved. This file is distributed under the  *)
(*  terms of the MIT License, as described in the file LICENSE.               *)
(*                                                                            *)
(******************************************************************************)

(* This file defines some of the input signatures of the functor [Solver.Make]. *)

(* -------------------------------------------------------------------------- *)

type clet_type =
  | CLetMono
  | CLetGen

(* The type of term variables is described to the solver as follows. *)

(* This signature is isomorphic to [Map.OrderedType] in OCaml's standard
   library. *)

module type TEVAR = sig

  (* The type of term variables. *)
  type tevar

  (* A total ordering. *)
  val compare: tevar -> tevar -> int

  val print_tevar : tevar -> PPrint.document

end

(* -------------------------------------------------------------------------- *)

(* The structure of types *after decoding* is described to the solver as
   follows. *)

module type OUTPUT = sig

  (* The solver represents type variables via unique integer identifiers. *)
  type tyvar = int

  module TyVarMap : Map.S with type key = tyvar

  (* The solver works with first-order types whose structure is defined by
     the type ['a structure], as in the signature [Unifier.STRUCTURE]. *)
  type 'a structure

  (* The solver constructs decoded types of type [ty], and never deconstructs
     them. So, the operations that the solver requires are constructors for
     the type [ty]. *)
  type ty

  (* [variable v] is a representation of the type variable [v] as a decoded
     type. In other words, [variable] is an injection of [tyvar] into [ty]. *)
  val variable: tyvar -> ty

  (* [forall] quantifies a decoded type. *)
  val forall: tyvar list -> ty -> ty

  (* Splits a quantfied type into quantifiers and body. *)
  val to_scheme : ty -> tyvar list * ty

  (* [structure t] turns [t], an application of type constructor to children
     of type [ty], into something of type [ty]. In other words, when [variable]
     and [structure] are combined, we see that [ty] must contain the fixed point
     of the functor [\X. tyvar + t X]. *)
  val structure: ty structure -> ty

  (* A worker function required by SolverHi.annotation_to_variable.  Used for
     converting type signatures in the source code to unification variables with
     a structure.  [to_variable] takes two functions for generating fresh
     unification variables.  First one always generates unregistered variables.
     Second one generates generic or unregistered variables, depending on
     whether the variables are under a quantifier or no.  See comments in
     SolverHi.annotation_to_variable for more details. *)
  val to_variable : ('a structure -> 'a) -> ('a structure -> 'a) -> (ty -> 'a)
                 -> 'a TyVarMap.t -> ty -> 'a

  (* If [v] is a type variable and [t] is a type, then [mu v t] is a
     representation of the recursive type [mu v.t]. This function is used in
     one of two situations: 1- the occurs check is disabled, so the solver
     produces recursive types; or 2- the occurs check is enabled, but the
     types carried by the exceptions [Unify] and [Cycle] can still be cyclic,
     and one may wish to decode and display them. *)
  val mu: tyvar -> ty -> ty

end
