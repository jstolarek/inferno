(******************************************************************************)
(*                                                                            *)
(*                             Frozen Inferno                                 *)
(*                                                                            *)
(*                    Jan Stolarek, University of Edinburgh                   *)
(*                                                                            *)
(*  Derived from Inferno code created by François Pottier, Inria Paris.       *)
(*                                                                            *)
(*  Copyright University of Edinburgh and Inria. All rights reserved. This    *)
(*  file is distributed under the terms of the MIT License, as described in   *)
(*  the file LICENSE.                                                         *)
(*                                                                            *)
(******************************************************************************)

open UnifierSig

(* This module takes care of creating and instantiating quantified types. It is
   parameterized over the type structure and over a unifier. *)

module Make (S : STRUCTURE) (U : UNIFIER with type 'a structure = 'a S.structure) : sig

  (* A variable is just a unifier variable. *)

  open U

  (* The literature defines a type scheme as a type (the ``body''), placed in
     the scope of a list of universal quantifiers. Here, the quantifiers are
     just variables (which definitely carry no structure), while the body is
     just a variable too (which possibly/probably carries some structure).  One
     may think of a type scheme as a fragment of the unification graph, part of
     which is marked ``generic'' and is meant to be copied when the type scheme
     is instantiated, part of which is not (the free variables, so to speak).

     In the presence of first-class polymorphism type schemes are no longer a
     distinguished syntactic construct in the source language: quantified types
     are now first-class citizens.  However, we use the type scheme definition
     internally since it is a convenient data representation within the
     solver. *)

  type scheme

  (* Type scheme accessors. *)
  val body            : scheme -> variable
  val quantifiers     : scheme -> variable list
  val has_quantifiers : scheme -> bool

  (* We maintain a piece of private state, which can be abstractly thought of
     as a representation of a constraint context of the following form:

     cctx := hole
     | cctx[let exists vs. hole in ...]

     That is, a context is either 1- just a hole; or 2- a hole, nested in a
     [CExist] construct, nested in the left-hand side of a [CLet] construct,
     itself nested in another context. (The variables [vs] are type variables;
     [...] stands for a constraint, which is irrelevant here.) In short, the
     state keeps track of how many [CLet] constructs have been entered (in the
     left-hand side) and keeps track of the variables that are existentially
     bound at each such construct.

     The state of the unifier is logically placed in this hole. Let us write
     [U] for a unifier state (that is, a unification constraint in solved
     form). When a unifier state [U] and a state of this module [cctx] are
     combined, the constraint [U] is logically placed in the hole of the
     context [cctx], i.e., the meaning of the combination is [cctx[U]].

     This state is mutable. *)

  type state

  (* A debugging utility. *)

  val show_state: string -> state -> unit

  (* The initial state corresponds to the empty constraint context. *)

  val init : unit -> state

  (* We manage the rank information carried by every unification variable. The
     details are abstract. Suffice it to say that the user is expected to set
     the rank of a freshly created variable to [no_rank]. The user is also
     expected to register every freshly created variable with us, using the
     function [register]. This updates the state (as well as the variable's
     rank) by recording that this variable is bound at the most recent [CLet]
     construct. [register_signatures] takes an unregistered variable with a
     structure corresponding to a source-level type signature and registers that
     variable and all unregistered variables inside the structure.  (Note:
     [register] and [register_signatures] can be called only if the current
     context is nonempty, i.e. the current [enter]/[exit] balance is at least
     one.) *)

  val no_rank            : int
  val register           : state -> variable -> unit
  val register_signatures: state -> variable -> unit

  (* Removes variables from the pool.  FIXME: feels like a hack, see #41 *)
  val remove_from_pool : state -> variable list -> unit

  (* A smart constructor for converting a variable into a type scheme.
     Variable's structure is traversed recursively in search for nested foralls.
     All quantifiers from these foralls are then turned into scheme quantifiers.
     The remaining variable is then turned into body of the scheme *)
  val scheme : variable -> scheme

  (* Flattens nested foralls.  Works exactly the same as [scheme] above but
     takes an argument that is a scheme rather than a variable.  *)
  val flatten_outer_foralls : scheme -> scheme

  (* Return all unbound type variables (no structure) in a scheme. *)
  val unbound_tyvars                : scheme -> variable list

  (* Test that all generic variables in a type scheme are bound. *)
  val all_generic_vars_bound        : scheme -> bool

  (* Returns a list of generic top-level (= not inside a forall) variables, both
     with and without structure. *)
  val toplevel_generic_variables    : variable -> variable list

  (* Sets all unbound generic variables in a scheme to have a given rank. *)
  val set_unbound_generic_vars_rank : scheme -> int -> unit

  exception MismatchedQuantifiers of variable list * variable list

  (* Ensures that two lists of variables have the same length and contain same
     variables in the same order.  Throws an exception if that is not the
     case. *)
  val assert_variables_equal : variable list -> variable list -> unit

  (* [enter] updates the current state by pushing a new [CLet] construct. The
     the hole is replaced with [let exists vs. hole in ...], where the list
     [vs] of young variables is empty. This function is used when entering the
     left-hand side of a [let] construct. *)

  val enter: state -> unit

  (* [exit] updates the current state by popping a [CLet] construct. This
     involves an inspection of the unifier state. The most recent [CLet]
     construct, combined with the unifier state, takes the form [let exist
     vs.U in ...]. The state [U] is inspected. (An occurs check is optionally
     performed at this point, so [U.Cycle] may be raised.) This allows some of
     the variables in the list [vs] to be deemed ``non-generalizable''; their
     existential quantifiers are hoisted out. The remaining variables in [vs]
     are deemed ``generalizable''. The user may provide a list of roots
     (variables) that she is interested in; each of these roots in turned into
     a type scheme.

     In summary, if [rectypes] is a Boolean flag that indicates whether
     recursive types should be allowed, if [state] is the current state, if
     [roots] is a list of roots of interest, then, after the call:

     let vs, schemes = exit rectypes state roots in
     ...

     [state] is updated, and [vs] is a list of the structureless generalizable
     variables, and [schemes] is a list of type schemes, in correspondence
     with the list [roots]. For each such root and scheme, the scheme's body
     is this root, and the scheme's quantifiers are the structureless
     generalizable variables that are reachable from this root. Hence, the
     scheme's quantifiers form a subset of [vs]. (Not a sublist. A subset.) *)

  (* The complexity of this operation is linear in the size of the young
     generation (i.e., the number of variables that were created since [enter]
     was last called) plus the length of the list [roots] plus the current
     nesting depth of [CLet] constructs (usually considered a constant). *)

  val exit: bool -> state -> variable list -> variable list * scheme list

  (* [instantiate] takes a fresh copy of a type scheme. The generic variables
     of the type scheme are replaced with freshly created variables, which are
     automatically registered (hence, the current state is updated). The function
     returns the (fresh) instances of the scheme's quantifiers (in the same order
     as the list returned by the function [quantifiers]) as well as the instance
     of the body. *)

  (* The complexity of this operation is linear in the size of the generic part
     of the type scheme. *)

  val instantiate: state -> scheme -> variable list * variable

end
