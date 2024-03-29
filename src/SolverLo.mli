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
open SolverSig

(* This module offers the traditional, low-level presentation of a constraint
   solver: a definition of the syntax of constraints and a function [solve],
   which solves a constraint and annotates it, so as to publish information
   that can be exploited in the reconstruction phase. *)

module Make
  (X : TEVAR)
  (S : STRUCTURE)
  (O : OUTPUT with type 'a structure = 'a S.structure)
: sig

  (* The type [tevar] of term variables is provided by [X]. *)
  open X

  (* The type ['a structure] of shallow types is provided by [S]
     (and repeated by [O]). *)

  (* The types [tyvar] and [ty] of decoded type variables and decoded types
     are provided by the module [O]. *)
  open O

  (* ---------------------------------------------------------------------- *)

  (* The type [variable] describes the solver's type variables. *)
  type variable

  (* [fresh t] creates a fresh type variable, with optional structure [t]. *)
  val fresh: variable structure option -> variable

  (* [fresh_generic t] creates a fresh generic variable, with optional structure
     [t].  *)
  val fresh_generic: variable structure option -> variable

  (* The type [ischeme] describes the solver's type schemes. *)

  type ischeme

  (* The syntax of constraints is as follows. *)
  type rawco =

    (* Truth. *)
  | CTrue

    (* A conjunction of two constraints. *)
  | CConj of rawco * rawco

    (* An equation between two types, represented by two unifier variables,
       [v1] and [v2]. These variables must have been correctly bound via
       [CExist] or by [CLet]. *)
  | CEq of variable * variable

    (* An existentially quantified constraint, [exists v.C]. The variable [v]
       must have been created fresh. *)
  | CExist of variable * rawco

    (* An application of a constraint abstraction, [x w [witnesses?]]. The term
       variable refers to a constraint abstraction (in other words, a type
       scheme) that has been defined earlier via [CDef] or [CLet]. This
       abstraction is applied to the type variable [w] (in other words, [w] must
       be an instance of this type scheme). The argument [witnesses] must be a
       fresh write-once reference, which the solver will set to a list of
       witnesses. This list indicates how the type scheme was instantiated. *)
  | CInstance of tevar * variable * variable list WriteOnceRef.t

  (* A frozen term variable, [x w].  Variable [x] must be bound in the
     environment, either with [CDef] or [CLet].  [w] receives the type of [x]
     stored in the environment, including outer forall quantifiers. *)
  | CFrozen of tevar * variable

  (* A nontrivial type scheme definition, [let r [x, a, s?]* [v]* C1 in C2
     [vs?]], where [r] is let type (generalizing or monomorphising).  For each
     triple [x, a, s?] and corresponding [v] in the list, the term variable [x]
     is bound to the constraint abstraction [\v.C1], and the write-once
     reference [s?] is filled with a type scheme that represents a simplified
     form of this constraint abstraction. The environment is extended with all
     of these new bindings when [C2] is examined. The write-once reference [vs?]
     is filled with a list of type variables that must be universally quantified
     in the left-hand side of the [let] construct so as to be in scope when [C1]
     is decoded.

     Note that there's a one-to-one correspondence between [x, a, s?]* and [v]*.
     These lists could be merged into one but it would make operating on them
     more difficult. *)
  | CLet of clet_type
        * (tevar * variable * ischeme WriteOnceRef.t) list
        * variable list
        * rawco
        * rawco
        * variable list WriteOnceRef.t

  (* ---------------------------------------------------------------------- *)

  (* The function [solve] is parameterized by the flag [rectypes], which
     indicates whether recursive types are permitted. It expects a constraint
     and solves it; that is, either it fails with one of exceptions below, or it
     succeeds and fills the write-once references that are embedded in the
     syntax of the constraint. *)
  val solve: bool -> rawco -> unit

  (* Exceptions to communicate errors to high-level solver interface. *)
  exception Unbound of tevar
  exception NotMono of tevar * variable
  exception Unify of variable * variable
  exception UnifySkolem of variable * variable
  exception UnifyMono
  exception Cycle of variable
  exception MismatchedQuantifiers of variable list * variable list

  (* ---------------------------------------------------------------------- *)

  (* Support for decoding types. *)

  (* A variable is decoded to its unique integer identifier, which (via the
     function [O.variable]) is turned into an output type. *)

  val decode_variable: variable -> tyvar

  (* A type decoder is a function that transforms a unifier variable into an
     output type. *)
  type decoder = variable -> ty

  (* The function [new_decoder] returns a new decoder, which may have persistent
     state. *)
  val new_decoder: bool -> decoder

  (* The function [decode_scheme] decodes a type scheme. It is parameterized
     with a type decoder. *)
  val decode_scheme: decoder -> ischeme -> ty

end
