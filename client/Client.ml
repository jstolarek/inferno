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

(* This sample client performs type inference for a fragment of ML and translates
   it down to a fragment of System F. *)

(* -------------------------------------------------------------------------- *)

(* The unifier will use the following type structure. *)

module S = struct

  type 'a structure =
    | TyArrow of 'a * 'a
    | TyProduct of 'a * 'a
    | TyForall of 'a list * 'a
    (* Arbitrary ground types to allow writing concrete examples *)
    | TyInt
    | TyBool

  let forall qs t =
    TyForall (qs, t)

  let maybeForall t = match t with
    | TyForall (qs, t) -> Some (qs, t)
    | _                -> None

  let isForall = function
    | TyForall _ -> true
    | _          -> false

  let map f t =
    match t with
    | TyArrow (t1, t2) ->
        let t1 = f t1 in
        let t2 = f t2 in
        TyArrow (t1, t2)
    | TyProduct (t1, t2) ->
        let t1 = f t1 in
        let t2 = f t2 in
        TyProduct (t1, t2)
    | TyForall (qs, t) ->
        let qs = List.map f qs in
        let t  = f t in
        TyForall (qs, t)
    | TyInt -> TyInt
    | TyBool -> TyBool

  let fold f t accu =
    match t with
    | TyArrow (t1, t2)
    | TyProduct (t1, t2) ->
        let accu = f t1 accu in
        let accu = f t2 accu in
        accu
    | TyForall (qs, t) ->
        let accu = List.fold_left (fun accu q -> f q accu) accu qs in
        f t accu
    | TyInt -> accu
    | TyBool -> accu

  let iter f t =
    let _ = map f t in
    ()

  exception Iter2

  let iter2 f t u =
    match t, u with
    | TyArrow (t1, t2), TyArrow (u1, u2)
    | TyProduct (t1, t2), TyProduct (u1, u2) ->
        f t1 u1;
        f t2 u2
    | TyForall (qs1, t1), TyForall (qs2, t2) ->
       (* We demand that iterated quantified types have the same number of
          quantifiers.  To achieve this it is crucial that nested quantifiers
          are flattened when necessary -- see Generalize.flatten_outer_foralls.
        *)
       if (List.length qs1 != List.length qs2) then raise Iter2;
       List.iter2 f qs1 qs2;
       f t1 t2
    | TyInt, TyInt -> ()
    | TyBool, TyBool -> ()
    | _, _ ->
        raise Iter2

  (* Pretty printer for client types (structure of types).  It is mutually
     recursive with printer for type variables.  Cf. SolverLo.print_var  *)
  let print fuel f s =
    let open PPrint in
    match s with
    | TyArrow (t1, t2) ->
       parens (f fuel t1 ^^ space ^^ string "->" ^^ space ^^ f fuel t2)
    | TyProduct (t1, t2) ->
       parens (f fuel t1 ^^ string "×" ^^ f fuel t2)
    | TyForall ([],  t) -> f fuel t
    | TyForall (qs,  t) ->
       string "forall " ^^ lbracket ^^
       separate (comma ^^ space) (List.map (fun q -> f fuel q) qs) ^^
       rbracket ^^
       dot ^^ space ^^
       f fuel t
    | TyInt -> string "Int"
    | TyBool -> string "Bool"

end

(* -------------------------------------------------------------------------- *)

(* The unifier type structure is decoded into the target calculus type structure
   as follows.  See SolverSig module for high-level comments about functions. *)

module O = struct

  type tyvar =
    int

  type 'a structure =
    'a S.structure

  type ty =
    F.nominal_type

  module TyVarMap = Map.Make(struct type t = int let compare = compare end)

  let variable x =
    F.TyVar x

  (* Create one F.TyForall per quantifier.  If no quantifiers are given return
     unmodified body. *)
  let forall qs body = List.fold_right (fun q t -> F.TyForall (q, t)) qs body

  let to_scheme ty =
    let rec go qs ty = match ty with
      | F.TyForall (q, body) -> go (q :: qs) body
      | t                    -> (List.rev qs, t)
    in go [] ty

  let structure t =
    match t with
    | S.TyArrow (t1, t2) ->
        F.TyArrow (t1, t2)
    | S.TyProduct (t1, t2) ->
        F.TyProduct (t1, t2)
    | S.TyForall (qs, t) ->
        List.fold_right (fun q t -> F.TyForall (F.decode_tyvar q, t)) qs t
    | S.TyInt -> F.TyInt
    | S.TyBool -> F.TyBool

  let to_variable fresh_tycon fresh callback (env : 'a TyVarMap.t) (body : ty) :
        'a =
    let rec go ty = match ty with
      | F.TyVar v              -> TyVarMap.find v env
      | F.TyArrow   (ty1, ty2) -> fresh (S.TyArrow   (go ty1, go ty2))
      | F.TyProduct (ty1, ty2) -> fresh (S.TyProduct (go ty1, go ty2))
      | F.TyForall _           -> callback ty
      | F.TyInt                -> fresh_tycon S.TyInt
      | F.TyBool               -> fresh_tycon S.TyBool
      | F.TyMu _               -> assert false
    in go body

  let mu x t =
    F.TyMu (x, t)
end

module ML = struct
  type ty    = O.ty
  type tevar = string

  (* Fresh tevar names *)
  let fresh_tevar =
    let postincrement r =
      let v = !r in
      r := v + 1;
      v in
    let counter = ref 0 in
    fun () ->
    "_x" ^ string_of_int (postincrement counter)

  type term =
    | Var of tevar
    | FrozenVar of tevar
    | Abs of tevar * ty option * term
    | App of term * term
    | Let of tevar * ty option * term * term
    | Pair of term * term
    | Proj of int * term
    | Int of int
    | Bool of bool

end

(* -------------------------------------------------------------------------- *)

(* Instantiate the solver. *)

module Solver =
  Inferno.SolverHi.Make(struct
      include String type tevar = t
      let print_tevar = PPrint.string
    end)(S)(O)

open Solver

(* -------------------------------------------------------------------------- *)

let arrow x y =
  S.TyArrow (x, y)

let product x y =
  S.TyProduct (x, y)

let product_i i x y =
  assert (i = 1 || i = 2);
  if i = 1 then
    product x y
  else
    product y x

let rec is_val = function
  | ML.App _            -> false
  | ML.Let (_, _, n, m) -> is_val n && is_val m
  | _                   -> true

(* Value restriction *)
let rec is_gval = function
  | ML.App _ | ML.FrozenVar _ -> false
  | ML.Let (_, _, n, m)       -> is_val n && is_gval m
  | _                         -> true

(* Ensures that all elements of xs appearing in ys appear at the front and in
   the same order *)
let rec align_order equal xs ys = match xs, ys with
  | [], _ -> ys
  | _, [] -> []
  | x :: xs, _ ->
     let equals, others = List.partition (equal x) ys in
     List.append equals (align_order equal xs others)

(* -------------------------------------------------------------------------- *)

(* The client uses the combinators provided by the solver so as to transparently
   1- analyse the source term and produce constraints; and 2- decode the
   solution of the constraints and produce a term in the target calculus. These
   two steps take place in different phases, but the code is written as if there
   was just one phase.

   [value_restriction] argument controls behaviour of let generalization.  [env]
   stores a list of rigid type variables brought into scope by type annotations
   on let bindings. *)

let rec hastype (value_restriction : bool) (env : int list) (t : ML.term)
                (w : variable) : F.nominal_term co
= let hastype = hastype value_restriction in
  match t with

  | ML.Int x ->
     w --- S.TyInt <$$> fun () -> F.Int x

  | ML.Bool b ->
     w --- S.TyBool <$$> fun () -> F.Bool b

    (* Variable. *)
  | ML.Var x ->
      (* [w] must be an instance of the type scheme associated with [x]. *)
      instance x w <$$> fun tys ->
      (* The translation makes the type application explicit. *)
      F.ftyapp (F.Var x) tys

    (* Frozen variable. *)
  | ML.FrozenVar x ->
     (* Frozen variables are not instantiated but taken directly from the
        environment. *)
      freeze x w <$$> fun () ->
      (* Unlike in the Var case, there's no type application for frozen
         variables. *)
      F.Var x

    (* Abstraction. *)
  | ML.Abs (x, ann, u) ->

     (* Construct an existential variable with structure defined by the type
        annotation. [false] flag means "generate unregistered variables" (as
        opposed to generic, instantiable variables). *)
      let ty = Inferno.Option.map (annotation_to_variable env false) ann in

      (* FIXME: when type signature is missing this existential should have
         monomorphic restriction.  See bug #35 *)
      exist ?v:ty (fun v1 ->
        (* Use [exist_] because we don't need the resulting type in the
           generated System F term. *)
        exist_ (fun v2 ->
          (* [w] must be the function type [v1 -> v2]. *)
          w --- arrow v1 v2 ^^
            (* FIXME: this differs from C-Abs rule in that it doesn't generate a
               def constraint.  See bug #35 *)
            let1_mono x ty (fun v -> v -- v1) (hastype env u v2)
        )
      ) <$$> fun (ty1, (_, _, (), u')) ->
        (* Once these constraints are solved, we obtain the translated function
           body [u']. There remains to construct an explicitly-typed abstraction
           in the target calculus. *)
      F.Abs (x, ty1, u')

    (* Application. *)
  | ML.App (t1, t2) ->

      (* Introduce a type variable to stand for the unknown argument type. *)
      exist_ (fun v ->
        lift (hastype env) t1 (arrow v w) ^&
        (hastype env) t2 v
      ) <$$> fun (t1', t2') ->
      F.App (t1', t2')

    (* Let bindings. *)
  | ML.Let (x, ann, t, u) ->

     (* FIXME: annotated let bindings should use CForall and CDef constraints
        once they are added.  It will probably make sense to separate this out
        into a case dedicated to annotated lets.  See bug #35 *)
     (* Extend bound type variables environment.  This ensures quantifiers
        introduced in an annotation are visible in the bound term and can be
        used in annotations inside it. *)
     let bound_env = match ann with
         | Some ann -> let (qs, _) = O.to_scheme ann in List.append qs env
         | _        -> env in

     (* Convert type annotation to an internal representation.  Treat variables
        in scope as generic. *)
     let ty = Inferno.Option.map (annotation_to_variable env true) ann in

     (* Pick appropriate function for constructing let constraint *)
     let let1 = if value_restriction && not (is_gval t)
                then let1_mono
                else let1_gen in

     let1 x ty (hastype bound_env t) (hastype env u w) <$$>
       fun (t, a, t', u') ->
       (* [a] are the type variables that we must introduce via Lambda (type)
          abstractions while type-checking [t'].  [t] is a type of bound term.
          Let us denote quantifiers of [t] as [b].  In FreezeML [a] is a subset
          of [b].  Consider:

          let x = auto ~id in ...

          There is no need to bind any type variables using Lambda-abstraction
          in the body of bound term (therefore [a] is empty) but [x] has the
          type scheme [forall a. a -> a], making [b] non-empty.  When [a] is not
          empty its variables must appear in the same order as they appear in
          [b]. *)
       F.Let (x, F.ftyabs (align_order (==) (fst (O.to_scheme t)) a) t', u')

    (* Pair. *)
  | ML.Pair (t1, t2) ->

      exist_ (fun v1 ->
        exist_ (fun v2 ->
          (* [w] must be the product type [v1 * v2]. *)
          w --- product v1 v2 ^^
          (* [t1] must have type [t1], and [t2] must have type [t2]. *)
          hastype env t1 v1 ^&
          hastype env t2 v2
        )
      ) <$$> fun (t1, t2) ->
      (* The System F term. *)
      F.Pair (t1, t2)

    (* Projection. *)
  | ML.Proj (i, t) ->

      exist_ (fun other ->
        lift (hastype env) t (product_i i w other)
      ) <$$> fun t ->
      F.Proj (i, t)

exception Unbound = Solver.Unbound
exception NotMono = Solver.NotMono
exception Unify = Solver.Unify
exception UnifySkolem = Solver.UnifySkolem
exception UnifyMono = Solver.UnifyMono
exception Cycle = Solver.Cycle
exception MismatchedQuantifiers = Solver.MismatchedQuantifiers

(* The top-level wrapper uses [let0]. It does not require an expected
   type; it creates its own using [exist]. And it runs the solver. *)

let translate (value_restriction : bool) (t : ML.term) : F.nominal_term =
  let let0 = if value_restriction && not (is_gval t)
             then let0_mono
             else let0_gen in
  solve false (
    let0 (exist_ (hastype value_restriction [] t)) <$$> fun (vs, t) ->
    (* [vs] are the binders that we must introduce *)
    F.ftyabs vs t
  )
