(* This sample client performs type inference for a fragment of ML and translates
   it down to a fragment of System F. *)

(* -------------------------------------------------------------------------- *)

(* The unifier will use the following type structure. *)

module S = struct

  type 'a structure =
    | TyArrow of 'a * 'a
    | TyProduct of 'a * 'a
    | TyForall of 'a list * 'a
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
       if (List.length qs1 != List.length qs2) then raise Iter2;
       (* S-Decompose-Forall *)
       List.iter2 f qs1 qs2;
        f t1 t2
    | TyInt, TyInt -> ()
    | TyBool, TyBool -> ()
    | _, _ ->
        raise Iter2

  let print fuel f s =
    let open PPrint in
    match s with
    | TyArrow   (t1, t2) ->
       parens (f fuel t1 ^^ space ^^ string "->" ^^ space ^^ f fuel t2)
    | TyProduct (t1, t2) ->
       parens (f fuel t1 ^^ string "×" ^^ f fuel t2)
    | TyForall  ([],  t) -> f fuel t
    | TyForall  (qs,  t) ->
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
   as follows. *)

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

  let forall qs body = match qs with
    | [] -> body
    | _  -> List.fold_right (fun q t -> F.TyForall (q, t)) qs body

  let rec to_scheme = function
    | F.TyForall (q, body) ->
       let (qs, body) = to_scheme body in
       (q :: qs, body)
    | t                     -> ([], t)

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
    (* END ML *)
    | Pair of term * term
    | Proj of int * term
    | Int of int
    | Bool of bool

  (* Unannotated abstraction and let *)
  let abs (x, m) = Abs (x, None, m)

  let let_ (x, m, n) = Let (x, None, m, n)

  (* FreezeML syntactic sugar *)
  let gen v =
    let x = fresh_tevar () in
    Let (x, None, v, FrozenVar x)

  let gen_annot v ty =
    let x = fresh_tevar () in
    Let (x, Some ty, v, FrozenVar x)

  let inst m =
    let x = fresh_tevar () in
    Let (x, None, m, Var x)
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

let is_gval = function
  | ML.App _ | ML.FrozenVar _ -> false
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
   1- analyse the source term and produce constraints; and 2- decode the solution
   of the constraints and produce a term in the target calculus. These two steps
   take place in different phases, but the code is written as if there was just
   one phase. *)

(* The function [analyse] takes a source term [t] and an expected type [w].
   No type environment is required, as everything is built into the constraint via
   suitable combinators, such as [def]. *)

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
      frozen_instance x w <$$> fun () ->
      (* The translation makes the type application explicit. *)
      F.Var x

    (* Abstraction. *)
  | ML.Abs (x, None, u) ->

      (* We do not know a priori what the domain and codomain of this function
         are, so we must infer them. We introduce two type variables to stand
         for these unknowns. *)
      exist (fun v1 ->
        (* Here, we could use [exist_], because we do not need [ty2]. I refrain
           from using it, just to simplify the paper. *)
        exist (fun v2 ->
          (* [w] must be the function type [v1 -> v2]. *)
          (* Here, we could use [^^], instead of [^&], so as to avoid building
             a useless pair. I refrain from using it, just to simplify the paper. *)
          w --- arrow v1 v2 ^&
          (* Under the assumption that [x] has type [domain], the term [u] must
             have type [codomain]. *)
          def x v1 (hastype env u v2) ^&
          (* Monomorphic predicate on an unannotated binder *)
          mono x v1
        )
      ) <$$> fun (ty1, (_ty2, ((), (u',())))) ->
      (* Once these constraints are solved, we obtain the translated function
         body [u']. There remains to construct an explicitly-typed abstraction
         in the target calculus. *)
      F.Abs (x, ty1, u')

  | ML.Abs (x, Some ty, u) ->

     (* Construct an existential variable with structure defined by the type
        annotation. *)

      exists_sig (annotation_to_variable false env ty) (fun v1 ->

        (* Here, we could use [exist_], because we do not need [ty2]. I refrain
           from using it, just to simplify the paper. *)
        exist (fun v2 ->
          (* [w] must be the function type [v1 -> v2]. *)
          (* Here, we could use [^^], instead of [^&], so as to avoid building
             a useless pair. I refrain from using it, just to simplify the
             paper. *)
          w --- arrow v1 v2 ^&
          (* Under the assumption that [x] has type [domain], the term [u] must
             have type [codomain]. *)
          def x v1 (hastype env u v2)
        )
      ) <$$> fun (ty1, (_ty2, ((), u'))) ->
        (* Once these constraints are solved, we obtain the translated function
           body [u']. There remains to construct an explicitly-typed abstraction
           in the target calculus. *)
      F.Abs (x, ty1, u')

    (* Application. *)
  | ML.App (t1, t2) ->

      (* Introduce a type variable to stand for the unknown argument type. *)
      exist (fun v ->
        lift (hastype env) t1 (arrow v w) ^&
        (hastype env) t2 v
      ) <$$> fun (_ty, (t1', t2')) ->
      F.App (t1', t2')

    (* Generalization. *)
  | ML.Let (x, ann, t, u) ->

     (* Extend bound type variables environment.  This ensures quantifiers
        introduced in an annotation are visible in the bound term and can be
        used in annotations. *)
     let bound_env = match ann with
         | Some ann -> let (qs, _) = O.to_scheme ann in List.append qs env
         | _        -> env in

     (* When value restriction is enabled and we let-bind a non-guarded
        expression (either an application or a frozen variable) we treat this
        binding as if it was a lambda abstraction.  In other words let
        expression of the form:

          let x : ty = t in u

        is treated as

          (\x:ty. u) t

        which means we generate constraints as if it was a combination of lambda
        abstraction and application, but in the resulting System F term we
        reconstruct a let binding.  *)
     if value_restriction && not (is_gval t) then
       begin
         match ann with
         | None ->
               exist (fun v1 ->
                   hastype env t v1 ^&
                   def x v1 (hastype env u w)
            ) <$$>
                 fun (_ty', (t', u')) ->
                 F.Let (x, t', u')
         | Some ty ->
            exist (fun v2 ->
                exists_sig (annotation_to_variable false env ty) (fun v1 ->
                    exist (fun v ->
                        v --- arrow v1 w ^&
                          hastype env t v2 ^&
                            def x v1 (hastype env u w) ^& v2 -- v1))
              ) <$$>
              fun (_ty', (_ty2', (_, ((), (t', (u',())))))) ->
              F.Let (x, t', u')
       end
     else begin
      (* Construct a ``let'' constraint. *)
      let ty = Inferno.Option.map (annotation_to_variable true bound_env) ann in
      let1 x ty (is_gval t) (hastype bound_env t) (hastype env u w)
      <$$> fun (t, a, t', u') ->
           (* [a] are the type variables that we must introduce (via
              Lambda-abstractions) while type-checking [t']. [t] is a type of
              bound terms.  Let us denote quantifiers of [t] as [b].  In
              FreezeML [a] is a subset of [b].  Consider:

                let x = auto ~id in ...

              There is no need to bind any type variables using
              Lambda-abstraction in the body of bound term (therefore [a] is
              empty) but [x] has the type scheme [forall a. a -> a], making [b]
              non-empty.  When [a] is not empty its variables must appear in the
              same order as they appear in [b]. *)

           F.Let (x, F.ftyabs (align_order (==) (fst (O.to_scheme t)) a) t', u')
      end

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

(* The top-level wrapper uses [let0]. It does not require an expected
   type; it creates its own using [exist]. And it runs the solver. *)

exception Unbound = Solver.Unbound
exception NotMono = Solver.NotMono
exception Unify = Solver.Unify
exception UnifySkolem = Solver.UnifySkolem
exception UnifyMono = Solver.UnifyMono
exception Cycle = Solver.Cycle
exception MismatchedQuantifiers = Solver.MismatchedQuantifiers

let translate (value_restriction : bool) (t : ML.term) : F.nominal_term =
  solve false (
    let0 (exist_ (hastype value_restriction [] t)) <$$> fun (vs, t) ->
    (* [vs] are the binders that we must introduce *)
    F.ftyabs vs t
  )
