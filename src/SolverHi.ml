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

module Make
  (X : TEVAR)
  (S : STRUCTURE)
  (O : OUTPUT with type 'a structure = 'a S.structure)
= struct

(* -------------------------------------------------------------------------- *)

(* We rely on the low-level solver interface. *)

module Lo =
  SolverLo.Make(X)(S)(O)

open Lo

type variable =
  Lo.variable

(* -------------------------------------------------------------------------- *)

(* We now set up the applicative functor API, or combinator API, to the
   solver. The constraint construction phase and the witness decoding phase
   are packaged together, with two benefits: 1- the syntax of constraints and
   witnesses, as well as the details of write-once references, are hidden; 2-
   the client can write code in a compositional and declarative style, under
   the illusion that constructing a query immediately gives rise to an
   answer. *)

(* The client is allowed to construct objects of type ['a co]. Such an object is
   a pair of a constraint and a continuation. It is evaluated in two phases. In
   the first phase, the constraint is solved. In the second phase, the continuation
   is invoked. It is allowed to examine the witness, and must produce a value of
   type ['a]. *)

(* The continuation has access to an environment of type [env]. For the moment,
   the environment is just a type decoder. *)

type env =
  decoder

type 'a co =
  rawco * (env -> 'a)

(* -------------------------------------------------------------------------- *)

(* The type ['a co] forms an applicative functor. *)

let pure a =
  CTrue,
  fun _env -> a

let (^&) (rc1, k1) (rc2, k2) =
  CConj (rc1, rc2),
  fun env -> (k1 env, k2 env)

let map f (rc, k) =
  rc,
  fun env -> f (k env)

(* The function [<$$>] is just [map] with reversed argument order. *)

let (<$$>) a f =
  map f a

(* The function [^^], a variation of [^&], also builds a conjunction constraint,
   but drops the first component of the resulting pair, and keeps only the second
   component. [f ^^ g] is equivalent to [f ^& g <$$> snd]. *)

let (^^) (rc1, k1) (rc2, k2) =
  CConj (rc1, rc2),
  fun env ->
    let _ = k1 env in
    k2 env

(* The type ['a f] does not form a monad. Indeed, there is no way of defining
   a [bind] combinator. *)

(* A note on syntax. We need [--] to bind tighter than [^&], which in turn
   must bind tighter than [<$$>]. This explains in part our choice of operator
   names. *)

(* -------------------------------------------------------------------------- *)

(* [annotation_to_variable] converts a type signature to a unifier variable.
   There are several subtleties here:

    * Annotations can either be placed on let expressions or on lambda binders.
      Annotation on a let expression brings its quantifiers into scope in the
      bound term.  Variables in scope are tracked by the client and passed in
      as initial env to the function.  The extra flag determines whether these
      quantifiers should be generic (for let expressions) or not (for lambdas).
      It is crucial that for lambda expressions we don't treat variables
      introduced by quantifiers in a signature as generic.

    * When traversing the body we must also carefully distinguish whether we
      generate generic or unregistered variables.  Starting at the top level we
      generate unregistered variables, but when we enter a forall we switch to
      generating generic variables.  This is done by replacing `fresh` function
      passed to worker.

    * Type constructors for fixed types (Int, Bool) must always be created as
      unregistered variables, not as generic variables.  For this reason
      O.to_variable needs two fresh functions: one that always creates an
      unregistered variable, and one that changes depending when we are in a
      quantified type.
 *)
(* JSTOLAREK: I don't like this function.  It is convoluted, feels fragile and I
   fear it is very client-specific. *)
let annotation_to_variable (env : int list) (generic_qs : bool) (t : O.ty) :
      Lo.variable =
  let extend_env fresh env qs =
    List.fold_left
      (fun env q -> O.TyVarMap.add q (fresh None) env)
      env qs in
  (* An alias that always passes the same function for creating fresh type
     constructors. *)
  let to_variable = O.to_variable (fun s -> Lo.fresh (Some s)) in
  let rec worker fresh init_env t : Lo.variable =
    let (qs, body) = O.to_scheme t in
    let env = extend_env Lo.fresh_generic init_env qs in
    let qs' = List.map (fun q -> O.TyVarMap.find q env) qs in
    match qs' with
    | [] -> to_variable (fun s -> Lo.fresh (Some s)) (worker fresh env) env body
    | _  -> fresh (Some (S.forall qs' (to_variable
                                    (fun s -> Lo.fresh_generic (Some s))
                                    (worker Lo.fresh_generic env) env body))) in
  let fresh = if generic_qs then Lo.fresh_generic else Lo.fresh in
  worker Lo.fresh (extend_env fresh O.TyVarMap.empty env) t

(* -------------------------------------------------------------------------- *)

(* Existential quantification. *)

let exist ?(v=fresh None) f =
  (* Pass [v] to the client. *)
  let rc, k = f v in
  (* Wrap the constraint [c] in an existential quantifier, *)
  CExist (v, rc),
  (* and construct a continuation which returns a pair of the witness for [v]
     and the value of the underlying continuation [k]. *)
  fun env ->
    let decode = env in
    (decode v, k env)

(* [construct] is identical to [exist], except [None] is replaced with
   [Some t]. We do not factor out the common code, because we wish to
   show only [exist] in the paper. *)

let construct t f =
  let v = fresh (Some t) in
  let rc, k = f v in
  CExist (v, rc),
  fun env ->
    let decode = env in
    (decode v, k env)

let exist_aux_ t f =
  let v = fresh t in
  let rc, k = f v in
  CExist (v, rc),
  (* Keep the original continuation. The client doesn't need the witness. *)
  k

let exist_ f =
  exist_aux_ None f
  (* This is logically equivalent to [exist f <$$> snd], but saves a
     call to [decode] as well as some memory allocation. *)

let construct_ t f =
  exist_aux_ (Some t) f

let lift f v1 t2 =
  construct_ t2 (fun v2 ->
    f v1 v2
  )

(* -------------------------------------------------------------------------- *)

(* Equations. *)

let (--) v1 v2 =
  CEq (v1, v2),
  fun _env -> ()

let (---) v t =
  lift (--) v t

(* If [construct_] was not exposed, [lift] could also be defined (outside this
   module) in terms of [exist_] and [---], as follows. This definition seems
   slower, though; its impact on the test suite is quite large. *)

let _other_lift f v1 t2 =
  exist_ (fun v2 ->
    v2 --- t2 ^^
    f v1 v2
  )

(* -------------------------------------------------------------------------- *)

(* Instantiation constraints. *)

let instance x v =
  (* In the constraint construction phase, create a write-once reference,
     and stick it into the constraint, for the solver to fill. *)
  let witnesses = WriteOnceRef.create() in
  CInstance (x, v, witnesses),
  fun env ->
    let decode = env in
    (* In the decoding phase, read this write-once reference, so as to
       obtain the list of witnesses. Decode them, and return them to
       the user. *)
    List.map decode (WriteOnceRef.get witnesses)

let freeze x v =
  (* No need to decode any types.  Frozen variables appear as they are without
     any type annotations or instantiations. *)
  CFrozen (x, v), fun _env -> ()

(* -------------------------------------------------------------------------- *)

(* Constraint abstractions. *)

(* The general form of [CLet] involves two constraints, the left-hand side and
   the right-hand side, yet it defines a *family* of constraint abstractions,
   bound the term variables [xs]. *)

let letn clet_type xs f1 (rc2, k2) =
  (* For each term variable [x], either create a fresh type variable [v] or use
     structure of the variable (type annotation) provided by the client, as in
     [CExist]. Also, create an uninitialized scheme hook, which will receive the
     type scheme of [x] after the solver runs. *)
  let xvss = List.map (fun (x, ty) ->
    let v = match ty with
      | None   -> fresh None
      | Some v -> v in
    x, v, WriteOnceRef.create()
  ) xs in
  (* Pass the vector of type variables to the user-supplied function [f1], as in
     [CExist].  These are fresh variables that we can later check against
     supplied type signatures. *)
  let vs = List.map (fun _ -> fresh None) xvss in
  let rc1, k1 = f1 vs in
  (* Create one more write-once reference, which will receive the list of
     all generalizable variables in the left-hand side. *)
  let generalizable_hook = WriteOnceRef.create() in
  (* Build a [CLet] constraint. *)
  CLet (clet_type, xvss, vs, rc1, rc2, generalizable_hook),
  fun env ->
    (* In the decoding phase, read the write-once references, *)
    let decode = env in
    let generalizable =
      List.map decode_variable (WriteOnceRef.get generalizable_hook)
    and ss =
      List.map (fun (_, _, scheme_hook) ->
        decode_scheme decode (WriteOnceRef.get scheme_hook)
      ) xvss
    in
    (* and return their values to the user, in addition to the values
       produced by the continuations [k1] and [k2]. *)
    ss, generalizable, k1 env, k2 env

(* The auxiliary function [single] asserts that its argument [xs] is a
   singleton list, and extracts its unique element. *)

let single xs =
  match xs with
  | [ x ] ->
      x
  | _ ->
      assert false

(* [let1] is a special case of [letn], where only one term variable is bound. *)

let let1_gen x ty f1 c2 =
  letn CLetGen [ x, ty ] (fun vs -> f1 (single vs)) c2 <$$>
  fun (ss, generalizable, v1, v2) -> (single ss, generalizable, v1, v2)

let let1_mono x ty f1 c2 =
  letn CLetMono [ x, ty ] (fun vs -> f1 (single vs)) c2 <$$>
  fun (ss, generalizable, v1, v2) -> (single ss, generalizable, v1, v2)

(* [let0] is a special case of [letn], where no term variable is bound, and
   the right-hand side is [CTrue]. We require using this form at the toplevel
   of every constraint. *)

let let0_gen c1 =
  letn CLetGen [] (fun _ -> c1) (pure ()) <$$>
  fun (_, generalizable, v1, ()) -> (generalizable, v1)

let let0_mono c1 =
  letn CLetMono [] (fun _ -> c1) (pure ()) <$$>
  fun (_, generalizable, v1, ()) -> (generalizable, v1)

(* -------------------------------------------------------------------------- *)

(* Running a constraint. *)

(* The constraint [c] should have been constructed by [let0], otherwise we
   risk encountering variables that we cannot register. Recall that
   [G.register] must not be called unless [G.enter] has been invoked first. Of
   course, we could accept any old constraint from the user and silently wrap
   it in [let0], but then, what would we do with the toplevel quantifiers? *)

include struct
  [@@@warning "-4"] (* yes, I know the following pattern matching is fragile *)

let ok rc =
  match rc with
  | CLet (_, _, _, _, CTrue, _) ->
      (* The argument of [solve] should be constructed by [let0]. *)
      true
  | _ ->
      false

end

(* Solving, or running, a constraint. *)

exception Unbound = Lo.Unbound
exception NotMono of X.tevar * O.ty
exception Unify of O.ty * O.ty
exception UnifySkolem of O.ty * O.ty
exception Cycle of O.ty
exception UnifyMono
exception MismatchedQuantifiers of O.ty list * O.ty list

let solve rectypes (rc, k) =
  assert (ok rc);
  begin try
    (* Solve the constraint. *)
    Lo.solve rectypes rc
  with
    (* Catch the unifier's exceptions and decode their arguments on the fly.
       This may be a waste of time, as the client may not need us to do this
       decoding, but this allows us to offer a nice & simple interface. Note
       that the cyclic decoder is required here, even if [rectypes] is [false],
       as recursive types can appear before the occurs check is successfully
       run. *)
  | Lo.NotMono (x, v) ->
      let decode = new_decoder true (* cyclic decoder *) in
      raise (NotMono (x, decode v))
  | Lo.Unify (v1, v2) ->
      let decode = new_decoder true (* cyclic decoder *) in
      raise (Unify (decode v1, decode v2))
  | Lo.UnifySkolem (v1, v2) ->
      let decode = new_decoder true (* cyclic decoder *) in
      raise (UnifySkolem (decode v1, decode v2))
  | Lo.Cycle v ->
      let decode = new_decoder true (* cyclic decoder *) in
      raise (Cycle (decode v))
  | Lo.UnifyMono ->
     raise (UnifyMono)
  | Lo.MismatchedQuantifiers (xs, ys) ->
     let decode = new_decoder true (* cyclic decoder *) in
     raise (MismatchedQuantifiers (List.map decode xs, List.map decode ys))
  end;
  (* Create a suitable decoder. *)
  let decode = new_decoder rectypes in
  (* Invoke the client continuation. *)
  let env = decode in
  k env

end
