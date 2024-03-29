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
open Utility

module Make
  (X : TEVAR)
  (S : STRUCTURE)
  (O : OUTPUT with type 'a structure = 'a S.structure)
= struct

(* -------------------------------------------------------------------------- *)

(* The type [tevar] of term variables is provided by [X]. *)

type tevar =
  X.tevar

module XMap =
  Map.Make(struct include X type t = tevar end)

(* The type [variable] of type variables is provided by the unifier [U], which
   we build. *)

module U =
  Unifier.Make(S)

type variable =
  U.variable

(* The type [ischeme] is provided by the generalization engine [G], which we
   build. *)

module G =
  Generalization.Make(S)(U)

type ischeme =
    G.scheme

(* -------------------------------------------------------------------------- *)

(* Creation of fresh variables. *)

let fresh t =
  U.fresh t G.no_rank

let fresh_generic t =
  U.fresh t U.generic

(* -------------------------------------------------------------------------- *)

let print_var v =
  (* In order to print the types containing client-defined types and
     solver-defined unification variables we need a pair of mutually recursive
     functions.  We additionally limit the size of printed types with fuel.
     This is necessary to avoid crashing in the presence of cyclic types. *)
  let rec var_printer    fuel v = U.print fuel struct_printer v and
          struct_printer fuel s = S.print fuel var_printer    s in
  var_printer Debug.fuel v

let print_tevar v =
  X.print_tevar v

let print_vars vs =
  let open PPrint in
  lbracket ^^
  separate (comma ^^ space) (List.map print_var vs) ^^
  rbracket

let print_scheme scheme =
  let open PPrint in
  match G.quantifiers scheme with
  | [] -> print_var (G.body scheme)
  | qs -> string "forall " ^^ print_vars qs ^^ dot ^^ space ^^
            print_var (G.body scheme)

let print_schemes vs =
  let open PPrint in
  lbracket ^^
  separate (comma ^^ space) (List.map print_scheme vs) ^^
  rbracket

(* The syntax of constraints is as follows. *)

(* This syntax is exposed to the user in the low-level interface [SolverLo],
   but not in the high-level interface [SolverHi]. So, it could be easily
   modified if desired. *)

(* FIXME: add CForall and CDef constraints.  See bug #35 *)
type rawco =
  (* Constraints *)
  | CTrue
  | CConj of rawco * rawco
  | CEq of variable * variable
  | CExist of variable * rawco
  | CInstance of tevar * variable * variable list WriteOnceRef.t
  | CFrozen of tevar * variable
  | CLet of clet_type
        * (tevar * variable * ischeme WriteOnceRef.t) list
        * variable list (* Proxy variables *)
        * rawco         (* Bound term *)
        * rawco         (* Let body *)
        * variable list WriteOnceRef.t

(* -------------------------------------------------------------------------- *)

(* The non-recursive wrapper function [solve] is parameterized by the flag
   [rectypes], which indicates whether recursive types are permitted. It
   expects a constraint and solves it; that is, either it fails with an
   exception, or it succeeds and fills the write-once references that are
   embedded in the syntax of the constraint. *)

exception Unbound of tevar
exception NotMono of tevar * variable
exception Unify = U.Unify
exception UnifySkolem = U.UnifySkolem
exception UnifyMono = U.UnifyMono
exception Cycle = U.Cycle
exception MismatchedQuantifiers = G.MismatchedQuantifiers

let solve (rectypes : bool) (c : rawco) : unit =

  (* Debugging utilities. *)
  let debug (str : string) (doc : PPrint.document) =
    let open PPrint in
    Debug.print (string str ^^ doc) in

  let debug_unify_before str v w =
    let open PPrint in
    let message =
      str ^^ space ^^ nest 2 (
          string "Trying to unifying variables:" ^^ hardline ^^
          print_var v ^^ hardline ^^
          print_var w) in
    Debug.print message in

  let debug_unify_after v =
    let open PPrint in
    let message =
      nest 2 (
          string "Unification successful.  Variable after unification:" ^^
          hardline ^^
          print_var v) in
    Debug.print message in

  (* Initialize the generalization engine. It has mutable state, so [state]
     does not need to be an explicit parameter of the recursive function
     [solve]. *)

  let state = G.init() in

  (* The recursive function [solve] is parameterized with an environment
     that maps term variables to type schemes. *)

  let rec solve (env : ischeme XMap.t) (c : rawco) : unit =
    let open PPrint in
    match c with
    | CTrue ->
        ()

    | CConj (c1, c2) ->
        Debug.print_str "Found constraint conjunction.  Solving first constraint.";
        solve env c1;
        Debug.print_str "First constraint in a conjunction solved, solving second.";
        solve env c2;
        Debug.print_str "Second constraint in a conjunction solved"

    | CEq (v, w) ->
        debug_unify_before (string "Solving equality constraint.") v w;
        U.unify v w;
        debug_unify_after v

    | CExist (v, c) ->
       (* We assume that the variable [v] has been created fresh, so it is
          globally unique, it carries no structure, and its rank is [no_rank].
          The combinator interface enforces this property. *)
        G.register_signatures state v;
        debug "Entering existential with unification variable " (print_var v);
        solve env c;
        debug "Exiting existential with unification variable " (print_var v)

    | CInstance (x, w, witnesses_hook) ->
        (* The environment provides a type scheme for [x]. *)
        let s = try XMap.find x env with Not_found -> raise (Unbound x) in

        (* Flatten nested quantifiers so that all quantifiers get instantiated.
           See bug #30. *)
        let s = G.flatten_outer_foralls s in

        (* Instantiating this type scheme yields a variable [v], which we unify
           with [w].  It also yields a list of witnesses, which we record, as
           they will be useful during the decoding phase. *)
        let witnesses, v = G.instantiate state s in
        WriteOnceRef.set witnesses_hook witnesses;

        debug_unify_before (string "Instantiating type scheme for " ^^
          print_tevar x ^^ space ^^ colon ^^ space ^^ print_scheme s ^^ dot ^^
          hardline) v w;
        U.unify v w;
        debug_unify_after v

    | CFrozen (x, w) ->
        (* The environment provides a type scheme for [x]. *)
        let s = try XMap.find x env with Not_found -> raise (Unbound x) in

        (* JSTOLAREK: This flattening is speculative, in a sense that I was
           unable to construct an example that requires this in order to work
           correctly.  Moreover, this flattening sort-of cancels out with the
           conditional below, though it does make sense if several
           forall-structured variables are nested. *)
        let s = G.flatten_outer_foralls s in

        let qs, body = G.quantifiers s, G.body s in

        (* If the type is quantified we need to create a fresh variable that has
           structure corresponding to the scheme.  If the type isn't quantified
           we just use its body. See bug #30. *)
        let v = if qs != []
                then let v = fresh (Some (S.forall qs body)) in
                     G.register state v; v
                else body in

        (* For the purpose of freezing quantifiers are considered skolems so
           that two distinct quantifiers can't be unified with each other. *)
        List.iter U.skolemize qs; (* FIXME: segfault here. See #12. *)

        debug_unify_before (string "Freezing variable " ^^
          print_tevar x ^^ space ^^ colon ^^ space ^^ print_scheme s ^^ dot ^^
          hardline) v w;
        U.unify v w;
        List.iter U.unskolemize qs;
        debug_unify_after v

    | CLet (clet_type, xvss, vs, c1, c2, generalizable_hook) ->
         let generalizing_let = clet_type = CLetGen in
         let mono_let         = clet_type = CLetMono in

        (* Warn the generalization engine that we are entering the left-hand
           side of a [let] construct. *)
        G.enter state;

        (* Register the variables [vs] with the generalization engine, just as
           if they were existentially bound in [c1]. This is what they are,
           basically, but they also serve as named entry points. *)
        List.iter (G.register state) vs;

        (* Just a chunk of debug output. *)
        begin
          if ( List.length( xvss ) > 0 ) then
            Debug.print (nest 2
              (string "Entering let binding LHS.  Defined bindings:" ^^
               hardline ^^ separate hardline (List.map (fun (x, v, _) ->
               print_tevar x ^^ space ^^ colon ^^ space ^^ print_var v) xvss)))
          else
            Debug.print_str "Entering top-level binding"
        end;
        debug "Let binding type: " (if generalizing_let
                                    then string "generalising"
                                    else string "monomorphising");
        if Debug.hard then G.show_state "State before solving" state;

        (* Solve the constraint [c1]. *)
        solve env c1;

        (* Ask the generalization engine to perform an occurs check, to adjust the
           ranks of the type variables in the young generation (i.e., all of the
           type variables that were registered since the call to [G.enter] above),
           and to construct a list [ss] of type schemes for our entry points. The
           generalization engine also produces a list [generalizable] of the young
           variables that should be universally quantified here. *)
        if Debug.hard then G.show_state "State after solving, before exiting" state;
        let generalizable, ss = G.exit rectypes state vs in
        Debug.print (string "Generalizable vars from the generalization engine: "
                         ^^ print_vars generalizable);
        Debug.print (string "Generalizable schemes from the generalization engine: "
                         ^^ print_schemes ss);
        if Debug.hard then G.show_state "State after exiting" state;

        (* Check the inferred type scheme against the type annotation or accept
           the inferred type if no annotation present.  Checking algorithm:

           - skolemize quantifiers in the signature.  This is a stateful
             operation, so all occurrences of quantifiers in the body become
             skolems

           - unify body of signature with body of inferred type scheme.  This
             updates type annotations inside the body of a bound term to match
             the types in the annotation.  Importantly, it unifies types that
             should be equal, so for example if the annotation says the type
             should be [forall a. a -> a -> a] and the inferred type is
             [forall a b. a -> b -> a] then unification ensures all appearences
             of [b] in the body of bound term are replaced with [a].  If
             unification fails it means that the type annotation is not an
             instance of inferred type.

           - unskolemize variables in the type signature
         *)
        let ss, generalizable = List.fold_right2
         (fun s (_, annotation, _) (ss, generalizable) ->
            if ( U.has_structure annotation ) then
              (* Type annotation present.  Check the inferred type against the
                 signature. *)
              begin
                (* We'll be unifying the signature with inferred type so we need
                   to ensure that all variables in the signature are correctly
                   registered. *)
                (* FIXME: this line seems redundant, i.e. commenting it causes
                   no test failures.  Pay special attention to this when
                   implementing #38.  The code here will likely go away. *)
                G.register_signatures state annotation;
                Debug.print (nest 2
                  ((if generalizing_let
                    then string "Generalizable let-binder "
                    else string "Monomorphising let-binder ") ^^
                   string "with type annotation:" ^^ hardline ^^
                   string "Annotation: " ^^ print_var annotation ^^ hardline ^^
                   string "Inferred  : " ^^ print_scheme s) );

                let annotation_scheme = G.scheme annotation in
                List.iter U.skolemize (G.quantifiers annotation_scheme);
                debug_unify_before
                  (string "Unifying let annotation with inferred type of let body.")
                  (G.body annotation_scheme) (G.body s);
                U.unify (G.body annotation_scheme) (G.body s); (* See #2 *)
                debug_unify_after (G.body annotation_scheme);
                List.iter U.unskolemize (G.quantifiers annotation_scheme);

                let generalizable =
                  if generalizing_let
                  then
                    (* When a type annotation is present we discard
                       generalizable variables from the generalization engine
                       and use quantifiers from the provided type signature. *)
                    G.quantifiers annotation_scheme
                  else
                    (* For non-generalizing lets we obviously don't generalize
                       anything. *)
                    begin
                      G.assert_variables_equal (G.quantifiers s)
                        (G.quantifiers annotation_scheme);
                      assert (generalizable = []);
                      []
                    end in
                annotation_scheme :: ss, generalizable
              end
            else
              begin
                Debug.print (nest 2
                  ((if generalizing_let
                    then string "Generalizable let-binder "
                    else string "Monomorphising let-binder ") ^^
                   string "without type annotation:" ^^ hardline ^^
                   string "Inferred type : " ^^ print_scheme s) );

                if mono_let
                then
                  (* FIXME: this code does not correctly implement semantics of
                     let mono constraints, as it monomorphises the quantifiers
                     instead of discarding them.  See #30.  This code will
                     likely have to be rewritten as part of #38. *)
                  begin
                    let ftvs        = G.unbound_tyvars s in
                    let quantifiers = G.quantifiers s in
                    Debug.print (string "Monomorphising unbound type variables "
                              ^^ print_vars ftvs ^^ string " of scheme "
                              ^^ print_scheme s);
                    List.iter U.monomorphize ftvs;
                    Debug.print (string "Monomorphising quantifiers "
                              ^^ print_vars quantifiers ^^ string " of scheme "
                              ^^ print_scheme s);
                    List.iter U.monomorphize quantifiers
                  end
                else
                  (* JSTOLAREK: this removes the monomorphic restriction from
                     the quantifiers in a generalizing let, but I can't remember
                     why we have to do this, i.e. what chain of events leads to
                     quantifiers becoming monomorphic in a generalising let.  *)
                  List.iter U.unmonomorphize generalizable;

                s :: ss, generalizable
              end
          ) ss xvss ([], generalizable) in

        Debug.print (string "Generalizable vars after signature check: "
                         ^^ print_vars generalizable);
        if Debug.hard then G.show_state "State after signature check" state;

        (* At this point some types may have unbound generic variables.  For let
           bindings with signatures this happens when the signature has no
           quantifiers but the inferred type does.  In such case unification
           with the body of inferred type introduces unbound quantifiers.  For
           let bindings without a signature this can happen when the inferred
           type has no quantifiers but contains only generic variables.  In this
           case the rank of the variable itself will be set to -1, making it an
           unbound generic variable.  These unbound generic variables need to be
           properly registered now.  See #9.

           Moreover, we need to ensure that all generic variables in the
           signature are removed from the pool.  This particularly happens for
           variables representing type constructors.  See #16

           Note that removing variables from the pool has O(n^2) complexity
           (assuming that mutable hash has constant access time) but
           `remove_from_pool` will actually do any work only if there are
           variables to be removed.  *)
        (* FIXME: this part of code relies on several functions that look like
           hacks, which is an indicator that this is likely not a good way of
           doing things.  See #41. *)
        List.iter (fun s ->
            if (not (G.has_quantifiers s)) then
              begin
                (* Set unbound generic variables as unregistered... *)
                G.set_unbound_generic_vars_rank s 0;
                (* ...and register them in the pool. *)
                G.register_signatures state (G.body s);
              end;
            (* Potential bug here.  We only remove top-level generic variables
               from the pool but it might be the case that some nested tyvars
               make it into the pool, in which case they also should be removed.
               For now I have not run into this in practice. *)
            (* FIXME: at the moment it seems that commenting out a call to
               [remove_from_pool] doesnt't make any difference.  See #41 *)
            G.remove_from_pool state (G.toplevel_generic_variables (G.body s));
            Debug.print (string "Unbound generic variables rank fix: " ^^
                           print_scheme s)
          ) ss;

        if Debug.hard then G.show_state "State after unbound vars fix" state;

        (* Fill the write-once reference [generalizable_hook]. *)
        WriteOnceRef.set generalizable_hook generalizable;
        (* Extend the environment [env] and fill the write-once references
           [scheme_hook]. *)
        if ( List.length( xvss ) > 0 ) then
          Debug.print_str "Typechecking of let bindings finished.  Adding bindings to environment:";
        let env =
          List.fold_left2 (fun env (x, _, scheme_hook) s ->
            WriteOnceRef.set scheme_hook s;
            Debug.print (string "  " ^^ print_tevar x ^^ space ^^ colon ^^
                               space ^^ print_scheme s);
            (* FIXME: first assertion is only true with the current incorrect
               semantic of let mono constraints (see #35).  After we rewrite the
               code as part of #38 make sure to revisit this assertion to make
               sure all is fine and just delete this comment.  Note also that at
               the moment this is the only place where [all_generic_vars_bound]
               is used in the code. *)
            assert (G.all_generic_vars_bound s);
            List.iter (fun q -> assert (not (U.has_structure q));
                                assert (U.rank q = U.generic))
              (G.quantifiers s);
            XMap.add x s env
          ) env xvss ss
        in
        if Debug.hard then G.show_state "State before proceeding with body" state;
        if ( List.length( xvss ) > 0 ) then
          Debug.print_str "Proceeding with let body now"
        else
          Debug.print_str "Typechecking of top-level binding finished";
        (* Proceed to solve [c2] in the extended environment. *)
        solve env c2

  in
  solve XMap.empty c

(* -------------------------------------------------------------------------- *)

(* Decoding types. *)

(* A variable is decoded to its unique integer identifier, which (via the
   function [O.variable]) is turned into an output type. *)

let decode_variable (x : variable) : O.tyvar =
  (* The following assertion ensures that the decoder is invoked only
     after the solver has been run. It would not really make sense to
     invoke the decoder before running the solver. That said, at the
     time of writing this comment, the API does not expose the decoder,
     so the client should have no way of violating this assertion. *)
  assert (U.rank x <> G.no_rank);
  U.id x

let decode_variable_as_type (x : variable) : O.ty =
  O.variable (decode_variable x)

(* A type decoder is a function that transforms a unifier variable into an
   output type. We choose to decode types in an eager manner; that is, we take
   care of invoking the decoder, so that the client never needs to perform this
   task. As a result, we do not even need to expose the decoder to the client
   (although we could, if desired). *)

type decoder =
  variable -> O.ty

(* The state of the cyclic decoder cannot persist. We must create a new
   cyclic decoder at every invocation, otherwise the [mu] binders could
   be incorrectly placed in the output. *)

let decode_cyclic : decoder =
  fun x ->
  U.new_cyclic_decoder
    decode_variable_as_type
    O.structure
    (fun x t -> O.mu (decode_variable x) t)
    x

(* Because [O.ty] is a nominal representation of types, a type is decoded
  in the same way, regardless of how many type binders we have entered.
  This makes it possible for the state of an (acyclic) decoder to persist
  between invocations. Thanks to this property, the type decoding process
  requires only linear time and space, regardless of how many calls to the
  decoder are performed. *)

(* The function [new_decoder] returns a new decoder. If [rectypes] is on,
   the cyclic decoding function, which does not have persistent state, is
   used. If [rectypes] is off, then a new acyclic decoder, with persistent
   state, is created and returned. *)

let new_decoder rectypes =
  let decode_acyclic : decoder =
    U.new_acyclic_decoder
      decode_variable_as_type
      O.structure
  in
  if rectypes then decode_cyclic else decode_acyclic

(* The function [decode_scheme] is parameterized by a type decoder, [decode]. *)

let decode_scheme decode (s : ischeme) : O.ty =
  O.forall (List.map decode_variable (G.quantifiers s))
    (decode (G.body s))

end
