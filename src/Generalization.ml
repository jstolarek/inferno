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
open Utility

module Make (S : STRUCTURE) (U : UNIFIER with type 'a structure = 'a S.structure) = struct

(* -------------------------------------------------------------------------- *)

(* The [Generalization] module manages the [rank] fields of the unification
   variables, as well as a global notion of ``current rank'', stored in the
   field [state.young]. Ranks can be thought of as de Bruijn levels, in the
   following sense: whenever the left-hand side of a [CLet] constraint is
   entered, the current rank is incremented by one. Thus, the rank of a
   variable indicates where (i.e., at which [CLet] construct) this variable is
   (existentially) bound. *)

(* The rank of a variable is set to the current rank when the variable is
   registered. Once a variable is registered, its rank can only
   decrease. Decreasing a variable's rank amounts to hoisting out the
   existential quantifier that binds this variable. *)

(* Ranks are updated in a lazy manner. Only one rank maintenance operation
   takes place during unification: when two variables are unified, the rank of
   the merged variable is set to the minimum of the ranks of the two
   variables. (This operation is performed by the unifier.) Two other rank
   maintenance operations are performed here, namely downward propagation and
   upward propagation. Downward propagation updates a child's rank, based on
   its father rank; there is no need for a child's rank to exceed its father's
   rank. Upward propagation updates a father's rank, based the ranks of all of
   its children: there is no need for a father's rank to exceed the maximum of
   its children's ranks. These operations are performed at generalization time
   because it would be costly (and it is unnecessary) to perform them during
   unification. *)

(* The [rank] field maps every variable to the [CLet] construct where it is
   bound. Conversely, the [Generalization] module keeps track, for every
   active [CLet] construct, of a (complete) list of variables that are bound
   there. This takes the form of an array, stored in the field [state.pool].
   For every rank comprised between 1 and [state.young], both included, this
   array stores a list of the variables that are bound there. This array is
   again updated in a lazy manner, at generalization time. Because the unifier
   updates the ranks, but does not know about this array, the property that
   holds in general is: if a variable [v] has rank [i], then it appears in
   pool number [j], where [i <= j] holds. Immediately after generalization has
   been performed, the array has been updated, so [i = j] holds. *)

type state = {
  (* An array of pools (lists of variables), indexed by ranks. *)
  pool: U.variable list InfiniteArray.t;
  (* The current rank. *)
  mutable young: int;
}

(* -------------------------------------------------------------------------- *)

(* The [Generalization] module is in charge of constructing and instantiating
   type schemes, or graph fragments that contain universally quantified (i.e.,
   to-be-copied) variables as well as free (i.e., not-to-be-copied) variables.
   This happens when we exit the left-hand side of a [CLet] constraint, i.e.,
   when we move from a context of the form [let x v = <hole> in c] to a
   context of the form [let x = scheme in <hole>]. At this moment, the current
   rank [state.young] is decremented by one, and all variables whose rank was
   precisely [state.young] become universally quantified, or generic. These
   variables are no longer stored in any pool, as they are no longer
   existentially quantified. Their rank is set to the constant [generic].
   This allows [instantiate] to recognize them easily. *)

(* The generic variables that have no structure are the ``quantifiers'' of the
   type scheme. A type scheme is internally represented as a pair of a list of
   quantifiers and a root variable, the ``body''. The order of the quantifiers
   is arbitrarily chosen, but once fixed, matters; the functions [quantifiers]
   and [instantiation] must agree on this order. The quantifiers are exactly
   the variables that are reachable from the body, have rank [generic], and
   have no structure. *)

(* FPOTTIER: Technical note (mostly to myself). The representation of type
   schemes is not stable, in the following sense. When a scheme is first created,
   its universal quantifiers versus free variables are recognized by their rank
   (rank [generic], versus a positive rank). This remains valid as long as
   this type scheme is in scope, i.e., as long as the current rank does not
   decrease below its current value. However, the current rank ultimately
   decreases (all the way down to zero), and at this final point, all
   variables have rank [generic], so the type schemes that were previously
   created are no longer useable. We could fix this problem (if desired) by
   not relying on the rank within [instantiate]; we would instead rely on a
   list of all generic variables (with or without structure). Note: the
   field [quantifiers] is a list of the generic variables *without* structure. *)

(* TEMPORARY consider doing this? maybe benchmark.
   If we DON'T do it, then we should document the fact that [instantiate]
   won't work any more after the current rank decreases below its current
   value. (Not really a problem, as the end-end-user is not supposed to
   have access to this function.) *)

type scheme = {
  (* A list of quantifiers. *)
  quantifiers: U.variable list;
  (* A distinguished variable forms the body of the type scheme. *)
  body: U.variable
}

(* -------------------------------------------------------------------------- *)

(* The rank [no_rank] is defined as [0]. This rank is used when a variable is
   freshly created and is not known to us yet. *)
let no_rank =
  0

(* The positive ranks are valid indices into the pool array. *)
let base_rank =
  no_rank + 1

(* -------------------------------------------------------------------------- *)

(* The initial state. *)

(* The pool array is initially populated with empty pools. The current rank is
   initially set to 0, so the first rank that is actually exploited is 1. *)

let init () = {
  pool = InfiniteArray.make 8 [];
  young = no_rank;
}

(* -------------------------------------------------------------------------- *)

(* Accessors for type schemes. *)

let quantifiers { quantifiers; _ } =
  quantifiers

let body { body; _ } =
  body

let has_quantifiers { quantifiers; _ } =
  not (quantifiers = [])

(* -------------------------------------------------------------------------- *)

(* Helper functions *)

(* Does the variable have a forall structure? *)
let is_forall v =
  Option.map S.isForall (U.structure v) = Some true

(* -------------------------------------------------------------------------- *)

(* Utility functions working with type schemes. *)

(* Simple constructor for situations where we can't use record name punting *)
let make_scheme quantifiers body = {quantifiers; body}

(* Turn a variable into a scheme with no quantifiers. *)
let degenerate_scheme body = { quantifiers = []; body }

(* Add quantifiers at the beginning of a type scheme. *)
let prepend_quantifiers qs { quantifiers; body } =
  { quantifiers = List.append qs quantifiers ; body }

(* Flatten foralls nested inside a variable structure, ensuring that all
   quantifiers nested inside the structure are pulled to the top level of the
   scheme. *)
let rec flatten_outer_foralls { quantifiers; body } =
  match U.structure body with
  | None   -> { quantifiers; body }
  | Some s ->
     let go scheme = prepend_quantifiers quantifiers
                                        (flatten_outer_foralls scheme) in
     match S.maybeForall s with
     | None             -> { quantifiers; body }
     | Some ([], body') -> go (degenerate_scheme body')
     | Some (qs, body') -> go (make_scheme qs body')

(* A smart constructor of type schemes for variables constructed from type
   annotation.  Uses [flatten_outer_foralls] to ensure all nested quantifiers
   are correctly pulled to the top level. *)
let scheme body = flatten_outer_foralls (degenerate_scheme body)

(* Returns all unbound quantifiers (rank -1, no structure) in a scheme.  At the
   moment only used internally in the [Generalization] module. *)
let unbound_quantifiers { quantifiers; body } =
  let extend_env env qs = List.fold_left (fun acc v ->
      (* Only record quantifiers without structure, since quantifiers *with*
         structure are the ones that can introduce unbound quantifiers during
         unification.  See #10. *)
      if (not (U.has_structure v)) then U.VarMap.add acc v ();
      acc
    ) env qs in
  let rec go inScope v acc =
    try
      U.VarMap.find inScope v;
      acc (* Quantifier in scope, all fine *)
    with Not_found ->
      if (U.rank v = U.generic && not (U.has_structure v))
      then v :: acc (* Unbound generic quantifier that we're looking for *)
      else
        let { quantifiers; body } = scheme v in
        match U.structure body with
        | None   -> if (U.rank body = U.generic) then v :: acc else acc
        | Some s -> S.fold (go (extend_env inScope quantifiers)) s acc in
  let inScope : unit U.VarMap.t = extend_env (U.VarMap.create 8) quantifiers
  in Utility.unduplicate U.equivalent (go inScope body [])

(* Return all unbound type variables (no structure) in a scheme. *)
let unbound_tyvars { quantifiers; body } =
  let extend_env env vs = List.fold_left (fun acc v ->
      (* Only add variables without structure. *)
      if (not (U.has_structure v)) then U.VarMap.add acc v ();
      acc
    ) env vs in
  let rec go inScope v acc =
    try
      U.VarMap.find inScope v;
      acc (* variable in scope, don't add it to the accumulator *)
    with Not_found ->
      if (not (U.has_structure v))
      then v :: acc (* Unbound type variable that we're looking for *)
      else
        let { quantifiers; body } = scheme v in
        match U.structure body with
        | None   -> go (extend_env inScope quantifiers) body acc
        | Some s -> S.fold (go (extend_env inScope quantifiers)) s acc in
  let inScope : unit U.VarMap.t = extend_env (U.VarMap.create 8) quantifiers
  in Utility.unduplicate U.equivalent (go inScope body [])

(* Check whether a variable contains unbound generic variables.  This means rank
   -1 variables that don't have a structure anywhere in the type or variables
   with a structure not enclosed by a forall.  See #9.  Currently only used in
   assertions. *)
let all_generic_vars_bound { quantifiers; body } =
  let extend_env env qs = List.fold_left (fun acc q ->
      assert (U.structure q == None);
      U.VarMap.add acc q ();
      acc
    ) env qs in
  let rec go inScope v =
    let toplevel = U.VarMap.length inScope == 0 in
    try
      U.VarMap.find inScope v;
      true (* Bound variables are fine *)
    with Not_found ->
      if (U.rank v = U.generic && not (U.has_structure v))
      then false (* Unbound generic quantifiers are bad *)
      else if (U.rank v = U.generic && U.has_structure v && toplevel)
      then false (* Generic variables at top level are bad *)
      else
        let { quantifiers; body } = scheme v in
        match U.structure body with
        | None -> true (* non-generic variables without structure are fine *)
        | Some s ->
             let inScope = extend_env inScope quantifiers in
             S.fold (fun w ok -> ok && go inScope w) s true in
  let inScope : unit U.VarMap.t = extend_env (U.VarMap.create 8) quantifiers
  in go inScope body

(* Returns a list of generic top-level variables, both with and without
   structure.  Top-level means not inside a forall. *)
(* FIXME: this function will likely be redundant when we implement handling of
   type signatures as described in the paper.  See #41 and #38. *)
let toplevel_generic_variables body =
  let rec go v acc =
    let acc = if (U.rank v == U.generic) then v :: acc else acc in
    if not (is_forall v) then (* Don't descend into foralls. *)
      begin
        let { quantifiers; body } = scheme v in
        match U.structure body with
        | None   -> acc
        | Some s -> S.fold go s acc
      end
    else acc
  in go body []

(* Sets all unbound generic variables in a scheme to have a given rank.  This
   function feels like an enormous hack.  *)
(* FIXME: this function will likely be redundant when we implement handling of
   type signatures as described in the paper.  See #41 and #38. *)
let set_unbound_generic_vars_rank { quantifiers; body } rank =
  let vs = List.filter (fun x -> not (List.mem x quantifiers))
                       (toplevel_generic_variables body) in
  List.iter (fun v -> U.set_rank v rank) vs

(* Returns all bound quantifiers in a scheme, including nested ones. *)
(* FIXME: currently unused *)
let bound_quantifiers { quantifiers; body } =
  let rec go v acc =
    let { quantifiers; body } = scheme v in
    let acc = List.append quantifiers acc in
    match U.structure body with
    | None   -> acc
    | Some s -> S.fold go s acc
  in Utility.unduplicate U.equivalent (go body quantifiers)

(* Freshen all nested quantifiers, leaving top-level quantifiers unchanged.
   Assumes there are no unbound quantifiers. *)
(* FIXME: currently unused *)
let freshen_nested_quantifiers state { quantifiers; body } =
  let freshen_quantifiers env qs = List.fold_left (fun acc q ->
      assert (U.structure q = None);
      assert (U.rank q = U.generic);
      U.PureVarMap.add q (U.fresh None U.generic) acc
    ) env qs in

  let rec copy visited v =
    if U.PureVarMap.mem v visited then
      (* If this is an already visited variable return it *)
      U.PureVarMap.find v visited
    else
      begin
        let v' = U.fresh None (U.rank v) in
        let visited = U.PureVarMap.add v v' visited in
        let visited =
          if is_forall v
          then let { quantifiers; _ } = scheme v in
               freshen_quantifiers visited quantifiers
          else visited in
        U.set_structure v' (Option.map (S.map (copy visited)) (U.structure v));
        v'
      end in

  (* Identity map for top-level quantifiers.  We don't freshen those *)
  let toplevel_qs = List.fold_left (fun acc q ->
      assert (U.structure q = None);
      assert (U.rank q = U.generic);
      U.PureVarMap.add q q acc
    ) U.PureVarMap.empty quantifiers in

  { quantifiers = List.map (copy toplevel_qs) quantifiers
  ; body        = copy toplevel_qs body }

exception MismatchedQuantifiers of U.variable list * U.variable list

(* Ensures that two lists of variables have the same length and contain same
   variables in the same order.  Throws an exception if that is not the case. *)
let assert_variables_equal (xs : U.variable list) (ys : U.variable list) =
  if (List.length xs != List.length ys) then
    raise (MismatchedQuantifiers (xs, ys));
  List.iter2 (fun x y -> if U.id x != U.id y
                         then raise (MismatchedQuantifiers (xs, ys))) xs ys

(* -------------------------------------------------------------------------- *)

(* Debugging utilities. *)

let show_variable v =
  Printf.printf "id = %d, rank = %d" (U.id v) (U.rank v);
  if (U.is_monomorphic v) then Printf.printf ", mono";
  if (U.is_skolem v) then Printf.printf ", skolem";
  Printf.printf "\n";
  flush stdout

let show_pool state k =
  Printf.printf "Pool %d:\n" k;
  List.iter show_variable (InfiniteArray.get state.pool k); flush stdout

let show_young state =
  Printf.printf "state.young = %d\n" state.young; flush stdout

let show_pools state =
  for k = base_rank to state.young do
    show_pool state k
  done;
  flush stdout

let show_state label state =
  Printf.printf "%s:\n" label;
  show_young state;
  show_pools state;
  flush stdout

(* -------------------------------------------------------------------------- *)

(* The internal function [register_at_rank] assumes that [v]'s rank is already
   a valid positive rank, and registers [v] by inserting it into the appropriate
   pool. *)

let register_at_rank ({ pool; _ } as state) v =
  let rank = U.rank v in
  assert (0 < rank && rank <= state.young);
  InfiniteArray.set pool rank (v :: InfiniteArray.get pool rank)

(* The external function [register] assumes that [v]'s rank is uninitialized.
   It sets this rank to the current rank, [state.young], then registers [v]. *)

let register state v =
  assert (U.rank v = no_rank);
  U.set_rank v state.young;
  register_at_rank state v

let register_signatures state v =
  let rec go v =
    if U.rank v = no_rank then
      register state v;
    Option.iter (S.iter go) (U.structure v)
  in go v

(* FIXME: This function is most likely reundant.  See #41 *)
let remove_from_pool ({ pool; _ } as state) vs =
  (* FIXME: quadratic complexity here.  We mitigate this by only doing work when
     [vs] are non-empty and then using VarMap instead of list to make checking
     for membership cheaper.  Note that I (JS) didn't test whether using VarMap
     actually pays off.  It well might be the case that for small [vs] the cost
     of creating a VarMap outweights the benefits.  *)
  if vs != [] then
    let vs : unit U.VarMap.t = List.fold_left (fun acc v ->
      U.VarMap.add acc v (); acc) (U.VarMap.create 128) vs in
    for k = base_rank to state.young do
      InfiniteArray.set pool k (List.filter (fun v -> not (U.VarMap.mem vs v))
                                            (InfiniteArray.get pool k))
    done

(* -------------------------------------------------------------------------- *)

(* [enter] simply increments the current rank by one. The corresponding pool is
   in principle already empty. *)

let enter state =
  state.young <- state.young + 1;
  assert (InfiniteArray.get state.pool state.young = [])

(* -------------------------------------------------------------------------- *)

(* [exit] is where the moderately subtle generalization work takes place. *)

let exit rectypes state roots =

  (* Get the list [vs] of all variables in the young generation.  These are the
     candidates for getting generalized. *)
  let vs = InfiniteArray.get state.pool state.young in

  (* This hash table stores all of these variables, so that we may check
     membership in the young generation in constant time. *)
  let young_generation : unit U.VarMap.t = U.VarMap.create 128 in

  (* This array stores all of these variables, indexed by rank. The use
     of a bucket sort is theoretically costly if the [CLet]-nesting depth
     is not considered a constant, because of the need to walk through
     possibly-empty buckets; in that case, a standard sort algorithm, or
     (even better) no sort at all would suffice. (Sorting helps us compute
     better ranks; but distinguishing between [young] and non-[young] would
     be enough.) In practice, the [CLet]-nesting depth should remain low,
     and walking through empty buckets (in the loop that follows) should
     cost almost nothing. So we adopt this approach, even though it violates
     the complexity claim of the paper. *)
  let sorted : U.variable list array = Array.make (state.young + 1) [] in

  (* Initialize these data structures. *)
  List.iter (fun v ->
    U.VarMap.add young_generation v ();
    let rank = U.rank v in
    assert (0 < rank && rank <= state.young);
    sorted.(rank) <- v :: sorted.(rank)
  ) vs;

  (* Define a membership test for the young generation. *)
  let is_young v =
    U.VarMap.mem young_generation v
  in

  (* If the client would like us to detect and rule out recursive types, then
     now is the time to perform an occurs check over the young generation. *)
  if not rectypes then
    List.iter (U.new_occurs_check is_young) vs;

  (* Now, update the rank of every variable in the young generation. Downward
     propagation and upward propagation, as described above, are performed. A
     single depth-first traversal of the young generation achieves
     both. Roughly speaking, downward propagation is achieved on the way down,
     while upward propagation is achieved on the way up. (In reality, all rank
     updates takes place during the upward phase.)

     During each traversal, every visited variable is marked as such, so as to
     avoid being visited again. To ensure that visiting every variable once is
     enough, the roots must be processed by increasing order of rank. In the
     absence of cycles, this enforces the following invariant: when performing
     a traversal whose starting point has rank [k], every variable marked as
     visited has rank [k] or less already. (In the presence of cycles, this
     algorithm is incomplete and may compute ranks that are slightly higher
     than necessary.) Conversely, every non-visited variable must have rank
     greater than or equal to [k]. This explains why [k] remains constant as
     we go down (i.e., discovering [v] does not improve the value of [k] that
     we are pushing down). *)

  let visited : unit U.VarMap.t = U.VarMap.create 128 in

  for k = base_rank to state.young do

    (* A postcondition of [traverse v] is [U.rank v <= k]. (This is downward
       propagation.) *)
    let rec traverse v =
      assert (U.rank v <> no_rank);
      (* If [v] was visited before, then its rank must be below [k], as we
         adjust ranks on the way down already. *)
      if U.VarMap.mem visited v then
        assert (U.rank v <= k)
      else begin
        (* Otherwise, immediately mark it as visited, and immediately adjust
           its rank so as to be at most [k]. (This is important if cyclic
           graphs are allowed.) *)
        U.VarMap.add visited v ();
        (* Downward propagation *)
        U.adjust_rank v k;
        (* If [v] is part of the young generation, and if it has structure,
           then traverse its children (updating their ranks) and on the way
           back up, adjust [v]'s rank again (this is upward propagation). If
           [v] has structure but no children, then it is a constant, and it
           receives the base rank; it will be moved to the oldest pool. If
           [v] has no structure, do nothing; it would be wrong to move its
           rank down to the base rank. *)
        if is_young v then begin
          (* The rank of this variable can't have been below [k], because
             it is young but was not visited yet. Thus, it must have been
             at or above [k], and since we have just adjusted it, it must
             now be [k]. *)
          assert (U.rank v = k);
          Option.iter (fun t ->
            (* Upward propagation *)
            U.adjust_rank v (
              S.fold (fun child accu ->
                traverse child;
                (* This bit is crucial to correctly handle generalization in the
                   presence of nested quantified types. *)
                (* JSTOLAREK: I can't recall the exact details of why this works
                   and I've run out of time to properly reverse-engineer this
                   part.  If things go wrong with generalization in the presence
                   of nested quantified types this is one place to look for
                   problems.  *)
                if U.rank child = U.generic
                then max (U.rank v    ) accu
                else max (U.rank child) accu
              ) t base_rank (* the base rank is neutral for [max] *)
            )
          ) (U.structure v)
        end
        (* If [v] is old, stop. *)
        else
          assert (U.rank v < state.young)
      end

    in
    List.iter traverse sorted.(k)

  done;

  (* The rank of every variable in the young generation has now been
     determined as precisely as possible.

     Every variable that has become an alias for some other (old or young)
     variable is dropped. We keep only one representative of each class.
     See #34.

     Every variable whose rank has become strictly less than [young] may be
     safely turned into an old variable. It is moved into the pool that
     corresponds to its rank.

     Every variable whose rank is still [young] must be generalized. That is,
     it becomes universally quantified in the type scheme that is being
     created. We set its rank to [generic]. By convention, a variable of rank
     [generic] is considered universally quantified. *)

  let vs =
    List.filter (fun v ->
      begin
        if U.rank v = U.generic then
          (* A copy of this variable already visited, discard.  See #34 *)
          false
        else
        if U.rank v < state.young then begin
          register_at_rank state v;
          false
        end
        else begin
          assert (U.rank v = state.young);
          U.set_rank v U.generic;
          U.structure v = None
        end
      end
    ) vs
  in

  (* Update the state by emptying the current pool and decreasing [young]. *)
  InfiniteArray.set state.pool state.young [];
  state.young <- state.young - 1;

  (* Return the list of unique generalizable variables that was constructed
     above, and a list of type schemes, obtained from the list [roots]. *)
  vs,
  List.map (fun body ->
      let s  = flatten_outer_foralls (degenerate_scheme body) in
      let qs = unbound_quantifiers s in
      prepend_quantifiers qs s)
    roots

(* -------------------------------------------------------------------------- *)

(* Instantiation amounts to copying a fragment of a graph. The fragment that
   must be copied is determined by inspecting the rank -- [generic] means
   copy, a positive rank means don't copy. *)

let instantiate state { quantifiers; body } =

  List.iter (fun q -> assert (U.structure q = None)) quantifiers;

  (* Prepare to mark which variables have been visited and record their copy. *)
  let visited : U.variable U.VarMap.t = U.VarMap.create 128 in

  (* If the variable [v] has rank [generic], then [copy v] returns a copy of
     it, and copies its descendants recursively. If [v] has positive rank,
     then [copy v] returns [v]. Only one copy per variable is created, even if
     a variable is encountered several times during the traversal. *)

  let rec copy toplevel v =

    (* If this variable has positive rank, then it is not generic: we return the
       variable as-is, no copying. *)

    if (U.rank v > 0) then
      v

    else begin
      try
        assert (U.rank v = U.generic);
        (* If a copy of this variable has been created already, return it. *)
        U.VarMap.find visited v
      with Not_found ->
        (* The variable must be copied, and has not been copied yet. Create a
           new variable, register it, and update the mapping. Then, copy its
           descendants. Note that the mapping must be updated before making a
           recursive call to [copy], so as to guarantee termination in the
           presence of cyclic terms. *)
        if not toplevel then begin
            (* If we're inside a nested quantified type we copy its structure
               maintaining all the ranks.  This ensures proper instantiation of
               outer quantifiers nested inside a quantified types.  It is
               important that we don't instantiate nested quantified types. *)
            let v' = U.fresh None (U.rank v) in
            (* Copy monomorphic restriction if present.  *)
            if (U.is_monomorphic v) then U.monomorphize v';
            U.VarMap.add visited v v';
            (* We're no longer at the top level if we enter a forall variable *)
            U.set_structure v' (Option.map (S.map (copy false)) (U.structure v));
            v'
          end
        else begin
            (* We are at the top level, i.e. not inside another quantified type.
               Copies of generic variables are therefore registered at current
               rank.  *)
            let v' = U.fresh None state.young in
            (* Copy monomorphic restriction if present. *)
            if (U.is_monomorphic v) then U.monomorphize v';
            register_at_rank state v';
            U.VarMap.add visited v v';
            (* We will no longer be at the top level if we enter a variable with
               a forall structure (quantified type). *)
            let toplevel = toplevel && not (is_forall v) in
            U.set_structure v' (Option.map (S.map (copy toplevel)) (U.structure v));
            v'
          end
      end
  in
  (* Enforcing proper order of evaluation is crucial here.  We need to first
     copy the outer quantifiers. *)
  let quantifiers' = List.map (copy true) quantifiers in
  let body         = copy true body in
  quantifiers', body

end
