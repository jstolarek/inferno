open Core
module N = Naive
module S = Shared

(* module Translate = DeBruijn.MakeTranslate(TypeVar)(TypeInTerm)(Int) *)
let tests = Shared.Test_definitions.naive_implementation_tests

let make_constraint ~obey_value_restriction ~generalise_toplevel term =
  (* Make sure that fresh type variables we generate don't clash with those
     introduced by translating forall annotations on let terms *)
  let max_tyar_in_term =
    N.Term.type_variables term |> Set.max_elt |> Option.value ~default:(-1)
  in
  N.Tyvar.set_initial_tyvar (max_tyar_in_term + 1);
  S.Logging.log "starting fresh tyvars at %d\n" (max_tyar_in_term + 1);

  let result_var = N.Tyvar.fresh_tyvar () in

  let transl_var =
    if generalise_toplevel then N.Tyvar.fresh_tyvar () else result_var
  in
  let transl_var_t = N.Types.TyVar transl_var in
  let constr_trans =
    N.Constraint_of_term.translate ~obey_value_restriction term transl_var_t
  in

  let open_result =
    if generalise_toplevel then
      let gen_tevar = N.Tevar.fresh_tevar () in
      let result_var_t = N.Types.TyVar result_var in
      (* let gen_tyvar = N.Tevar.fresh_tevar () in *)
      N.Constraint.Let
        ( N.Types.Poly,
          gen_tevar,
          transl_var,
          constr_trans,
          N.Constraint.Freeze (gen_tevar, result_var_t) )
    else constr_trans
  in

  (result_var, N.Constraint.Exists (result_var, open_result))

let run_test ~generalise_toplevel (module Solver : N.Solving.Solver) t =
  let open S.Logging in
  let open Shared.Test_definitions in
  let obey_value_restriction = t.vres in
  let result_var, constr =
    make_constraint ~obey_value_restriction ~generalise_toplevel t.term
  in
  log_sexp "constraint:\n%s\n" (N.Constraint.sexp_of_t constr);

  let constr = N.Constraint.freshen_binders constr in
  log_sexp "constraint after freshening binders:\n%s\n"
    (N.Constraint.sexp_of_t constr);

  let exp_ty_opt = Option.map t.typ ~f:N.Types.nominal_of_debruijn in

  let initial_state = N.Solving.state_of_constraint constr in
  log_sexp "initial state:\n%s\n" (N.State.sexp_of_t initial_state);

  let result = Solver.solve initial_state in
  match (result, exp_ty_opt) with
  | Result.Ok N.State.{ mono_flex_vars; subst }, Some exp_ty ->
      log_message "solver succeeded";
      let res_ty = Map.find_exn subst result_var in
      log "result type:%s\n" (S.Types.string_of_typ res_ty);
      log "expected type:%s\n" (S.Types.string_of_typ exp_ty);
      OUnit2.assert_bool "Types not equal" (Solver.Unifier.equal exp_ty res_ty)
  | Result.Ok _, None ->
      OUnit2.assert_failure "Solver succeded when it shouldn't!\n"
  | Result.Error _, None -> log_message "solver failed, as expected"
  | Result.Error e, Some _ ->
      log_sexp "Solver failed with %s\n" (N.Tc_errors.sexp_of_errors e);
      OUnit2.assert_failure "Solver failed when it shouldn't!\n"


let test_cases_ordered, test_cases_unordered_reused =
  let mk_cases (module Solver : N.Solving.Solver) ordered =
    let test_definitions = S.Test_definitions.naive_implementation_tests in
    let convert test_def =
      let open Shared.Test_definitions in
      let open OUnit2 in
      test_def.name >:: fun ctx ->
      run_test (module Solver) ~generalise_toplevel:true test_def
    in
    List.map ~f:convert (test_definitions ordered)
  in
  ( mk_cases (module N.Solving.Ordered) true,
    mk_cases (module N.Solving.Unordered) false )

let unordered_unification_tests =
  let open N.Types in
  let open OUnit2 in
  N.Tyvar.set_initial_tyvar 100;
  let equal =
    [
      ( forall [ 0; 1 ] (TyArrow (TyVar 0, TyVar 1)),
        forall [ 1; 0 ] (TyArrow (TyVar 0, TyVar 1)) );
      ( forall [ 0; 1 ] (TyArrow (TyVar 1, TyVar 1)),
        forall [ 1 ] (TyArrow (TyVar 1, TyVar 1)) );
    ]
  in
  let not_equal =
    [
      ( forall [ 0; 1 ] (TyArrow (TyVar 0, TyVar 0)),
        forall [ 1; 0 ] (TyArrow (TyVar 0, TyVar 1)) );
      ( forall [ 0; 1 ] (TyArrow (TyVar 0, TyVar 1)),
        forall [ 0; 1 ] (TyArrow (TyVar 0, TyVar 0)) );
    ]
  in
  let check expect_equal (ty1, ty2) =
    let msg =
      Printf.sprintf "Types expected%s to be equal"
        (if expect_equal then "" else " not")
    in
    "Type equality test" >:: fun _ctx ->
    assert_bool msg Bool.(N.Unification.Unordered.equal ty1 ty2 = expect_equal)
  in

  List.append
    (List.map equal ~f:(check true))
    (List.map not_equal ~f:(check false))

let suites =
  let open OUnit2 in
  "all"
  >::: [
         "ordered test cases" >::: test_cases_ordered;
         "unordered type equality tests" >::: unordered_unification_tests;
         "ordered test cases by unordered solver"
         >::: test_cases_unordered_reused;
       ]

let () = OUnit2.run_test_tt_main suites
