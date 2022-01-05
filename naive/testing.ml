open Core
module N = Naive
module S = Shared

(* module Translate = DeBruijn.MakeTranslate(TypeVar)(TypeInTerm)(Int) *)
let tests = Shared.Test_definitions.naive_implementation_tests

let make_constraint ~generalise_toplevel result_var term =
  let transl_var =
    if generalise_toplevel then N.Tyvar.fresh_tyvar () else result_var
  in
  let transl_var_t = N.Types.TyVar transl_var in
  let constr_trans = N.Constraint_of_term.translate term transl_var_t in

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

  N.Constraint.Exists (result_var, open_result)

let run_test ~generalise_toplevel t =
  let open S.Logging in
  let open Shared.Test_definitions in
  let result_var = N.Tyvar.fresh_tyvar () in

  let constr = make_constraint ~generalise_toplevel result_var t.term in
  log_sexp "constraint:\n%s\n" (N.Constraint.sexp_of_t constr);

  let constr = N.Constraint.freshen_binders constr in
  log_sexp "constraint after freshening binders:\n%s\n" (N.Constraint.sexp_of_t constr);

  let exp_ty_opt = Option.map t.typ ~f:N.Types.nominal_of_debruijn in

  let initial_state = N.Solver.state_of_constraint constr in
  log_sexp "initial state:\n%s\n" (N.State.sexp_of_t initial_state);

  let result = N.Solver.solve initial_state in
  match (result, exp_ty_opt) with
  | Result.Ok { N.Solver.mono_vars; N.Solver.subst }, Some exp_ty ->
      log_message "solver succeeded";
      let res_ty = Map.find_exn subst result_var in
      log "result type:%s\n" (S.Types.string_of_typ res_ty);
      log "expected type:%s\n" (S.Types.string_of_typ exp_ty);
      OUnit2.assert_bool "Types not equal" (N.Unifier.equal exp_ty res_ty)
  | Result.Ok _, None -> OUnit2.assert_failure "Solver succeded when it shouldn't!\n"
  | Result.Error _, None -> log_message "solver failed, as expected"
  | Result.Error e, Some _ ->
      log_sexp "Solver failed with %s\n" (N.Tc_errors.sexp_of_errors e);
      OUnit2.assert_failure "Solver failed when it shouldn't!\n"

(* let main () = run_test ~generalise_toplevel:false S.Test_definitions.a2_dot *)
(* let _ = main () *)

let tests_cases =
  let test_definitions = S.Test_definitions.naive_implementation_tests in
  let convert test_def =
    let open Shared.Test_definitions in
    let open OUnit2 in
    test_def.name >:: fun ctx -> run_test ~generalise_toplevel:true test_def
  in
  List.map ~f:convert test_definitions

let suites =
  let open OUnit2 in
  "all" >::: [ "test cases" >::: tests_cases ]

let () = OUnit2.run_test_tt_main suites
