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

open Client
open F
open Shared
open Shared.Result

let verbose =
  false

(* -------------------------------------------------------------------------- *)

(* Facilities for dealing with exceptions. *)

(* A log is a mutable list of actions that produce output, stored in reverse
   order. It is used to suppress the printing of progress messages as long as
   everything goes well. If a problem occurs, then the printing actions are
   executed. *)

type log = {
  mutable actions: (unit -> unit) list
}

let create_log () =
  { actions = [] }

let log_action log action =
  log.actions <- action :: log.actions

let log_msg log msg =
  log_action log (fun () ->
    output_string stdout msg
  )

let print_log log =
  List.iter (fun action ->
    action();
    (* Flush after every action, as the action itself could raise an
       exception, and we will want to know which one failed. *)
    flush stdout
  ) (List.rev log.actions)

let attempt log msg f x =
  log_msg log msg;
  try
    f x
  with e ->
    (* All exceptions corresponding to source program being ill-typed
       (e.g. unification errors) are handled inside [translate].  If we get an
       exception at this point it means an implementation bug since we must have
       generated an ill-typed System F program.  See also comment in [translate]
       below. *)
    begin
    match e with
    | FTypeChecker.NotAnArrow ty ->
       log_action log (fun () ->
           Printf.fprintf stdout "Implementation bug.\n";
           PPrint.ToChannel.pretty 0.9 80 stdout PPrint.(
               string "Exception: not an arrow type:" ^^ hardline ^^
               string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline)
         )
    | FTypeChecker.NotAProduct ty ->
       log_action log (fun () ->
           Printf.fprintf stdout "Implementation bug.\n";
           PPrint.ToChannel.pretty 0.9 80 stdout PPrint.(
             string "Exception: not a product type:" ^^ hardline ^^
             string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline)
         )
    | FTypeChecker.NotAForall ty ->
       log_action log (fun () ->
           Printf.fprintf stdout "Implementation bug.\n";
           PPrint.ToChannel.pretty 0.9 80 stdout PPrint.(
             string "Exception: not a forall type:" ^^ hardline ^^
             string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline)
         )
    | exn ->
       log_action log (fun () ->
           Printf.fprintf stdout "Implementation bug.\n";
           Printf.fprintf stdout "%s\n" (Printexc.to_string exn);
           Printf.fprintf stdout "%s" (Printexc.get_backtrace ());
         )
    end;
    Result.ImplementationBug

(* -------------------------------------------------------------------------- *)

let print_type ty =
  PPrint.(ToChannel.pretty 0.9 80 stdout (FPrinter.print_type ty ^^ hardline))

let print_ml_term m =
  PPrint.(ToChannel.pretty 0.9 80 stdout (MLPrinter.print_term m ^^ hardline))

let print_types tys =
  PPrint.(ToChannel.pretty 0.9 80 stdout
     (lbracket ^^ separate comma (List.map FPrinter.print_type tys) ^^ rbracket
      ^^ hardline))

(* A wrapper over the client's [translate] function. *)
let translate log (t, value_restriction) =
  try
    Result.WellTyped (Client.translate value_restriction t)
  with
  | Client.Cycle ty ->
     log_action log (fun () ->
        Printf.fprintf stdout "Type error: a cyclic type arose.\n";
        print_type ty
       );
     IllTyped
  | Client.NotMono (x, ty) ->
     log_action log (fun () ->
        Printf.fprintf stdout "Type error: unannotated lambda binder %s inferred with polymorphic type:\n" x;
        print_type ty
       );
     IllTyped
  | Client.Unify (ty1, ty2) ->
     log_action log (fun () ->
        Printf.fprintf stdout "Type error: type mismatch.\n";
        Printf.fprintf stdout "Type error: mismatch between the type:\n";
        print_type ty1;
        Printf.fprintf stdout "and the type:\n";
        print_type ty2;
        Printf.fprintf stdout "when translating the term:\n";
        print_ml_term t
       );
     IllTyped
  | Client.UnifySkolem (ty1, ty2) ->
     log_action log (fun () ->
        Printf.fprintf stdout "Type error: type mismatch.\n";
        Printf.fprintf stdout "Type error: skolem unification error between types:\n";
        print_type ty1;
        Printf.fprintf stdout "and the type:\n";
        print_type ty2;
        Printf.fprintf stdout "when translating the term:\n";
        print_ml_term t
       );
     IllTyped
  | Client.UnifyMono ->
     log_action log (fun () ->
         Printf.fprintf stdout  "Type error: Violated monomorphism constraint\n" );
     IllTyped
  | Client.MismatchedQuantifiers (xs, ys) ->
     log_action log (fun () ->
         Printf.fprintf stdout "Type error: Quantifiers in let annotation don't matched inferred ones.\n";
         Printf.fprintf stdout "Expected:\n";
         print_types ys;
         Printf.fprintf stdout "Inferred:\n";
         print_types xs
       );
     IllTyped
  (* No exceptions should ever happen in a correct implementation other than
     Client exceptions, which are used to communicate typechecking errors.
     However, our implementation is not proven correct and implementation bugs
     do happen.  Catching them here and reporting them explicitly in the
     testsuite driver greatly simplifies testing since we don't need to comment
     out buggy test cases.  *)
  | exn ->
     log_action log (fun () ->
        Printf.fprintf stdout "Implementation bug.\n";
        Printf.fprintf stdout "%s\n" (Printexc.to_string exn);
        Printf.fprintf stdout "%s" (Printexc.get_backtrace ());
       );
     ImplementationBug

(* -------------------------------------------------------------------------- *)

let failing_test_count = ref 0

let print_summary_and_exit () =
  if !failing_test_count > 0 then
    begin
      Printf.printf "\n\027[31mSummary: There were %d problem(s)\027[0m\n"
        !failing_test_count;
      exit 1
    end
  else
    begin
      Printf.printf "\n\027[32mSummary: All tests behave as expected\027[0m\n";
      exit 0
    end

(* -------------------------------------------------------------------------- *)

(* Representation of a single test *)
type test = Test_definitions.test =
  { name : string               (* test name to report in the results *)
  ; term : ML.term              (* term to typecheck                  *)
  ; typ  : Types.debruijn_type option (* expected type.  None if ill-typed  *)
  ; vres : bool                 (* enable value restriction?          *)
  }

(* The returned boolean indicates if the example "works", meaning that
   - the term had the expected type    or
   - failed to typecheck as expected.
  An implementation bug always means test failure. *)
let test_driver { name; term; typ; vres } : log * bool =
  let log = create_log() in
  log_action log (fun () ->
      Printf.printf "\n===========================================\n\n%!";
      Printf.printf "Running example %s\n%!" name;
    );
  let outcome =
    attempt log
      "Type inference and translation to System F...\n"
      (translate log) (term, vres)
  in
  match outcome, typ with
  | IllTyped, None ->
      (* Term is ill typed and is expected to be as such *)
     log_action log (fun () ->
         Printf.printf "Example %s was rejected by the typechecker as expected.\n" name;
       );
     log, true

  | WellTyped (t : F.nominal_term), Some exp_ty ->
     (* Term is determined to be well-typed and is expected to be as such.  We
        now need to check whether the inferred type is the same as the expected
        one. And we need to be careful since implementation bugs can result
        in exceptions when elaborating the term to System F. *)
      let works = ref false in
      log_action log (fun () ->
        Printf.printf "Formatting the System F term...\n%!";
        let doc = PPrint.(string "  " ^^ nest 2 (FPrinter.print_term t) ^^ hardline) in
        Printf.printf "Pretty-printing the System F term...\n%!";
        PPrint.ToChannel.pretty 0.9 80 stdout doc
      );
      begin
      match attempt log
              "Converting the System F term to de Bruijn style...\n"
              F.translate t with
      | IllTyped -> assert false (* Should never come from [attmept] *)
      | ImplementationBug ->
         (* Elaborating term to System F caused an exception *)
         log_action log (fun () ->
             Printf.printf "Example %s triggered an implementation bug!\n" name;
           );
      | WellTyped t ->
         begin
         match attempt log
                 "Type-checking the System F term...\n"
                 FTypeChecker.typeof t with
         | IllTyped -> assert false (* Should never come from [attmept] *)
         | ImplementationBug ->
            (* Typechecking caused an exception *)
            log_action log (fun () ->
                Printf.printf "Example %s triggered an implementation bug!\n" name;
              );
         | WellTyped ty ->
            log_action log (fun () ->
                if ( exp_ty = ty ) then (* Expected and actual types match. *)
                  begin
                    Printf.printf "Pretty-printing the System F de Bruijn type...\n%!";
                    let doc = PPrint.(string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline) in
                    PPrint.ToChannel.pretty 0.9 80 stdout doc;
                  end
                else (* Actual type differs from expected type *)
                  begin
                    Printf.printf "Expected type does not match actual type!\n";
                    Printf.printf "Expected:\n";
                    let doc = PPrint.(string "  " ^^ FPrinter.print_debruijn_type exp_ty ^^ hardline) in
                    PPrint.ToChannel.pretty 0.9 80 stdout doc;
                    Printf.printf "Actual:\n";
                    let doc = PPrint.(string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline) in
                    PPrint.ToChannel.pretty 0.9 80 stdout doc;
                  end
              );
            if ( exp_ty = ty ) then works := true else works := false
         end;
      end;
      log, !works
  | IllTyped, Some exp_ty ->
     (* Solver claim the program is ill-typed but we expected it to be
        well-typed. *)
     log_action log (fun () ->
         Printf.printf "Example %s expected to have a type:\n" name;
         let doc = PPrint.(string "  " ^^ FPrinter.print_debruijn_type exp_ty ^^ hardline) in
         PPrint.ToChannel.pretty 0.9 80 stdout doc;
         Printf.printf "but was determined ill-typed.\n";
       );
     log, false

  | WellTyped t, None ->
     (* Solver found the program to be well-typed but we expected it to be
        rejected by the solver.  Similarly to earlier case we need to be careful
        when translating the typechecked term to System F since we might run
        into problems with implementation bugs. *)
     log_action log (fun () ->
         Printf.printf "Formatting the System F term...\n%!";
         let doc = PPrint.(string "  " ^^ nest 2 (FPrinter.print_term t) ^^ hardline) in
         Printf.printf "Pretty-printing the System F term...\n%!";
         PPrint.ToChannel.pretty 0.9 80 stdout doc
       );
     begin
       match attempt log
              "Converting the System F term to de Bruijn style...\n"
              F.translate t with
      | IllTyped -> assert false
      | ImplementationBug ->
         (* Elaborating term to System F caused an exception *)
         log_action log (fun () ->
             Printf.printf "Example %s triggered an implementation bug!\n" name;
           );
      | WellTyped t ->
         begin
         match attempt log
                 "Type-checking the System F term...\n"
                 FTypeChecker.typeof t with
         | IllTyped -> assert false
         | ImplementationBug ->
            (* Typechecking caused an exception *)
            log_action log (fun () ->
                Printf.printf "Example %s triggered an implementation bug!\n" name;
              );
         | WellTyped ty ->
            log_action log (fun () ->
                Printf.printf "Pretty-printing the System F de Bruijn type...\n%!";
                let doc = PPrint.(string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline) in
                PPrint.ToChannel.pretty 0.9 80 stdout doc;
                Printf.printf "Example %s epected to be ill-typed but typechecks.\n" name;
              );
         end;
     end;
     log, false

  | ImplementationBug, _ ->
     (* Typechecking caused an exception *)
     log_action log (fun () ->
         Printf.printf "Example %s triggered an implementation bug!\n" name;
       );
     log, false


let test t : unit =
  let name = t.name in
  let log, works = test_driver t in
  if verbose then
    print_log log;
  if ( works ) then
    Printf.printf "\027[32mExample %s works as expected\027[0m\n" name
  else
    begin
      Printf.printf "\027[31mExample %s does not work as expected\027[0m\n"
        name;
      failing_test_count := !failing_test_count + 1
    end


let known_broken_test t : unit =
  let name = t.name in
  let log, works = test_driver t in
  if verbose then
    print_log log;
  if ( works ) then
    begin
      Printf.printf "\027[31mExample %s isn't broken anymore, great! Please \
                     investigate and switch it to use the normal \"test\" \
                     driver\027[0m\n" name;
      (* We count this as a "failure" to encourage people to investigate and
       switch the driver if things indeed work now *)
      failing_test_count := !failing_test_count + 1
    end
  else
    Printf.printf "\027[33mExample %s is broken, which is currently a \
                   known problem\027[0m\n" name




let () =
  let open Test_definitions in
  test env_test;
  (* PLDI paper examples *)
  test a1;
  test a1_dot;
  test a2;
  test a2_dot;
  test a4;
  test a4_dot;
  test a5;
  test a6;
  test a6_dot;
  test a7;
  test a8;
  test a10_star;
  test a11_star;
  test a12_star;

  test b1_star;

  test d1_star;
  test d2_star;

  test e3;
  test e3_dot;

  test f9;
  test f9_annot;
  test f10_dagger;

  test bad1;
  test bad2;
  test bad3;
  test bad3_no_value_restriction;
  test bad4;
  test bad4_no_value_restriction;
  test bad5;
  test bad6;

  (* Other examples *)
  test fml_id_to_int;
  test fml_id_to_bool;
  test fml_const_false;
  test fml_inst_1;
  test fml_inst_2;
  test fml_inst_3;
  test fml_inst_sig_1;
  test fml_inst_sig_2;
  test fml_id_app;

  test fml_quantifier_placement_1;
  test fml_quantifier_placement_2;

  test fml_nested_forall_inst_1;
  test fml_nested_forall_inst_2;
  test fml_nested_forall_inst_3;
  test fml_nested_forall_inst_4;

  test fml_let_annot_1;
  test fml_let_annot_2;
  test fml_let_annot_3;
  test fml_let_annot_4;
  test fml_let_annot_5;
  test fml_let_annot_6;
  test fml_let_annot_6_quantifier_shadowing;
  test fml_let_annot_7;
  test fml_let_annot_7_quantifier_shadowing;
  test fml_let_annot_8;
  test fml_let_annot_8_quantifier_shadowing;
  test fml_let_annot_9;
  test fml_let_annot_9_no_annot;
  known_broken_test fml_let_annot_10;

  test fml_mono_binder_constraint_1;
  test fml_mono_binder_constraint_2;

  test fml_quantifier_ordering_1;
  test fml_quantifier_ordering_2;
  test fml_quantifier_ordering_3;
  test fml_quantifier_ordering_4;

  test fml_redundant_quantifiers_1;

  test fml_type_annotations_1;
  test fml_id_appl;
  test fml_choose_choose;
  test fml_choose_choose_let;
  test fml_choose_choose_let_annot;
  test fml_choose_choose_lambda;
  test fml_id_auto_1;
  test fml_id_auto_2;

  test fml_alpha_equiv_1;
  test fml_alpha_equiv_2;
  test fml_alpha_equiv_3;
  test fml_alpha_equiv_4;
  test fml_alpha_equiv_5;

  test fml_mixed_prefix_1;
  test fml_mixed_prefix_2;
  test fml_mixed_prefix_2_no_sig;
  test fml_mixed_prefix_3;
  test fml_mixed_prefix_4;

  test fml_poly_binding_1;
  test fml_poly_binding_2;
  test fml_poly_binding_3;
  test fml_poly_binding_4;

  test fml_scoped_tyvars_1;

  test fml_mono_gen_test1;
  test fml_mono_gen_test2;
  test fml_e3_dot_no_lambda_sig;

  test fml_free_unification_vars_1;
  test fml_free_unification_vars_2;

  test fml_value_restriction_1;
  test fml_value_restriction_2;
  known_broken_test fml_value_restriction_3

let () = print_summary_and_exit ()
