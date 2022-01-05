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
    Tc_result.ImplementationBug

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
    Tc_result.WellTyped (Client.translate value_restriction t)
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
  let tests =
    Test_definitions.inferno_implementation_tests
      (fun t () -> test t)
      (fun t () -> known_broken_test t)
  in
  List.iter (fun thunk -> thunk ()) tests

let () = print_summary_and_exit ()
