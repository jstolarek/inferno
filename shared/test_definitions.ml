module ML = Ml

open Types

(* Representation of a single test *)
type test =
  { name : string               (* test name to report in the results *)
  ; term : ML.term              (* term to typecheck                  *)
  ; typ  : Types.debruijn_type option (* expected type.  None if ill-typed  *)
  ; vres : bool                 (* enable value restriction?          *)
  }

(* Syntactic sugar to simplify writing of tests *)

let var x =
  ML.Var x

let frozen x =
  ML.FrozenVar x

let app x y =
  ML.App (x, y)

let abs x y =
  ML.Abs (x, None, y)

let let_ (x, m, n) =
  ML.Let (x, None, m, n)

let gen v =
  let x = ML.fresh_tevar () in
  ML.Let (x, None, v, FrozenVar x)

let gen_annot v ty =
  let x = ML.fresh_tevar () in
  ML.Let (x, Some ty, v, ML.FrozenVar x)

let inst m =
  let x = ML.fresh_tevar () in
  ML.Let (x, None, m, ML.Var x)

let w =
  var "w"

let x =
  var "x"

let y =
  var "y"

let z =
  var "z"

let f =
  var "f"

let g =
  var "g"

let id =
  var "id"

let choose =
  var "choose"

let auto =
  var "auto"

let auto' =
  var "auto'"

let poly =
  var "poly"

let one =
  ML.Int 1

let true_ =
  ML.Bool true

let false_ =
  ML.Bool false

(* Application of equality operator to two terms *)
let eq x y =
  app (app (var "==") x) y

(* This is commonly used. *)
let forall_a_a_to_a =
  Some (TyForall (1, TyArrow (TyVar 1, TyVar 1)))

(* Function composition.  Because OCaml doesn't have one :-/ *)
let (<<) f g x = f(g(x))

(* -------------------------------------------------------------------------- *)

(* Environment with functions from Figure 2 in PLDI paper.  Note that any
   functions involving lists are omitted. *)

(* id : ∀ a. a → a *)
let fml_id k = let_ ("id", abs "x" x, k)

(* choose : ∀ a. a → a → a *)
let fml_choose k = ML.Let ("choose",
  Some (TyForall (1, TyArrow (TyVar 1, TyArrow (TyVar 1, TyVar 1)))),
  abs "x" (abs "y" x), k)

(* auto : (∀ a. a → a) → (∀ a. a → a) *)
let fml_auto k = let_ ("auto", ML.Abs ("x", forall_a_a_to_a,
                                            app x (frozen "x")), k)

(* auto' : (∀ a. a → a) → b → b *)
let fml_autoprim k = let_ ("auto'", ML.Abs ("x", forall_a_a_to_a, app x x), k)

(* app : ∀ a b. (a → b) → a → b *)
let fml_app k = let_ ("app", abs "f" (abs "x" (app f x)), k)

(* revapp : ∀ a b. b → (a → b) → b *)
let fml_revapp k = let_ ("revapp", abs "x" (abs "f" (app f x)), k)

(* zero : Int → Int.  Turns every Int into 0.  This function replaces `inc`
   from FreezeML paper for all intents and purposes, since we only care about
   typing *)
let fml_zero k = let_ ("zero", ML.Abs ("x", Some int_t, ML.Int 0), k)

(* poly : (∀ a. a → a) → (Int × Bool) *)
let fml_poly k = let_ ("poly", ML.Abs ("g", forall_a_a_to_a,
   ML.Pair (app g one, app g true_)), k)

(* pair : ∀ a b. a → b → (a × b) *)
let fml_pair k = ML.Let ("pair",
  Some (TyForall (1, TyForall (2, TyArrow (TyVar 1, TyArrow (TyVar 2,
                                  TyProduct (TyVar 1, TyVar 2)))))),
  abs "x" (abs "y" (ML.Pair (x, y))), k)

(* pair' : ∀ b a. a → b → (a × b) *)
let fml_pairprim k = ML.Let ("pair'",
  Some (TyForall (2, TyForall (1, TyArrow (TyVar 1, TyArrow (TyVar 2,
                                  TyProduct (TyVar 1, TyVar 2)))))),
  abs "x" (abs "y" (ML.Pair (x, y))), k)

(* only used in E3 *)
let fml_e3_r k =
  ML.Let
    ( "r"
    , Some (TyArrow (TyForall (1, TyArrow (TyVar 1,
                     TyForall (2, TyArrow (TyVar 2, TyVar 2)))), int_t))
    , ML.Abs
       ("x",
        Some (TyForall (1, TyArrow (TyVar 1,
                TyForall (2, TyArrow (TyVar 2, TyVar 2))))),
        one)
    , k )

(* (==) : ∀ a. a → a → Bool *)
let fml_eq k =
   ML.Let ( "=="
          , Some (TyForall (1, TyArrow (TyVar 1, TyArrow (TyVar 1, bool_t))))
          , abs "x" (abs "y" true_)
          , k )

(* id_int : Int → Int *)
let fml_id_int k =
  ML.Let ( "id_int", Some (TyArrow (int_t, int_t)), abs "x" x, k )



(* -------------------------------------------------------------------------- *)

(* Tests *)

(* Test functions making up the basic environment *)
let env_test =
  { name = "env_test"
  ; term = (fml_id       <<
            fml_choose   <<
            fml_auto     <<
            fml_autoprim <<
            fml_app      <<
            fml_revapp   <<
            fml_zero     <<
            fml_poly     <<
            fml_pair     <<
            fml_pairprim <<
            fml_eq       <<
            fml_id_int)
           (ML.Int 1)
  ; typ  = Some int_t
  ; vres = true
  }

(* PLDI paper examples (Figure 2).  Some examples are marked as MISSING.  This
   is because they use features not implemented in inferno.  Typically this
   means lists. *)

(* Note: inferno does not permit unbound type variables in the resulting System
   F term.  Therefore in the inferred types all free type variables are bound at
   the program's top level.  In the examples below type variables bound at
   program top level are placed in braces to explicitly mark they are not per se
   part of the type inferred for the term.  Concretely, if the inferred type is:

     [∀ b. ∀ a.] a → b → b

   it means that the inferred type is `a → b → b` and the quantifiers `∀ b. ∀
   a.` are added at the program top level.  *)

(* Section A: Polymorphic instantiation *)

(* example            : A1
   term               : λx.λy.y
   inferred type      : [∀ b. ∀ a.] a → b → b  (inferno order)
   type in PLDI paper : a → b → b
*)
let a1_inferno_order =
  { name = "A1"
  ; term = abs "x" (abs "y" y)
  ; typ  = Some (TyForall ((), TyForall ((),
             TyArrow (TyVar 0, TyArrow (TyVar 1, TyVar 1)))))
  ; vres = true
  }
let a1_correct_order =
  { name = "A1"
  ; term = a1_inferno_order.term
  ; typ  = Some (TyForall ((), TyForall ((),
             TyArrow (TyVar 1, TyArrow (TyVar 0, TyVar 0)))))
  ; vres = true
  }

(* example            : A1∘
   term               : $(λx.λy.y)
   inferred type      : ∀ b. ∀ a. a → b → b (* inferno order *)
   type in PLDI paper : ∀ a b. a → b → b
 *)
let a1_dot_correct_order =
  { name = "A1̣∘"
  ; term = gen (abs "x" (abs "y" y))
  ; typ  = Some (TyForall ((), TyForall ((),
             TyArrow (TyVar 1, TyArrow (TyVar 0, TyVar 0)))))
  ; vres = true
  }

let a1_dot_inferno_order =
  { name = a1_dot_correct_order.name
  ; term = a1_dot_correct_order.term
  ; typ  = Some (TyForall ((), TyForall ((),
             TyArrow (TyVar 0, TyArrow (TyVar 1, TyVar 1)))))
  ; vres = a1_dot_correct_order.vres
  }

(* example            : A2
   term               : choose id
   inferred type      : [∀ a.] (a → a) → (a → a)
   type in PLDI paper : (a → a) → (a → a)
 *)
let a2 =
  { name = "A2"
  ; term = (fml_id << fml_choose)
           (app choose id)
  ; typ  = Some (TyForall ((),
             TyArrow (TyArrow (TyVar 0, TyVar 0), TyArrow (TyVar 0, TyVar 0))))
  ; vres = true
  }

(* example            : A2∘
   term               : choose ~id
   inferred type      : (∀ a. a → a) → (∀ a. a → a)
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
 *)
let a2_dot =
  { name = "A2∘"
  ; term = (fml_id << fml_choose)
           (app choose (frozen "id"))
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                          TyForall ((), TyArrow (TyVar 0, TyVar 0))))
  ; vres = true
  }

(* MISSING: A3: choose [] ids *)

(* example            : A4
   term               : λ(x : ∀ a. a → a). x x
   inferred type      : [∀ b.] (∀ a. a → a) → b → b
   type in PLDI paper : (∀ a. a → a) → (b → b)
 *)
let a4 =
  { name = "A4"
  ; term = ML.Abs ("x", forall_a_a_to_a, app x x)
  ; typ  = Some (TyForall ((), TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                                        TyArrow (TyVar 0, TyVar 0))))
  ; vres = true
  }

(* example            : A4̣∘
   term               : λ(x : ∀ a. a → a). x ~x
   inferred type      : (∀ a. a → a) → (∀ a. a → a)
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
 *)
let a4_dot =
  { name = "A4̣∘"
  ; term = ML.Abs ("x", forall_a_a_to_a, app x (frozen "x"))
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                          TyForall ((), TyArrow (TyVar 0, TyVar 0))))
  ; vres = true
  }

(* example            : A5
   term               : id auto
   inferred type      : (∀ a. a → a) → (∀ a. a → a)
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
 *)
let a5 =
  { name = "A5"
  ; term = (fml_id << fml_auto)
           (app id auto)
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                          TyForall ((), TyArrow (TyVar 0, TyVar 0))))
  ; vres = true
  }

(* example            : A6
   term               : id auto'
   inferred type      : [∀ b.] (∀a. a → a) → b → b
   type in PLDI paper : (∀ a. a → a) → (b → b)
 *)
let a6 =
  { name = "A6"
  ; term = (fml_id << fml_autoprim)
           (app id auto')
  ; typ  = Some (TyForall ((), TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                                        TyArrow (TyVar 0, TyVar 0))))
  ; vres = true
  }

(* example            : A6∘
   term               : id ~auto'
   inferred type      : ∀ b. (∀ a. a → a) → (b → b)
   type in PLDI paper : ∀ b. (∀ a. a → a) → (b → b)
 *)
let a6_dot =
  { name = "A6∘"
  ; term = (fml_id << fml_autoprim)
           (app id (frozen "auto'"))
  ; typ  = Some (TyForall ((), TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                                        TyArrow (TyVar 0, TyVar 0))))
  ; vres = true
  }

(* example            : A7
   term               : choose id auto
   inferred type      : (∀ a. a → a) → (∀ a. a → a)
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
   related bugs       : #3
 *)
let a7 =
  { name = "A7"
  ; term = (fml_id << fml_choose << fml_auto)
           (app (app choose id) auto)
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                          TyForall ((), TyArrow (TyVar 0, TyVar 0))))
  ; vres = true
  }

(* example            : A8
   term               : choose id auto'
   inferred type      : X
   type in PLDI paper : X
 *)
let a8 =
  { name = "A8"
  ; term = (fml_id << fml_choose << fml_autoprim)
           (app (app choose id) auto')
  ; typ  = None
  ; vres = true
  }

(* MISSING : A9⋆: f (choose ~id) ids *)

(* example            : A10⋆
   term               : poly ~id
   inferred type      : Int × Bool
   type in PLDI paper : Int × Bool
 *)
let a10_star =
  { name = "A10⋆"
  ; term = (fml_id << fml_poly)
           (app poly (frozen "id"))
  ; typ  = Some (TyProduct (int_t, bool_t))
  ; vres = true
  }

(* example            : A11⋆
   term               : poly $(λx. x)
   inferred type      : Int × Bool
   type in PLDI paper : Int × Bool
 *)
let a11_star =
  { name = "A11⋆"
  ; term = (fml_poly)
           (app poly (gen (abs "x" x)))
  ; typ  = Some (TyProduct (int_t, bool_t))
  ; vres = true
  }

(* example            : A12⋆
   term               : id poly $(λx. x)
   inferred type      : Int × Bool
   type in PLDI paper : Int × Bool
 *)
let a12_star =
  { name = "A12⋆"
  ; term = (fml_id << fml_poly)
           (app (app id poly) (gen (abs "x" x)))
  ; typ  = Some (TyProduct (int_t, bool_t))
  ; vres = true
  }

(* Section B : Inference with Polymorphic arguments *)

(* example            : B1⋆
   term               : λ(f : ∀ a. a → a). (f 1, f True)
   inferred type      : (∀ a. a → a) → Int × Bool
   type in PLDI paper : (∀ a. a → a) → Int × Bool
 *)
let b1_star =
  { name = "B1⋆"
  ; term = ML.Abs ("f", forall_a_a_to_a, ML.Pair (app f one,
                                                  app f true_))
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                          TyProduct (int_t, bool_t)))
  ; vres = true
  }

(* MISSING : B2⋆: λ(xs : List (∀ a. a → a)). poly (head xs) *)


(* Section C : Functions on Polymorphic Lists *)

(* MISSING: whole section, because lists are not supported *)


(* Section D : Application Functions *)

(* example            : D1⋆
   term               : app poly ~id
   inferred type      : Int × Bool
   type in PLDI paper : Int × Bool
 *)
let d1_star =
  { name = "D1⋆"
  ; term = (fml_app << fml_poly << fml_id)
           (app (app (var "app") poly) (frozen "id"))
  ; typ  = Some (TyProduct (int_t, bool_t))
  ; vres = true
  }

(* example            : D2⋆
   term               : revapp ~id poly
   inferred type      : Int × Bool
   type in PLDI paper : Int × Bool
 *)
let d2_star =
  { name = "D2⋆"
  ; term = (fml_revapp << fml_poly << fml_id)
           (app (app (var "revapp") (frozen "id")) poly)
  ; typ  = Some (TyProduct (int_t, bool_t))
  ; vres = true
  }

(* MISSING : D3⋆: runST ~argST *)

(* MISSING : D4⋆: app runST ~argST *)

(* MISSING : D5⋆: revapp ~argST runST *)


(* Section E : η-expansion *)

(* MISSING: E1: k h l *)

(* MISSING: E2⋆: k $(λx.(h x)@) l
     where: k : ∀ a. a → List a → a
            h : Int → ∀ a. a → a
            l : List (∀ a. Int → a → a)
 *)

(* example            : E3
   term               : let r : (∀ a. a → (∀ b. b → b)) → Int = λx.1
                        in r (λx.λy.y)
   inferred type      : X
   type in PLDI paper : X
 *)
let e3 =
  { name = "E3"
  ; term = (fml_e3_r)
           (app (var "r") (abs "x" (abs "y" y)))
  ; typ  = None
  ; vres = true
  }

(* example            : E3∘
   term               : let r : (∀ a. a → (∀ b. b → b)) → Int =
                          λ(x : (∀ a. a → (∀ b. b → b))).1
                        in r $(λx.$(λy.y))
   inferred type      : Int
   type in PLDI paper : Int
 *)
let e3_dot =
  { name = "E3∘"
  ; term = (fml_e3_r)
           (app (var "r") (gen (abs "x" (gen (abs "y" y)))))
  ; typ  = Some int_t
  ; vres = true
  }

(* Section F : FreezeML Programs *)

(* MISSING: F1-F8.  Either already implemented in previous examples or not
   possible to implement due to lack of support for lists *)

(* example            : F9
   term               : let f = revapp ~id in f poly
   inferred type      : Int × Bool
   type in PLDI paper : Int × Bool
 *)
let f9 =
  { name = "F9"
  ; term = (fml_revapp << fml_id << fml_poly)
           (let_ ("f", app (var "revapp") (frozen "id"), app (var "f") poly))
  ; typ  = Some (TyProduct (int_t, bool_t))
  ; vres = true
  }

(* term               : let f : ∀ b. ((∀ a. a → a) → b) → b = revapp ~id in f poly
   inferred type      : Int × Bool
   type in PLDI paper : Int × Bool

   Note : this one is absent from PLDI paper. Value restriction must be off to
   allow generalization
 *)
let f9_annot =
  { name = "F9_annot"
  ; term = (fml_revapp << fml_id << fml_poly)
           (ML.Let ( "f"
                   , Some (TyForall (2, TyArrow (TyArrow
                             (TyForall (1, TyArrow (TyVar 1, TyVar 1)),
                           TyVar 2), TyVar 2)))
                   , app (var "revapp") (frozen "id")
                   , app (var "f") poly))
  ; typ  = Some (TyProduct (int_t, bool_t))
  ; vres = false
  }

(* example            : F10†
   term               : choose id (λ(x : ∀ a. a → a). $(auto' ~x))
   inferred type      : (∀ a. a → a) → (∀ a. a → a)
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
   note               : example in the paper is incorrect since usage of x is
                        not frozen.
 *)
let f10_dagger =
  { name = "F10†"
  ; term = (fml_choose << fml_id << fml_autoprim)
           (app (app choose id) (ML.Abs ("x", forall_a_a_to_a,
                                         gen (app auto' (frozen "x")))))
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                          TyForall ((), TyArrow (TyVar 0, TyVar 0))))
  ; vres = false
  }

(* Bad examples *)

(* example            : bad1
   term               : λf.(poly ~f, f 1)
   inferred type      : X
   type in PLDI paper : X
 *)
let bad1 =
  { name = "bad1"
  ; term = (fml_poly)
           (abs "f" (ML.Pair (app poly (frozen "f"), app (var "f") one)))
  ; typ  = None
  ; vres = true
  }

(* example            : bad2
   term               : λf.(f 1, poly ~f)
   inferred type      : X
   type in PLDI paper : X
 *)
let bad2 =
  { name = "bad2"
  ; term = (fml_poly)
           (abs "f" (ML.Pair (app (var "f") one, app poly (frozen "f"))))
  ; typ  = None
  ; vres = true
  }

(* example            : bad3
   term               : λ(bot : ∀ a. a). let f = bot bot in (poly ~f, f 1)
   inferred type      : X
   type in PLDI paper : X
 *)
let bad3 =
  { name = "bad3"
  ; term = (fml_poly)
           (ML.Abs ("bot", Some (TyForall (1, TyVar 1)),
                    let_ ("f", app (var "bot") (var "bot"),
                            (ML.Pair (app poly (frozen "f"), app (var "f") one)))))
  ; typ  = None
  ; vres = true
  }

(* term               : λ(bot : ∀ a. a). let f = bot bot in (poly ~f, f 1)
   inferred type      : X
 *)
let bad3_no_value_restriction =
  { name = "bad3_no_value_restriction"
  ; term = (fml_poly)
           (ML.Abs ("bot", Some (TyForall (1, TyVar 1)),
                    let_ ("f", app (var "bot") (var "bot"),
                            (ML.Pair (app poly (frozen "f"), app (var "f") one)))))
  ; typ  = None
  ; vres = false
  }

(* example            : bad4
   term               : λ(bot : ∀ a. a). let f = bot bot in (f 1, poly ~f)
   inferred type      : X
   type in PLDI paper : X
 *)
let bad4 =
  { name = "bad4"
  ; term = (fml_poly)
           (ML.Abs ("bot", Some (TyForall (1, TyVar 1)),
                    let_ ("f", app (var "bot") (var "bot"),
                            (ML.Pair (app (var "f") one, app poly (frozen "f"))))))
  ; typ  = None
  ; vres = true
  }

(* term               : λ(bot : ∀ a. a). let f = bot bot in (f 1, poly ~f)
   inferred type      : X
 *)
let bad4_no_value_restriction =
  { name = "bad4_no_value_restriction"
  ; term = (fml_poly)
           (ML.Abs ("bot", Some (TyForall (1, TyVar 1)),
                    let_ ("f", app (var "bot") (var "bot"),
                            (ML.Pair (app (var "f") one, app poly (frozen "f"))))))
  ; typ  = None
  ; vres = false
  }

(* example            : bad5
   term               : let f = λx.x in ~f 1
   inferred type      : X
   type in PLDI paper : X
 *)
let bad5 =
  { name = "bad5"
  ; term = let_ ("f", abs "x" x, app (frozen "f") one)
  ; typ  = None
  ; vres = true
  }

(* example            : bad6
   term               : let f = λx.x in id ~f 1
   inferred type      : X
   type in PLDI paper : X
 *)
let bad6 =
  { name = "bad6"
  ; term = (fml_id)
           (let_ ("f", abs "x" x, app (app id (frozen "f")) one))
  ; typ  = None
  ; vres = true
  }


(* Examples that were not in the PLDI paper *)

(* This was causing an exception in FTypeChecker because type equality checker
   wasn't extended to support int_t.

   term : λ(x : ∀ a. a → a). x 1
   type : (∀ a. a → a) → Int
 *)
let fml_id_to_int =
  { name = "id_to_int"
  ; term = ML.Abs ("x", forall_a_a_to_a, app x one)
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)), int_t))
  ; vres = true
  }

(* Two simple functions to test correctness of Bool implementation *)
(*
   term : λ(x : ∀ a. a → a). x true
   type : (∀ a. a → a) → Bool
*)
let fml_id_to_bool =
  { name = "id_to_bool"
  ; term = ML.Abs ("x", forall_a_a_to_a, app x false_)
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)), bool_t))
  ; vres = true
  }

(*
   term : λ(x : bool). false
   type : Bool → Bool
*)
let fml_const_false =
  { name = "const_false"
  ; term = ML.Abs ("x", Some bool_t, false_)
  ; typ  = Some (TyArrow (bool_t, bool_t))
  ; vres = true
  }

(* Some examples to test correct instantiation of quantified types *)
(*
   term : (let id = λx.x in id) 1
   type : Int
*)
let fml_inst_1 =
  { name = "inst_1"
  ; term = app (let_ ("id", abs "x" x, id)) one
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term : (let x = auto ~id in x) 1
   type : Int
*)
let fml_inst_2 =
  { name = "inst_2"
  ; term = (fml_id << fml_auto)
           (app (let_ ("x", app auto (frozen "id"), x)) one)
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term : let f : ∀a.((a → a) → Int) = λx.1
          in (λx.f x) id
   type : [∀ a.] Int

  Note: the generalisation of a in the result looks weird.
  Probably something inferno-specific?
*)
let fml_inst_3 =
  { name = "inst_3"
  ; term = (fml_id)
           (ML.Let ( "f"
                   , Some (TyForall (1, TyArrow (TyArrow( TyVar 1, TyVar 1), int_t)))
                   , abs "x" one
                   , app (abs "x" (app f x)) id))
  ; typ  = Some int_t
  ; vres = true
  }

let fml_inst_3_inferno =
  { name = fml_inst_3.name
  ; term = fml_inst_3.term
  ; typ  = Some (TyForall ((), int_t))
  ; vres = fml_inst_3.vres
  }

(*
   term : let id_int : Int → Int = λx.x in id_int 1
   type : Int
*)
let fml_inst_sig_1 =
  { name = "inst_sig_1"
  ; term = ML.Let ("id_int",
                   Some (TyArrow (int_t, int_t)),
                   abs "x" x,
                   app (var "id_int") one)
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term : let id_int : Int → Int = λx.x in id_int true
   type : X
*)
let fml_inst_sig_2 =
  { name = "inst_sig_2"
  ; term = ML.Let ("id_int",
                   Some (TyArrow (int_t, int_t)),
                   abs "x" x,
                   app (var "id_int") true_)
  ; typ  = None
  ; vres = true
  }

(*
   term : let f = (λx.x) 1 in f
   type : Int
*)
let fml_id_app =
  { name = "id_app"
  ; term = let_ ("f",
                    app (abs "x" x) one,
                    var "f")
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term : let f = (λx.1) in f
   type : [∀ a.] a → Int
*)
let fml_quantifier_placement_1 =
  { name = "quantifier_placement_1"
  ; term = let_ ("f",
                    abs "x" one,
                    var "f")
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, int_t)))
  ; vres = true
  }

(*
   term : let f = (λx.1) in ~f
   type : ∀ a. a → Int
*)
let fml_quantifier_placement_2 =
  { name = "quantifier_placement_2"
  ; term = let_ ("f",
                    abs "x" one,
                    frozen "f")
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, int_t)))
  ; vres = true
  }

(*
   term : λ(x : (∀ a. a → a) → (∀ a. a → a)). (x ~id)@ 1
   type : ((∀ a. a → a) → (∀ a. a → a)) → Int
*)
let fml_nested_forall_inst_1 =
  { name = "nested_forall_inst_1"
  ; term = (fml_id)
           (ML.Abs ("x",
                    Some (TyArrow ( TyForall (1, TyArrow (TyVar 1, TyVar 1))
                                  , TyForall (1, TyArrow (TyVar 1, TyVar 1)))),
                    app (inst (app x (frozen "id"))) one))
  ; typ  = Some
      (TyArrow
        (TyArrow ( TyForall ((), TyArrow (TyVar 0, TyVar 0))
                 , TyForall ((), TyArrow (TyVar 0, TyVar 0))), int_t))
  ; vres = true
  }

(*
   term : let (f : (∀ a. (∀ b. b → b) → a → a) → (∀ a. (∀ b. b → b) → a → a)) = id in
          let g = f $auto' in
          g ~id
   type : [∀ a.] a → a
*)
let fml_nested_forall_inst_2 =
  { name = "nested_forall_inst_2"
  ; term = (fml_id << fml_autoprim)
          ( ML.Let  ( "f"
                    , Some (TyArrow
                            ((TyForall (1, TyArrow ((TyForall (2, TyArrow (TyVar 2, TyVar 2))), TyArrow (TyVar 1, TyVar 1)))),
                             (TyForall (1, TyArrow ((TyForall (2, TyArrow (TyVar 2, TyVar 2))), TyArrow (TyVar 1, TyVar 1))))))
          , id
          , let_ ( "g", app (var "f") (gen auto')
                    , app (var "g") (frozen "id"))))
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyVar 0)))
  ; vres = true
  }

(*
   term : let (f : ∀ a. ((∀ b. b → b) → a → a) → ((∀ b. b → b) → a → a)) = id in
          let g = f (id auto') in
          g ~id
   type : [∀ a.] a → a
*)
let fml_nested_forall_inst_3 =
  { name = "nested_forall_inst_3"
  ; term = (fml_id << fml_autoprim)
           (ML.Let  ( "f"
                    , Some (TyForall (1, (TyArrow
                            (TyArrow ((TyForall (2, TyArrow (TyVar 2, TyVar 2))), TyArrow (TyVar 1, TyVar 1)),
                             TyArrow ((TyForall (2, TyArrow (TyVar 2, TyVar 2))), TyArrow (TyVar 1, TyVar 1))))))
          , id
          , let_ ( "g", app (var "f") (app id auto')
                    , app (var "g") (frozen "id"))))
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyVar 0)))
  ; vres = true
  }

(*
   term : let x : ∀ a. a → (∀ b. b → a) → Int = λx.λy. 1 in x true
   type : (∀ b. b → Bool) → Int
*)
let fml_nested_forall_inst_4 =
  { name = "nested_forall_inst_4"
  ; term = ML.Let ( "x"
                  , Some (TyForall (1, TyArrow (TyVar 1, TyArrow
                         (TyForall (2, TyArrow (TyVar 2, TyVar 1)),int_t))))
                  , abs "x" (ML.Abs ("y", Some (TyForall (2, TyArrow (TyVar 2, TyVar 1))), one))
                  , app x true_)
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, bool_t)), int_t))
  ; vres = true
  }


(* Correctness of type annotations on let binders *)
(*
   term : let (id : ∀ a. a → a) = λx.x in id
   type : ∀ a. a → a
*)
let fml_let_annot_1 =
  { name = "let_annot_1"
  ; term = ML.Let ("id", Some (TyForall (1, TyArrow (TyVar 1, TyVar 1)))
                       , abs "x" x, id)
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyVar 0)))
  ; vres = true
  }

(*
   term : let (id : ∀ a b. a → b) = λx.x in id
   type : X
*)
let fml_let_annot_2 =
  { name = "let_annot_2"
  ; term = ML.Let ("id", Some (TyForall (1, TyForall (2,
                                TyArrow (TyVar 1, TyVar 2))))
                       , abs "x" x, id)
  ; typ  = None
  ; vres = true
  }

(*
   term : let (id : ∀ a. a → a) = λ(x : Int).x in id
   type : X
*)
let fml_let_annot_3 =
  { name = "let_annot_3"
  ; term = ML.Let ("id", Some (TyForall( 1, TyArrow (TyVar 1, TyVar 1))),
                   ML.Abs ("x", Some int_t , x), id)
  ; typ  = None
  ; vres = true
  }

(*
   term : let (y : ∀ a. a → a) = ~id in y
   type : ∀ a. a → a
*)
let fml_let_annot_4 =
  { name = "let_annot_4"
  ; term = (fml_id)
           (ML.Let ("y", forall_a_a_to_a, frozen "id", y))
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyVar 0)))
  ; vres = true
  }

(*
   term : let id = λx.x in let (choose : ∀a b. a → b → b) = λx.λy.x in choose id
   type : X
*)
let fml_let_annot_5 =
  { name = "let_annot_5"
  ; term = let_ ("id", abs "x" x,
      ML.Let ("choose", Some (TyForall (1, TyForall (2, TyArrow (TyVar 1,
                                             TyArrow (TyVar 2, TyVar 2))))),
                   abs "x" (abs "y" x), app choose id))
  ; typ  = None
  ; vres = true
  }

(*
   term: let (f : ∀ a. ∀ b. b → b) = λx.x in 1
   type: Int
*)
let fml_let_annot_6 =
  { name = "let_annot_6"
  ; term = ML.Let ( "f"
                  , Some (TyForall(1, TyForall (2, TyArrow (TyVar 2, TyVar 2))))
                  , abs "x" x
                  , one)
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term: let (f : ∀ a. ∀ a. a → a) = λx.x in 1
   type: Int
*)
let fml_let_annot_6_quantifier_shadowing =
  { name = "let_annot_6_quantifier_shadowing"
  ; term = ML.Let ( "f"
                  , Some (TyForall(1, TyForall (1, TyArrow (TyVar 1, TyVar 1))))
                  , abs "x" x
                  , one)
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term: let (f : ∀ a. ∀ b. b → b) = id in 1
   type: Int
*)
let fml_let_annot_7 =
  { name = "let_annot_7"
  ; term = (fml_id)
           (ML.Let ( "f"
                   , Some (TyForall(1, TyForall (2, TyArrow (TyVar 2, TyVar 2))))
                   , id
                   , one))
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term: let (f : ∀ a. ∀ a. a → a) = id in 1
   type: Int
*)
let fml_let_annot_7_quantifier_shadowing =
  { name = "let_annot_7_quantifier_shadowing"
  ; term = (fml_id)
           (ML.Let ( "f"
                   , Some (TyForall(1, TyForall (1, TyArrow (TyVar 1, TyVar 1))))
                   , id
                   , one))
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term: let (f : ∀ a. ∀ b. b → b) = ~id in 1
   type: X
*)
let fml_let_annot_8 ordered =
  { name = "let_annot_8"
  ; term = (fml_id)
           (ML.Let ( "f"
                   , Some (TyForall(1, TyForall (2, TyArrow (TyVar 2, TyVar 2))))
                   , frozen "id"
                   , one))
  ; typ  =
      if ordered then
        None
      else
        Some int_t
  ; vres = true
  }

(*
   term: let (f : ∀ a. ∀ a. a → a) = ~id in 1
   type: X
*)
let fml_let_annot_8_quantifier_shadowing ordered =
  { name = "let_annot_8_quantifier_shadowing"
  ; term = (fml_id)
           (ML.Let ( "f"
                   , Some (TyForall(1, TyForall (1, TyArrow (TyVar 1, TyVar 1))))
                   , frozen "id"
                   , one))
  ; typ  =
      if ordered then
        None
      else
        Some int_t
  ; vres = true
  }

(*
   term: let (f : ∀ a. a → Bool) = λ(x:Int).x = x in 1
   type: X
*)
let fml_let_annot_9 =
  { name = "let_annot_9"
  ; term = (fml_eq)
           (ML.Let ( "f"
                   , Some (TyForall(1, TyArrow (TyVar 1, bool_t)))
                   , ML.Abs ("x", Some int_t, eq x x)
                   , one))
  ; typ  = None
  ; vres = true
  }

(*
   term: let f = λ(x:Int).x = x in f
   type: Int → Bool
*)
let fml_let_annot_9_no_annot =
  { name = "let_annot_9_no_annot"
  ; term = (fml_eq)
           (ML.Let ( "f"
                   , None
                   , ML.Abs ("x", Some int_t, eq x x)
                   , f))
  ; typ  = Some (TyArrow (int_t, bool_t))
  ; vres = true
  }

(*
   term: let f : ∀a b. a → b → b =
           let g : ∀ b. a → b → b = λy.λz.z in id ~g
         in f
   type: None
   bug: #31

   Note: According to the FreezeML well-scopedness rules, this program is ill-scoped!
   The outer let binding does not generalize/bind a & b, meaning that they are not in scope in the inner one!
*)
let fml_let_annot_10 =
  { name = "let_annot_10"
  ; term = (fml_id)
           (ML.Let ( "f"
                   , Some (TyForall (1, TyForall (2, TyArrow (TyVar 1, TyArrow (TyVar 2, TyVar 2)))))
                   , ML.Let ( "g"
                            , Some (TyForall (2, TyArrow (TyVar 1, TyArrow (TyVar 2, TyVar 2))))
                            , ML.Abs ("y", Some (TyVar 1), abs "z" z)
                            , app id (frozen "g")
                            )
                   , f))
  ; typ  = None
  ; vres = true
  }

(*
   term : λx. choose ~id x
   type : X
*)
let fml_mono_binder_constraint_1 =
  { name = "mono_binder_constraint_1"
  ; term = (fml_choose << fml_id)
           (abs "x" (app (app choose (frozen "id")) x))
  ; typ  = None
  ; vres = true
  }

(*
   term : let f = λx.x 1 in f
   type : ∀ a. (Int → a) → a
*)
let fml_mono_binder_constraint_2 =
  { name = "mono_binder_constraint_2"
  ; term = let_ ("f", abs "x" (app (var "x") one), var "f")
  ; typ  = Some (TyForall ((), TyArrow (TyArrow (int_t, (TyVar 0)), TyVar 0)))
  ; vres = true
  }

(*
   term : (λ(f : ∀ a b. a → b → (a × b)). f 1 true) ~pair
   type : Int × Bool
*)
let fml_quantifier_ordering_1 =
  { name = "quantifier_ordering_1"
  ; term = (fml_pair)
           (app (ML.Abs ("f", Some (TyForall (1, TyForall (2,
                                      TyArrow (TyVar 1, TyArrow (TyVar 2,
                                      TyProduct (TyVar 1, TyVar 2))))))
                            , app (app (var "f") one) true_))
                (frozen "pair"))
  ; typ  = Some (TyProduct (int_t, bool_t))
  ; vres = true
  }

(*
   term : (λ(f : ∀ a b. a → b → (a × b)). f 1 true) ~pair'
   type : X
   bugs : #3
*)
let fml_quantifier_ordering_2 ordered =
  { name = "quantifier_ordering_2"
  ; term = (fml_pairprim)
           (app (ML.Abs ("f", Some (TyForall (1, TyForall (2,
                                      TyArrow (TyVar 1, TyArrow (TyVar 2,
                                      TyProduct (TyVar 1, TyVar 2))))))
                            , app (app (var "f") one) true_))
                (frozen "pair'"))
  ; typ  =
      if ordered then
        None
      else
        Some (TyProduct (int_t, bool_t))
  ; vres = true
  }

(*
   term : let pair' : ∀ b a. a → b → (a × b) = ~pair in ~pair'
   type : X
*)
let fml_quantifier_ordering_3 ordered =
  { name = "quantifier_ordering_3"
  ; term = (fml_pair)
           (ML.Let ( "pair'"
                    , Some (TyForall (2, TyForall (1,
                                     TyArrow (TyVar 1, TyArrow (TyVar 2,
                                     TyProduct (TyVar 1, TyVar 2))))))
                    , frozen "pair"
                    , frozen "pair'"))
  ; typ  =
      if ordered then
        None
      else
        Some (TyForall ((), TyForall ((),
                                     TyArrow (TyVar 0, TyArrow (TyVar 1,
                                     TyProduct (TyVar 0, TyVar 1))))))
  ; vres = true
  }

(*
   term : let pair' : ∀ b a. a → b → (a × b) = pair in ~pair'
   type : ∀ b a. a → b → (a × b)
*)
let fml_quantifier_ordering_4 =
  { name = "quantifier_ordering_4"
  ; term = (fml_pair)
           (ML.Let ( "pair'"
                    , Some (TyForall (2, TyForall (1,
                                     TyArrow (TyVar 1, TyArrow (TyVar 2,
                                     TyProduct (TyVar 1, TyVar 2))))))
                    , var "pair"
                    , frozen "pair'"))
  ; typ  = Some (TyForall ((), TyForall ((),
                                     TyArrow (TyVar 0, TyArrow (TyVar 1,
                                     TyProduct (TyVar 0, TyVar 1))))))
  ; vres = true
  }

(*
   term : let f = (λx.1) (λy.y) in ~f
   type : ∀ a. Int

  Note: this also looks very wrong!
*)

let fml_redundant_quantifiers_1 =
  { name = "quantifier_placement_3"
  ; term = let_ ("f",
                    app (abs "x" one) (abs "y" y),
                    frozen "f")
  ; typ  = Some int_t
  ; vres = true
  }

let fml_redundant_quantifiers_1_inferno =
  { name = fml_redundant_quantifiers_1.name
  ; term = fml_redundant_quantifiers_1.term
  ; typ  = Some (TyForall ((), int_t))
  ; vres = fml_redundant_quantifiers_1.vres
  }

(*
   term : let (x : (∀ a. a → a) → Int) = λ(f : ∀ a. a → a). f 1 in 1
   type : Int
   bugs : #2
*)
let fml_type_annotations_1 =
  { name = "type_annotations_1"
  ; term = ML.Let ("x",
                   Some (TyArrow (TyForall (1, TyArrow (TyVar 1, TyVar 1)),
                                  int_t)),
                   ML.Abs ("f", forall_a_a_to_a, app (var "f") one), one)
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term : let id = λx.x in ~id 1
   type : ∀ a. a → a
*)
let fml_id_appl =
  { name = "let_annot_1"
  ; term = let_ ("id", abs "x" x, app (frozen "id") one)
  ; typ  = None
  ; vres = true
  }

(*
   term : choose ~choose
   type : (∀ a. a → a → a) → (∀ a. a → a → a)
*)
let fml_choose_choose =
  { name = "choose_choose"
  ; term = (fml_choose)
           (app choose (frozen "choose"))
  ; typ  = Some (TyArrow
               ((TyForall ((), TyArrow (TyVar 0, TyArrow (TyVar 0, TyVar 0)))),
                (TyForall ((), TyArrow (TyVar 0, TyArrow (TyVar 0, TyVar 0))))))
  ; vres = true
  }

(*
   term : let f = choose ~choose in f ~choose
   type : ∀ a. a → a → a
*)
let fml_choose_choose_let =
  { name = "choose_choose_let"
  ; term = (fml_choose)
  (let_ ( "f"
           , app choose (frozen "choose")
           , app f (frozen "choose")))
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyArrow (TyVar 0, TyVar 0))))
  ; vres = true
  }

(*
   term : let (f : (∀ a. a → a → a) → (∀ a. a → a → a)) = choose ~choose
          in f ~choose
   type : ∀ a. a → a → a
*)
let fml_choose_choose_let_annot =
  { name = "choose_choose_let_annot"
  ; term = (fml_choose)
  (ML.Let ( "f"
          , Some (TyArrow
                ((TyForall (1, TyArrow (TyVar 1, TyArrow (TyVar 1, TyVar 1)))),
                 (TyForall (1, TyArrow (TyVar 1, TyArrow (TyVar 1, TyVar 1))))))
          , app choose (frozen "choose")
          , app (var "f") (frozen "choose")))
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyArrow (TyVar 0, TyVar 0))))
  ; vres = true
  }

(*
   term : (λ(f : (∀ a. a → a → a) → (∀ a. a → a → a)). f ~choose) (choose ~choose)
   type : ∀ a. a → a → a
*)
let fml_choose_choose_lambda =
  { name = "choose_choose_lambda"
  ; term = (fml_choose)
           (app (ML.Abs ( "f"
                        , Some (TyArrow
                                  ((TyForall (1, TyArrow (TyVar 1, TyArrow (TyVar 1, TyVar 1)))),
                                   (TyForall (1, TyArrow (TyVar 1, TyArrow (TyVar 1, TyVar 1))))))
                        , app f (frozen "choose")))
                (app choose (frozen "choose")))
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyArrow (TyVar 0, TyVar 0))))
  ; vres = true
  }

(*
   term : (λx.x) ~auto
   type : (∀ a. a → a) → (∀ a. a → a)
*)
let fml_id_auto_1 =
  { name = "id_auto_1"
  ; term = (fml_auto)
           (app (abs "x" x) (frozen "auto"))
  ; typ  = None
  ; vres = true
  }

(*
   term : (id (λx.x)) ~auto
   type : ∀ a. a → a
*)
let fml_id_auto_2 =
  { name = "id_auto_2"
  ; term = (fml_auto << fml_id)
           (app (app id (abs "x" x)) (frozen "auto"))
  ; typ  = None
  ; vres = true
  }

(*
   term: let (x : (∀ a. a → a) → Int) = λ(y: ∀ a. a → a)). 1 in
         let (z : ∀ b. b → b) = λw. w in
         x (~z)
   type: Int
*)
let fml_alpha_equiv_1 =
  { name = "alpha_equiv_1"
  ; term = ML.Let ( "x"
                  , Some (TyArrow (TyForall (1, TyArrow (TyVar 1, TyVar 1)), int_t))
                  , ML.Abs ( "y", forall_a_a_to_a, one)
                  , ML.Let ( "z"
                           , Some (TyForall (2, TyArrow (TyVar 2, TyVar 2)))
                           , abs "w" w
                           , app x (frozen "z")))
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term: let (x : (∀ a. ∀ b. a → a) → Int) = λ(y:∀ a. ∀ b. a → a). 1 in
         let (z : ∀ c. ∀ d. c → c) = λw. w in
         x (~z)
   type: Int
*)
let fml_alpha_equiv_2 =
  { name = "alpha_equiv_2"
  ; term = ML.Let ( "x"
                  , Some (TyArrow (TyForall (1, TyForall (2, TyArrow (TyVar 1, TyVar 1))), int_t))
                  , ML.Abs ( "y", Some (TyForall (1, TyForall (2, TyArrow (TyVar 1, TyVar 1)))), one)
                  , ML.Let ( "z"
                           , Some (TyForall(3, TyForall (4, TyArrow (TyVar 3, TyVar 3))))
                           , abs "w" w
                           , app x (frozen "z")))
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term: let (x : (∀ a.∀ b. b → b) → Int) = λ(y:∀ a. ∀ b. b → b). 1 in
         let (z : ∀ c.∀ d. d → d) = λw. w in
         x (~z)
   type: Int
*)
let fml_alpha_equiv_3 =
  { name = "alpha_equiv_3"
  ; term = ML.Let ( "x"
                  , Some (TyArrow (TyForall(1, TyForall (2, TyArrow (TyVar 2, TyVar 2))), int_t))
                  , ML.Abs ( "y", Some (TyForall (1, TyForall (2, TyArrow (TyVar 2, TyVar 2)))), one)
                  , ML.Let ( "z"
                           , Some (TyForall(3, TyForall (4, TyArrow (TyVar 4, TyVar 4))))
                           , abs "w" w
                           , app x (frozen "z")))
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term: let (x : (∀ a. ∀ a. a → a) → Int) = λy(y:∀ a. ∀ a. a → a). 1 in
         let (z : ∀ b. ∀ b. b → b) = λw. w in
         x (~z)
   type: Int
*)
let fml_alpha_equiv_4 =
  { name = "alpha_equiv_4"
  ; term = ML.Let ( "x"
                  , Some (TyArrow (TyForall(1, TyForall (1, TyArrow (TyVar 1, TyVar 1))), int_t))
                  , ML.Abs ("y", Some (TyForall(1, TyForall (1, TyArrow (TyVar 1, TyVar 1)))), one)
                  , ML.Let ("z"
                           , Some (TyForall (2, TyForall (2, TyArrow (TyVar 2, TyVar 2))))
                           , ML.Abs( "w", None, ML.Var("w"))
                           , ML.App (ML.Var "x", ML.FrozenVar "z")))
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term: let (x : (∀ a. ∀ a. a → a) → Int) = λ(y:∀ a.∀ a. a → a). 1 in
         let (z : ∀ a. ∀ b. a → a) = λw. w in
         x (~z)
   type: X
*)
let fml_alpha_equiv_5 ordered =
  { name = "alpha_equiv_5"
  ; term = ML.Let ( "x"
                  , Some (TyArrow (TyForall(1, TyForall (1, TyArrow (TyVar 1, TyVar 1))), int_t))
                  , ML.Abs ( "y", Some (TyForall (1, TyForall (1, TyArrow (TyVar 1, TyVar 1)))), one)
                  , ML.Let ( "z"
                           , Some (TyForall (1, TyForall (2, TyArrow (TyVar 1, TyVar 1))))
                           , abs "w" w
                           , app x (frozen "z")))
  ; typ  =
      if ordered then
        None
      else
        Some int_t
  ; vres = true
  }


(*
   term: let (x : ∀ a.(∀ b. a → a) → Int) = λ(y:∀ b. a → a). 1 in
         let (z : ∀ b. b → b) = λw. w in
         x (~z)
   type: X
*)
let fml_mixed_prefix_1 =
  { name = "mixed_prefix_1"
  ; term = ML.Let ( "x"
                  , Some (TyForall (1, TyArrow (TyForall (2, TyArrow (TyVar 1, TyVar 1)), int_t)))
                  , ML.Abs ( "y", Some( TyForall (2, TyArrow (TyVar 1, TyVar 1))), one)
                  , ML.Let ( "z"
                           , Some (TyForall (1, TyArrow (TyVar 1, TyVar 1)))
                           , abs "w" w
                           , app x (frozen "z")))
  ; typ  = None
  ; vres = true
  }

(*
   term: let (x : ∀ a.(∀ b. b → a) → Int) = λ(y:∀ b. b → a). 1 in
         let (z : ∀ b. b → Int) = λw. 1 in
         x (~z)
   type: Int
*)
let fml_mixed_prefix_2 =
  { name = "mixed_prefix_2"
  ; term = ML.Let ( "x"
                  , Some (TyForall (1, TyArrow (TyForall (2, TyArrow (TyVar 2, TyVar 1)), int_t)))
                  , ML.Abs ( "y", Some( TyForall(2, TyArrow (TyVar 2, TyVar 1))), one)
                  , ML.Let ( "z"
                           , Some (TyForall (1, TyArrow (TyVar 1, int_t)))
                           , abs "w" one
                           , app x (frozen "z")))
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term: let (x : ∀ a.(∀ b. b → a) → Int) = λ(y:∀ b. b → a). 1 in
         let z = λw. 1 in
         x (~z)
   type: Int
*)
let fml_mixed_prefix_2_no_sig =
  { name = "mixed_prefix_2_no_sig"
  ; term = ML.Let ( "x"
                  , Some (TyForall (1, TyArrow (TyForall (2, TyArrow (TyVar 2, TyVar 1)), int_t)))
                  , ML.Abs ( "y", Some( TyForall(2, TyArrow (TyVar 2, TyVar 1))), one)
                  , ML.Let ( "z"
                           , None
                           , abs "w" one
                           , app x (frozen "z")))
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term: (λx. let y : ∀ a. a → a = λz.x in y) 1 true
   type: X
*)
let fml_mixed_prefix_3 =
  { name = "mixed_prefix_3"
  ; term = app (app (abs "x" (ML.Let ("y", forall_a_a_to_a, abs "z" x, y))) one)
               true_
  ; typ  = None
  ; vres = true
  }

(*
   term: (λw. let y : ∀ a. a → a → Bool × Bool = λz:a.λx. (x = z, w = z)) in y)
         true 1 1
   type: X
*)
let fml_mixed_prefix_4 =
  { name = "mixed_prefix_4"
  ; term = (fml_eq)
           (app (app (app (abs "w"
             (ML.Let ("y"
                     , Some (TyForall (1, TyArrow (TyVar 1, TyArrow (TyVar 1,
                                 TyProduct (bool_t, bool_t)))))
                     , abs "z" (abs "x" (ML.Pair (eq x z, eq w z))), y))
           ) true_) one) one)
  ; typ  = None
  ; vres = true
  }

(*
   term: let (x : ∀ a.(∀ b. b → b) → Int) = λ(z:∀ b. b → b). 1 in
         let (y : ∀ a. a → a) = λw. w in
         x (~y)
   type: [∀ a.] Int

  Note: The type that inferno wants looks plain wrong
*)
let fml_poly_binding_1 =
  { name = "poly_binding_1"
  ; term = ML.Let ( "x"
                  , Some (TyForall (1, TyArrow (TyForall (2, TyArrow(TyVar 2, TyVar 2)), int_t)))
                  , ML.Abs ( "z", Some (TyForall (2, TyArrow (TyVar 2, TyVar 2))), one )
                  , ML.Let ( "y"
                           , Some (TyForall (1, TyArrow (TyVar 1, TyVar 1)))
                           , abs "w" w
                           , app x (frozen "y")))
  ; typ  = Some int_t
  ; vres = true
  }

let fml_poly_binding_1_inferno =
  { name = fml_poly_binding_1.name
  ; term = fml_poly_binding_1.term
  ; typ  = Some (TyForall ((), int_t))
  ; vres = fml_poly_binding_1.vres
  }

(*
   term: let (x : ∀ a. a → a) = λ(z : a). z in x 1
   type: Int
*)
let fml_poly_binding_2 =
  { name = "poly_binding_2"
  ; term = ML.Let ( "x"
                  , Some (TyForall (2, TyArrow (TyVar 2, TyVar 2)))
                  , ML.Abs ("z", Some (TyVar 2), z)
                  , app x one)
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term: let (x : ∀ a. (∀ b. a → b) → Int) = λ(z : (∀ b. a → b)). 1 in 1
   type: Int
*)
let fml_poly_binding_3 =
  { name = "poly_binding_3"
  ; term = ML.Let ( "x"
                  , Some (TyForall (1, (TyArrow (TyForall (2, TyArrow (TyVar 1, TyVar 2)), int_t))))
                  , ML.Abs ("z", Some (TyForall (2, TyArrow (TyVar 1, TyVar 2))), one)
                  , one)
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term: let (x : ∀ a. (∀ b. a → b → Int) → Int) = λ(z : (∀ b. a → b → Int)). 1 in 1
   type: Int
*)
let fml_poly_binding_4 =
  { name = "poly_binding_4"
  ; term = ML.Let ( "x"
                  , Some (TyForall (1, (TyArrow (TyForall (2, TyArrow (TyVar 1, TyArrow (TyVar 2, int_t))), int_t))))
                  , ML.Abs ("z", Some (TyForall (2, TyArrow (TyVar 1, TyArrow (TyVar 2, int_t)))), one)
                  , one)
  ; typ  = Some int_t
  ; vres = true
  }

(*
   term: let x : ∀ a. (a → a) → (a → a) = let y : a → a = λw.w
                                          in λz.y
         in x id_int
   type: Int → Int
*)
let fml_scoped_tyvars_1 =
  { name = "scoped_tyvars_1"
  ; term = (fml_id_int)
           (ML.Let ( "x"
                  , Some (TyForall (1, TyArrow( TyArrow (TyVar 1, TyVar 1),TyArrow(TyVar 1, TyVar 1))))
                  , ML.Let ( "y"
                           , Some (TyArrow (TyVar 1, TyVar 1))
                           , abs "w" w
                           , abs "z" y)
                  , app x (var "id_int")
             ))
  ; typ  = Some (TyArrow (int_t, int_t))
  ; vres = true
  }

(*
   term : let id = (λx.x) in id ~id
   type : ∀ a. a → a
*)
let fml_mono_gen_test1 =
  { name = "mono_test"
  ; term = ML.Let ("id", None, abs "x" x, app id (frozen "id"))
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyVar 0)))
  ; vres = true
  }

(*
   term : let (id : ∀ a. a → a) = (λx.x) in id ~id
   type : ∀ a. a → a
*)
let fml_mono_gen_test2 =
  { name = "fml_skolem_with_non_skolem"
  ; term =  ML.Let ("id", forall_a_a_to_a,
              (abs "x" x),
              app id (frozen "id"))
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyVar 0)))
  ; vres = true
  }

(*
   Like e3, but no type annotation on the lambda defining r

   term : let r : (∀ a. a → (∀ b. b → b)) → Int = λx.1 in
          r $(λx.$(λy.y))
   type : X
 *)
let fml_e3_dot_no_lambda_sig =
  { name = "no_lambda_sig_E3∘"
  ; term = ML.Let ("r", Some (TyArrow (TyForall (1, TyArrow (TyVar 1,
                               TyForall (2, TyArrow (TyVar 2, TyVar 2)))), int_t)),
                        abs "x" one,
                   app (var "r") (gen (abs "x" (gen (abs "y" y)))))
  ; typ  = None
  ; vres = true
  }

(*
   term : revapp ~id
   type : ∀ b. ((∀ a. a → a) → b) → b
*)
let fml_free_unification_vars_1 =
  { name = "free_unification_vars_1"
  ; term = (fml_id << fml_revapp)
           (app (var "revapp") (frozen "id"))
  ; typ  = Some (TyForall ((), TyArrow (TyArrow
                (TyForall ((), TyArrow (TyVar 0, TyVar 0)), TyVar 0), TyVar 0)))
  ; vres = true
  }

(*
   term : let f = revapp ~id in f
   type : ∀ b. ((∀ a. a → a) → b) → b
*)
let fml_free_unification_vars_2 =
  { name = "free_unification_vars_2"
  ; term = (fml_id << fml_revapp)
           (let_ ("f", (app (var "revapp") (frozen "id")), f))
  ; typ  = Some (TyForall ((), TyArrow (TyArrow
                (TyForall ((), TyArrow (TyVar 0, TyVar 0)), TyVar 0), TyVar 0)))
  ; vres = true
  }

(*
   term : let f = id id in f ~id
   type : X
*)
let fml_value_restriction_1 =
  { name = "fml_value_restriction_1"
  ; term = (fml_id)
           (let_ ("f", (app id id), app f (frozen "id")))
  ; typ  = None
  ; vres = true
  }

(*
   term : let f = let g = 1
                  in id id
          in f ~id
   type : X
   bug  : #27
*)
let fml_value_restriction_2 =
  { name = "fml_value_restriction_2"
  ; term = (fml_id)
           (let_ ("f", let_ ("g", one, (app id id)), app f (frozen "id")))
  ; typ  = None
  ; vres = true
  }

(*
   term : let f = id id in poly ~f
   type : X
   bug  : #35
*)
let fml_value_restriction_3 =
  { name = "fml_value_restriction_3"
  ; term = (fml_id << fml_poly)
           (let_ ("f", (app id id), app poly (frozen "f")))
  ; typ  = None
  ; vres = true
  }

(*
   term : let (f : ∀ a. int) = 1 in ~f
   type : ∀ a. int
*)
let fml_redundant_quantifier_1 =
  { name = "fml_redundant_quantifier_1"
  ; term = ML.Let ("f", Some (TyForall (1, int_t)), one, (frozen "f"))
  ; typ  = Some (TyForall ((), int_t))
  ; vres = true
  }

(*
   term : let (f : ∀ a b. a -> a) =  λx in ~f
   type : ∀ a b. a -> a
*)
let fml_redundant_quantifier_2 =
  { name = "fml_redundant_quantifier_2"
  ; term = ML.Let ("f", Some (TyForall (1, TyForall (2, TyArrow (TyVar 1, TyVar 1)))), abs "x" x, (frozen "f"))
  ; typ  = Some (TyForall ((), TyForall ((), TyArrow (TyVar 1, TyVar 1))))
  ; vres = true
  }


let shared_good_tests test ordered = [
  test env_test;


  (* PLDI paper examples *)

  (* a1 is added as per-implementation test *)
  (* a1_dot is added as per-implementation test *)
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
  (* fml_inst_3 seems inferno-specfic *)
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
  test (fml_let_annot_8 ordered);
  test (fml_let_annot_8_quantifier_shadowing ordered);
  test fml_let_annot_9;
  test fml_let_annot_9_no_annot;


  test fml_mono_binder_constraint_1;
  test fml_mono_binder_constraint_2;

  test fml_quantifier_ordering_1;
  test (fml_quantifier_ordering_2 ordered);
  test (fml_quantifier_ordering_3 ordered);
  test fml_quantifier_ordering_4;

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
  test (fml_alpha_equiv_5 ordered);

  test fml_mixed_prefix_1;
  test fml_mixed_prefix_2;
  test fml_mixed_prefix_2_no_sig;
  test fml_mixed_prefix_3;
  test fml_mixed_prefix_4;

  (* fml_poly_binding_1 has an inferno-specific version *)
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

  test fml_redundant_quantifier_1;
  test fml_redundant_quantifier_2;
]

let inferno_tests_known_broken handle =
  [
  handle fml_let_annot_10;
  handle fml_value_restriction_3
]

let inferno_dedicated_tests test =
[ (* Some of these tests behave very weirdly ... *)
  test a1_inferno_order;
  test a1_dot_inferno_order;
  test fml_inst_3_inferno;
  test fml_redundant_quantifiers_1_inferno;
  test fml_poly_binding_1_inferno
]


let inferno_implementation_tests good_test known_broken_test =
  shared_good_tests good_test false @ inferno_dedicated_tests good_test
  @ inferno_tests_known_broken  known_broken_test


let naive_dedicated_tests test =
[
  test a1_correct_order;
  test a1_dot_correct_order;
  test fml_inst_3;
  test fml_redundant_quantifiers_1;
  test fml_poly_binding_1;

  (* broken in inferno *)
  test fml_value_restriction_3
]

let naive_implementation_tests ordered =
  shared_good_tests Fun.id ordered @ naive_dedicated_tests Fun.id
