type errors =
  | Unification_clash_failure
  | Unification_occurs_failure
  | Quantifier_escape
  | Cannot_monomorphise
      [@@deriving sexp]
