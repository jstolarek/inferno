open Core

type tevar = Tevar.t [@@deriving sexp]

type t = Shared.Ml.term =
  | Var of tevar
  | FrozenVar of tevar
  | Abs of tevar * Types.t option * t
  | App of t * t
  | Let of tevar * Types.t option * t * t
  | Pair of t * t
  | Proj of int * t
  | Int of int
  | Bool of bool

let is_val = Shared.Ml.is_val
let is_gval = Shared.Ml.is_gval

let type_variables term =
  let rec collect vars = function
    | Abs (_, ty_opt, m) ->
        let vars =
          Option.value_map ~default:Tyvar.Set.empty ~f:Types.all_variables
            ty_opt
          |> Set.union vars
        in
        collect vars m
    | Let (_, ty_opt, m, n) ->
        let vars =
          Option.value_map ~default:Tyvar.Set.empty ~f:Types.all_variables
            ty_opt
          |> Set.union vars
        in
        Shared.Logging.log_sexp "variables in let annot:%s\n"
          (Tyvar.Set.sexp_of_t vars);
        collect (collect vars m) n
    | App (m, n) | Pair (m, n) -> collect (collect vars m) n
    | Proj (_, m) -> collect vars m
    | _ -> vars
  in

  collect Tyvar.Set.empty term
