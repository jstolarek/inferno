(* open Core *)

(* type t = (Tyvar.t, Types.t, Tyvar.comparator_witness) Map.t *)

(* let empty = Map.empty (module Tyvar) *)
(* let get (subst : t) var = Map.find_exn subst var *)
(* let set = Map.set *)

(* let range_contains subst rigid_vars var = *)
(*   let ftv ty = Types.free_flexible_variables ty rigid_vars in *)
(*   Map.exists subst ~f:(fun ty -> Tyvar.Set.mem (ftv ty) var) *)

(* let can_demote (subst : t) rigid_vars flex_mono_vars vars_to_check = *)
(*   let rec cd var = *)
(*     Types.is_monomorphic (get subst var) rigid_vars flex_mono_vars *)
(*   in *)
(*   Set.for_all vars_to_check ~f:cd *)
