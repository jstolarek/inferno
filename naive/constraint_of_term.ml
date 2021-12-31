open Core

let translate term ty =
  let fresh = Tyvar.fresh_tyvar in
  let rec for_lambda arg_ty ret_ty fun_ty tevar term =
    let open Constraint in
    And
      ( Equiv (Types.TyArrow (arg_ty, ret_ty), fun_ty),
        Def (tevar, arg_ty, transl term ret_ty) )
  and transl term ty =
    match term with
    | Term.Var x -> Constraint.Inst (x, ty)
    | Term.FrozenVar x -> Constraint.Freeze (x, ty)
    | Term.App (m, n) ->
        let a1 = fresh () in
        let a1t = Types.TyVar a1 in
        Constraint.Exists
          (a1, Constraint.And (transl m (Types.TyArrow (a1t, ty)), transl n a1t))
    | Term.Abs (x, None, m) ->
        let a1 = fresh () in
        let a2 = fresh () in
        let a1t = Types.TyVar a1 in
        let a2t = Types.TyVar a2 in
        Constraint.exists ([ a1; a2 ], for_lambda a1t a2t ty x m)
    | Term.Abs (x, Some annot_ty, m) ->
        let a1 = fresh () in
        let a1t = Types.TyVar a1 in
        Constraint.Exists (a1, for_lambda annot_ty a1t ty x m)
    | Term.Let (x, None, m, n) ->
        let restriction = if Term.is_gval m then Types.Poly else Types.Mono in
        let a1 = fresh () in
        let a1t = Types.TyVar a1 in
        Constraint.Let (restriction, x, a1, transl m a1t, transl n ty)
    | Term.Let (x, Some annot_ty, m, n) when Term.is_gval m ->
        let qs, guarded_ty = Types.split_toplevel_quantifiers annot_ty in
        let conj1 = Constraint.forall (qs, transl m guarded_ty) in
        let conj2 = Constraint.Def (x, annot_ty, transl n ty) in
        Constraint.And (conj1, conj2)
    | Term.Let (x, Some annot_ty, m, n) ->
        let conj1 = transl m annot_ty in
        let conj2 = Constraint.Def (x, annot_ty, transl n ty) in
        Constraint.And (conj1, conj2)
    | Term.Pair (m, n) ->
        let a1 = fresh () in
        let a2 = fresh () in
        let a1t = Types.TyVar a1 in
        let a2t = Types.TyVar a2 in
        Constraint.exists
          ( [ a1; a2 ],
            Constraint.conj
              [
                Constraint.Equiv (Types.TyProduct (a1t, a2t), ty);
                transl m a1t;
                transl n a2t;
              ] )
    | Term.Proj (i, prod) ->
        let a1 = fresh () in
        let a2 = fresh () in
        let a1t = Types.TyVar a1 in
        let a2t = Types.TyVar a2 in
        Constraint.exists
          ( [ a1; a2 ],
            Constraint.conj
              [
                transl prod (Types.TyProduct (a1t, a2t));
                (match i with
                | 1 -> Constraint.Equiv (a1t, ty)
                | 2 -> Constraint.Equiv (a2t, ty)
                | _ -> failwith "illegal index in projection");
              ] )
    | Term.Int _ -> Constraint.Equiv (Types.Builtin.int, ty)
    | Term.Bool _ -> Constraint.Equiv (Types.Builtin.bool, ty)
  in

  transl term ty
