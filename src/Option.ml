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

let iter f o =
  match o with
  | None ->
      ()
  | Some x ->
      f x

let fold f o accu =
  match o with
  | None ->
      accu
  | Some x ->
      f x accu

let map f o =
  match o with
  | None ->
      None
  | Some x ->
      Some (f x)

let multiply m o1 o2 =
  match o1, o2 with
  | None, o
  | o, None ->
      o
  | Some x1, Some x2 ->
      Some (m x1 x2)

let is_none = function
  | None   -> true
  | Some _ -> false

let is_some = function
  | None   -> false
  | Some _ -> true
