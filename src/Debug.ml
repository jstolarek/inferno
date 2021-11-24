(******************************************************************************)
(*                                                                            *)
(*                             Frozen Inferno                                 *)
(*                                                                            *)
(*                    Jan Stolarek, University of Edinburgh                   *)
(*                                                                            *)
(*  Copyright University of Edinburgh. All rights reserved. This file is      *)
(*  distributed under the terms of the MIT License, as described in the       *)
(*  file LICENSE.                                                             *)
(*                                                                            *)
(******************************************************************************)

(* -------------------------------------------------------------------------- *)

(* Tweak settings in this section according to debugging needs.  See interface
   file for details. *)

let enabled     = false
let hard        = false
let print_ranks = true
let fuel        = 8

(* -------------------------------------------------------------------------- *)

let print_str message =
  if enabled then prerr_endline message;
  flush stderr

let print doc =
  if enabled then
    PPrint.(ToChannel.pretty 0.9 80 stderr (doc ^^ hardline));
  flush stderr

let hard = enabled && hard
