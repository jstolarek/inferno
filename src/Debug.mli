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

(* Debugging facilities *)

(* Toggle debugging messages. *)
val enabled : bool

(* Toggle very detailed messages.  You want this if things go very wrong.  Only
   takes effect when [enabled] is true. *)
val hard : bool

(* Toggle rank display when printing variables. *)
val print_ranks : bool

(* Printing fuel.  Used to limit the size of printed types.  Also required to
   avoid crashing in the presence of cyclic types. *)
val fuel : int

(* Print a string to stderr. *)
val print_str : string -> unit

(* Print a document to stderr. *)
val print : PPrint.document -> unit
