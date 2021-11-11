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

val enabled     : bool
val hard        : bool
val print_ranks : bool
val print_repr  : bool
val fuel        : int

val print_str : string -> unit
val print     : PPrint.document -> unit
