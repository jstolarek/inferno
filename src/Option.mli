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

val iter: ('a -> unit) -> 'a option -> unit

val fold: ('a -> 'b -> 'b) -> 'a option -> 'b -> 'b

val map: ('a -> 'b) -> 'a option -> 'b option

val multiply: ('a -> 'a -> 'a) -> 'a option -> 'a option -> 'a option

val is_none: 'a option -> bool

val is_some: 'a option -> bool
