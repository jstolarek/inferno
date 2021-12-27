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

 type 'a t =
   | WellTyped of 'a
   | IllTyped
   | ImplementationBug
