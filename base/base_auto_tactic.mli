(*
 * We define a simple auto tactic, where it
 * is possible to add tactics to be tried by the auto tactic.
 *
 * This is the simple-minded auto tactic.  Each tactic
 * is given a precedence, and the tactics are ordered
 * by their precedences before they are tried.
 *
 * The trivialT tactic is like autoT, but it is intended
 * that trivialT either proves the goal or fails.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

include Mptop

open Refiner.Refiner.TermType

open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent

(*
 * The info provided is a name,
 * a precedence, and a function
 * to produce a tactic.  The function
 * is called once per run of the auto tactic.
 *
 * One problem we have is that some tactics
 * may wish to keep some state.  The type system
 * won't allow us to make the struct polymorphic,
 * so we have the tactic produce a tactic
 * and a continuation.
 *)
type auto_tac =
   AutoTac of (tactic_arg -> (tactic * auto_tac) list)

type auto_prec

type 'a auto_info =
   { auto_name : string;
     auto_prec : auto_prec;
     auto_tac : 'a
   }

(*
 * The string is for debugging.
 *)
resource (tactic auto_info, tactic) trivial
resource (auto_tac auto_info, tactic) auto

val process_trivial_resource_annotation :
   (Tactic.pre_tactic * auto_prec, tactic auto_info) annotation_processor
val process_auto_resource_annotation :
   (Tactic.pre_tactic * auto_prec, auto_tac auto_info) annotation_processor

(*
 * Operations on precedences.
 * The create operation takes a list of precedences that
 * are smaller, and another list that are larger.
 *)
val create_auto_prec : auto_prec list -> auto_prec list -> auto_prec

(*
 * Trivial is used by autoT.
 *)
val trivial_prec : auto_prec

(*
 * Trivial tactic.
 *)
topval trivialT : tactic

(*
 * The inherited tactic.
 *)
topval autoT : tactic

(*
 * Short for tryT (completeT autoT)
 *)
topval tryAutoT : tactic -> tactic

(*
 * Most times, a normal tactic is passed as auto_tac.
 * This wrapper converts it.
 *)
val auto_wrap : tactic -> auto_tac

(*
 * At other times, the search algorithm may want to
 * make sure the same configuration does not occur.
 * This wrapper will keep track of the sequents
 * seen, and fail if a sequent has been seen before.
 *)
val auto_progress : tactic -> auto_tac
val auto_hyp_progress : (int -> tactic_arg -> bool) -> (int -> tactic) -> auto_tac
val auto_assum_progress : (int -> tactic_arg -> bool) -> (int -> tactic) -> auto_tac

topval byDefT: conv -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
