(*!
 * @spelling{arg tac}
 *
 * @begin[doc]
 * @theory[Base_auto_tactic]
 *
 * The @tt{Base_auto_tactic} module defines two of the most useful
 * tactics in the @MetaPRL prover.  The @tactic[autoT] tactic attempts
 * to prove a goal ``automatically,'' and the @tactic[trivialT] tactic
 * proves goals that are ``trivial.''  Their implementations are surprisingly
 * simple---all of the work in automatic proving is implemented in
 * descendent theories.
 *
 * This module describes the @emph{generic} implementation of the
 * @hreftactic[autoT] and @hreftactic[trivialT] tactics.  They are implemented
 * using a resource
 * containing collections of tactics that are added by descendent theories.
 * The @Comment!resource[auto_resource] builds collections of tactics specified by
 * a data structure with the following type:
 *
 * @begin[center]
 * @begin[verbatim]
 * type auto_info =
 *    { auto_name : string;
 *      auto_prec : auto_prec;
 *      auto_tac : tactic;
 *      auto_type : auto_type;
 *    }
 *
 * and auto_type =
 *    AutoTrivial
 *  | AutoNormal
 *  | AutoComplete
 * @end[verbatim]
 * @end[center]
 *
 * The @tt{auto_name} is the name used to describe the entry (for
 * debugging purposes).  The @tt{auto_tac} is a function that takes
 * the current goal (the @tt{tactic_arg}) and provides a tactic that
 * can be applied to the goal, and a new @tt{auto_tac} that can be
 * used on the subgoals.  The entries are divided into precedence
 * levels; tactics with higher precedence are applied first.
 *
 * Finally, @tt{auto_type} specifies how @hreftactic[autoT] and @hreftactic[trivialT]
 * will use each particular entry. @tt{AutoTrivial} entries are the only ones
 * used by @hreftactic[trivialT]; @hreftactic[autoT] attempts using them before
 * any other entries. @tt{AutoComplete} will be used by @hreftactic[autoT] after
 * all @tt{AutoTrivial} and @tt{AutoNormal} entries are ehausted. @hreftactic[autoT]
 * will consider an application of an @tt{AutoComplete} entry to be successfull
 * only if it would be able to completely prove all subgoals generated by it.
 *
 * This theory also defines the @tactic[byDefT] tactic. @tt{byDefT }@i{conv}
 * (where @i{conv} is usially an @tt{unfold_} conversional) uses @i{conv}
 * (through @hrefconv[higherC]) on all the assumptions and on the goal and then
 * calls @hreftactic[autoT].
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * Author: Jason Hickey @email{jyh@cs.caltech.edu}
 * Modified by: Aleksey Nogin @email{nogin@cs.cornell.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Mptop
(*! @docoff *)

open Printf
open Mp_debug
open Dag
open Imp_dag
open String_set

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Top_conversionals
open Mptop

(*
 * Debugging.
 *)
let _ =
   show_loading "Loading Base_auto_tactic%t"

let debug_auto =
   create_debug (**)
      { debug_name = "auto";
        debug_description = "Display auto tactic operations";
        debug_value = false
      }

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * The auto tactic just produces a list of tactics to try.
 *)
type auto_prec = unit ImpDag.node

(*
 * The info provided is a name,
 * a precedence, and a function
 * to produce a tactic.  The function
 * is called once per run of the auto tactic.
 *)
type auto_info = {
   auto_name : string;
   auto_prec : auto_prec;
   auto_tac : tactic;
   auto_type : auto_type;
}

and auto_type =
   AutoTrivial
 | AutoNormal
 | AutoComplete

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * We create a DAG to manage ordering in the tree.
 *)
let dag = ImpDag.create ()

(*
 * Sort the nodes in the list.
 *)
let compare node1 node2 =
   ImpDag.node_rel dag node1.auto_prec node2.auto_prec = LessThan

let auto_tac tac = tac.auto_tac

let sort_nodes = Sort.list compare

(*
 * Debugging firstT.
 *)
let debugT auto_tac =
   let tac p =
      eprintf "Auto: trying %s%t" auto_tac.auto_name eflush;
      let res = (progressT auto_tac.auto_tac) p in
         eprintf "\t success!%t" eflush;
         res
   in
      { auto_tac with auto_tac = tac }

let map_progressT tac =
   { tac with auto_tac = progressT tac.auto_tac }

let trivialP  tac = (tac.auto_type == AutoTrivial)
let normalP   tac = (tac.auto_type == AutoNormal)
let completeP tac = (tac.auto_type == AutoComplete)

(*
 * Build an auto tactic from all of the tactics given.
 * A list of tactics to try is constructed.
 * The earlier tactics should be tried first.
 *)
let make_progressT goals tac p =
   let goal = Sequent.goal p in
   if List.exists (alpha_equal goal) goals then idT p
   else tac (goal::goals) p

let extract tactics =
   let tactics =
      if !debug_auto then List.map debugT tactics
      else List.map map_progressT tactics
   in
   let trivial = sort_nodes (List.filter trivialP tactics) in
   let normal = sort_nodes (List.filter normalP tactics) in
   let complete = sort_nodes (List.filter completeP tactics) in
   if !debug_auto then begin
      let names tacs = String.concat "; " (List.map (fun t -> t.auto_name) tacs) in
      eprintf "Auto tactics:\n\tTrivial: %s\n\tNormal: %s\n\tComplete: %s%t"
         (names trivial) (names normal) (names complete) eflush;
   end;
   let make_progress_first reset next =
      let rec prog_first tacs goals =
         match tacs with
            [] ->
               next goals
          | tac :: tacs ->
               (tac.auto_tac thenT (make_progressT goals prog_reset)) orelseT
                  (prog_first tacs goals)
      and prog_reset goals = prog_first reset goals
      in
         prog_first
   in
   let next_idT _ = idT in
   let gen_trivT next = make_progress_first trivial next trivial [] in
   let trivT = gen_trivT next_idT in
   let gen_normT next = gen_trivT (make_progress_first (trivial @ normal) next normal) in
   let all_tacs = trivial @ normal @ complete in
   let try_complete goals = tryT (completeT (make_progress_first all_tacs next_idT complete goals)) in
   let autoT = gen_normT try_complete in
   let strongAutoT = make_progress_first all_tacs next_idT all_tacs [] in
      (trivT, autoT, strongAutoT)

let improve_resource data info = info::data

(*
 * Resource.
 *)
let resource auto = Functional {
   fp_empty = [];
   fp_add = improve_resource;
   fp_retr = extract
}

(*
 * Create a precedence.
 *)
let create_auto_prec before after =
   let node = ImpDag.insert dag () in
      List.iter (fun p -> ImpDag.add_edge dag p node) before;
      List.iter (fun p -> ImpDag.add_edge dag node p) after;
      node

(*
 * Use the tactic as long as progress is being made.
 *)
let rec check_progress goal = function
   goal' :: goals ->
      if alpha_equal goal goal' then
         true
      else
         check_progress goal goals
 | [] ->
      false

(*
 * Actual tactics.
 *)
let trivialT p =
   let trivT, _, _ = get_resource_arg p get_auto_resource in
      trivT p

let autoT p =
   let _, autoT, _ = get_resource_arg p get_auto_resource in
      autoT p

let strongAutoT p =
   let _, _, sAutoT = get_resource_arg p get_auto_resource in
      sAutoT p

let tcaT = tryT (completeT strongAutoT)

let tryAutoT tac =
   tac thenT tcaT

let byDefT conv =
   rwhAllAll (conv thenC reduceC) thenT autoT

(*
 * Trivial is in auto tactic.
 *)
let trivial_prec = create_auto_prec [] []

(*
 * Some trivial tactics.
 *)
let resource auto += {
   auto_name = "nthAssumT";
   auto_prec = trivial_prec;
   auto_tac = onSomeAssumT nthAssumT;
   auto_type = AutoTrivial;
}

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
