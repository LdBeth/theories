(*
 * Primitiva axiomatization of implication.
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

include Czf_itt_sep
include Czf_itt_set_ind

open Printf
open Mp_debug

open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent
open Var

open Itt_logic
open Itt_rfun

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_dexists%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "dexists"{'T; x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_dexists : "dexists"{'s; x. 'A['x]} <-->
   set_ind{'s; T, f, g. x: 'T * 'A['f 'x]}

interactive_rw reduce_dexists : "dexists"{collect{'T; x. 'f['x]}; y. 'A['y]} <-->
   (t: 'T * 'A['f['t]])

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform dexists_df : mode[prl] :: parens :: "prec"[prec_lambda] :: "dexists"{'s; x. 'A} =
   pushm[0] Nuprl_font!"exists" slot{'x} " " Nuprl_font!member " " slot{'s} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive dexists_type 'H 'y :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."dexists"{'s; x. 'A['x]}} }

(*
 * Intro.
 *)
interactive dexists_intro 'H 'z 'w :
   sequent [squash] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- member{'z; 's} } -->
   sequent ['ext] { 'H >- 'A['z] } -->
   sequent ['ext] { 'H >- "dexists"{'s; x. 'A['x]} }

(*
 * Elimination.
 *)
interactive dexists_elim 'H 'J 'x 'z 'v 'w :
   sequent ['ext] { 'H; x: "dexists"{'s; y. 'A['y]}; 'J['x] >- isset{'s} } -->
   sequent ['ext] { 'H; x: "dexists"{'s; y. 'A['y]}; 'J['x]; z: set >- "type"{'A['z]} } -->
   sequent ['ext] { 'H; x: "dexists"{'s; y. 'A['y]}; 'J['x] >- fun_prop{z. 'A['z]} } -->
   sequent ['ext] { 'H;
                    x: "dexists"{'s; y. 'A['y]};
                    'J['x];
                    z: set;
                    v: member{'z; 's};
                    w: 'A['z]
                    >- 'C['x]
                  } -->
   sequent ['ext] { 'H; x: "dexists"{'s; y. 'A['y]}; 'J['x] >- 'C['x] }

(*
 * This is a restricted formula.
 *)
interactive dexists_res 'H 'w 'x :
   sequent ['ext] { 'H; w: set; x: set >- "type"{'B['w; 'x]} } -->
   sequent ['ext] { 'H >- fun_set{w. 'A['w]} } -->
   sequent ['ext] { 'H >- restricted{z, y. 'B['z; 'y]} } -->
   sequent ['ext] { 'H >- restricted{z. "dexists"{'A['z]; y. 'B['z; 'y]}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Propositional reasoning.
 *)
let d_dexistsT i p =
   if i = 0 then
      let z = get_with_arg p in
      let w = maybe_new_vars1 p "v" in
         (dexists_intro (hyp_count_addr p) z w
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main";
                  addHiddenLabelT "antecedent"]) p
   else
      let x, _ = nth_hyp p i in
      let z, v, w = Var.maybe_new_vars3 p "u" "v" "w" in
      let i, j = hyp_indices p i in
         (dexists_elim i j x z v w
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p

let dexists_term = << "dexists"{'T; x. 'A['x]} >>

let d_resource = Mp_resource.improve d_resource (dexists_term, d_dexistsT)

(*
 * Typehood.
 *)
let d_dexists_typeT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         (dexists_type (hyp_count_addr p) v thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_desists_typeT", StringError "no elimination form"))

let dexists_type_term = << "type"{."dexists"{'s; z. 'A['z]}} >>

let d_resource = Mp_resource.improve d_resource (dexists_type_term, d_dexists_typeT)

(*
 * Restricted.
 *)
let d_dexists_resT i p =
   if i = 0 then
      let u, v = maybe_new_vars2 p "u" "v" in
         (dexists_res (hyp_count_addr p) u v
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p
   else
      raise (RefineError ("d_dexists_res", StringError "no elimination form"))

let dexists_res_term = << restricted{z. "dexists"{'s; y. 'A['y; 'z]}} >>

let d_resource = Mp_resource.improve d_resource (dexists_res_term, d_dexists_resT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
