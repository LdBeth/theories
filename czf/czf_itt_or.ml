(*
 * Primitiva interactiveatization of implication.
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

open Printf
open Mp_debug

open Refiner.Refiner.RefineError
open Mp_resource

open Tacticals
open Conversionals
open Sequent
open Var

open Itt_logic
open Itt_rfun

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_or%t" eflush

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Implication is restricted.
 *)
interactive union_fun 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "union"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive union_res 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "union"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive or_fun 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "or"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive or_res 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "or"{'A['x]; 'B['x]}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Restricted.
 *)
let d_union_funT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         union_fun (hyp_count_addr p) z p
   else
      raise (RefineError ("d_union_funT", StringError "no elimination form"))

let union_fun_term = << fun_prop{z. "union"{'P1['z]; 'P2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (union_fun_term, d_union_funT)

(*
 * Restricted.
 *)
let d_union_resT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         union_res (hyp_count_addr p) z p
   else
      raise (RefineError ("d_union_resT", StringError "no elimination form"))

let union_res_term = << restricted{z. "union"{'P1['z]; 'P2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (union_res_term, d_union_resT)

(*
 * Restricted.
 *)
let d_or_funT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         or_fun (hyp_count_addr p) z p
   else
      raise (RefineError ("d_or_funT", StringError "no elimination form"))

let or_fun_term = << fun_prop{z. "or"{'P1['z]; 'P2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (or_fun_term, d_or_funT)

(*
 * Restricted.
 *)
let d_or_resT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         or_res (hyp_count_addr p) z p
   else
      raise (RefineError ("d_or_resT", StringError "no elimination form"))

let or_res_term = << restricted{z. "or"{'P1['z]; 'P2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (or_res_term, d_or_resT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
