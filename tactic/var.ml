doc <:doc< 
   @begin[doc]
   @module[Var]
  
   The @tt[Var] module provides utilities to
   generate new variables that are guaranteed to be distinct
   from all other bound variables in a proof goal.  For example,
   the @tt[productElimination] (Section @refmodule[Itt_dprod])
   rule, splits a hypothesis of the form $x@colon T_1 @times T_2$
   into two hypotheses $u@colon T_1$ and $v@colon T_2$.  The variables
   $u$ and $v$ have to be chosen at rule application time, and this
   module assists in the generation of new names.
  
   There are three basic functions implemented here.
   @begin[verbatim]
   val new_var         : string -> string list -> string
   val maybe_new_var   : string -> string list -> string
   val maybe_new_vars  : string list -> string list -> string list
   @end[verbatim]
  
   The function $@tt[new_var]@space v@space @i[vars]$ generates a new variable
   ``similar'' to $v$, but not contained in $@i[vars]$.  In this
   case ``similar'' means that the variable has the same name, but
   it may have a numerical suffix to make it distinct.
   @end[doc]
  
   ----------------------------------------------------------------
  
   @begin[license]
  
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.
  
   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.
  
   Copyright (C) 1998 Jason Hickey, Cornell University
  
   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.
  
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
  
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
  
   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
  
   @end[license]
>>

doc <:doc< 
   @begin[doc]
   @parents
   @end[doc]
>>
extends Summary
doc <:doc< @docoff >>

open Refiner.Refiner.Term
open Refiner.Refiner.RefineError

open Printf
open Mp_debug
open String_util

open Tactic_type

(*
 * Debug statement.
 *)
let _ =
   show_loading "Loading Var%t"

(*
 * Split a varname into root, suffix
 * according to the pattern %s%d
 *)
let split_var v =
   let len = String.length v in
      if len = 0 then
         v, 0
      else
         let rec search i =
            if i = 0 then
               v, 0
            else if is_digit v.[i - 1] then
               search (i - 1)
            else if i = len then
               v, 0
            else
               String.sub v 0 i, int_of_string (String.sub v i (len - i))
         in
            search len

(*
 * Generate a new variable disjoint from the given vars.
 * If the var has a name matching "%s%d", then keep the same form
 * and use the smallest index to keep the var name disjoint.
 *)
let mem' vars v = List.mem v vars

let new_var v vars =
   String_util.vnewname (fst (split_var v)) (mem' vars)

let maybe_new_var v vars =
   if List.mem v vars then
      new_var v vars
   else
      v

let maybe_new_vars vars vars' =
   let rec aux l l' = function
      h::t ->
         let h' = maybe_new_var h l in
            aux (h'::l) (h'::l') t
    | [] -> l'
   in
      aux vars' [] vars

let maybe_new_var_arg p v =
   let vars = Sequent.declared_vars p in
      maybe_new_var v vars

(*
 * Optional vars.
 *)
let get_opt_var_arg v p =
   try dest_var (Sequent.get_term_arg p "var") with
      RefineError _ ->
         maybe_new_var v (Sequent.declared_vars p)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
