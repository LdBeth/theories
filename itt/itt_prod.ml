(*!
 * @spelling{dprod}
 *
 * @begin[doc]
 * @theory[Itt_prod]
 *
 * The product type $@prod{A; B}$ is @emph{derived} from the
 * dependent production module @hreftheory[Itt_dprod].  The
 * non-dependent product $@prod{A; B}$ is equivalent to
 * $@prod{x; A; B}$, where $x$ is not free in $B$.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * @email{jyh@cs.cornell.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Itt_equal
include Itt_dprod
include Itt_struct
(*! @docoff *)

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type.Sequent
open Tactic_type.Tacticals

open Base_dtactic

open Itt_equal
open Itt_subtype
open Itt_dprod
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_prod%t"

(* debug_string DebugLoad "Loading itt_prod..." *)

(*!
 * @begin[doc]
 * @rewrites
 * The @tt{unfold_dprod} rewrite unfold the non-dependent
 * product to a dependent-product with a @emph{new} variable
 * $x$.
 * @end[doc]
 *)
prim_rw unfold_prod : ('A * 'B) <--> (x: 'A * 'B)

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Typehood and equality}
 *
 * The product space $@prod{A; B}$ is well-formed if
 * both $A$ and $B$ are types.
 * @end[doc]
 *)
interactive independentProductEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { 'H >- 'A1 * 'B1 = 'A2 * 'B2 in univ[i:l] }

(*
 * Typehood.
 *)
interactive independentProductType {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A1} } -->
   [wf] sequent [squash] { 'H >- "type"{'A2} } -->
   sequent ['ext] { 'H >- "type"{.'A1 * 'A2} }

(*
 * H >- Ui ext A * B
 * by independentProductFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
interactive independentProductFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] }

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * The elimination form splits the hypothesis $x@colon @prod{A; B}$ into
 * its parts $u@colon A$ and $v@colon B$.
 * @end[doc]
 *)
interactive independentProductElimination {| elim_resource [ThinOption thinT] |} 'H 'J 'z 'u 'v :
   ('t['u; 'v] : sequent ['ext] { 'H; z: 'A * 'B; u: 'A; v: 'B; 'J['u, 'v] >- 'T['u, 'v] }) -->
   sequent ['ext] { 'H; z: 'A * 'B; 'J['z] >- 'T['z] }

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 *
 * The members of the non-dependent product $@prod{A; B}$
 * are the pairs $@pair{a; b}$, where $a @in A$ and $b @in B$.
 * @end[doc]
 *)
interactive independentPairEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   [wf] sequent [squash] { 'H >- 'b1 = 'b2 in 'B } -->
   sequent ['ext] { 'H >- ('a1, 'b1) = ('a2, 'b2) in 'A * 'B }

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * The propositional interpretation of the
 * non-dependent product space $@prod{A; B}$ is the
 * conjunction $@and{A; B}$.  The proposition is
 * true if both $A$ and $B$ are true.
 * @end[doc]
 *)
interactive independentPairFormation {| intro_resource [] |} 'H :
   [wf] ('a : sequent ['ext] { 'H >- 'A }) -->
   [wf] ('b : sequent ['ext] { 'H >- 'B }) -->
   sequent ['ext] { 'H >- 'A * 'B }

(*!
 * @begin[doc]
 * @thysubsection{Subtyping}
 *
 * The product space is covariant in both parts.
 * @end[doc]
 *)
interactive independentProductSubtype {| intro_resource [] |} 'H :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H >- subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- subtype{ ('A1 * 'B1); ('A2 * 'B2) } }
(*! @docoff *)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (prod_term, infer_univ_dep0_dep0 dest_prod)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two product types.
 *)
let prod_subtypeT p =
   (independentProductSubtype (hyp_count_addr p)
    thenT addHiddenLabelT "subtype") p

let resource sub +=
   (DSubtype ([<< 'A1 * 'B1 >>, << 'A2 * 'B2 >>;
               << 'A1 >>, << 'A2 >>;
               << 'B1 >>, << 'B2 >>],
              prod_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
