doc <:doc<
   @module[Czf_itt_dall]

   The @tt{Czf_itt_dall} theory defines @emph{restricted}
   universal quantification.  The syntax of the operator
   is $@dall{x; s; P[x]}$, where $s$ is a set, and $P[x]$
   is a functional proposition for any set argument $x$.
   The proposition is true if $P[a]$ is true for any element
   $@mem{a; s}$.

   The restricted universal quantification is coded as
   an implication on the elements of $s$.

   $$@dall{x; @collect{y; T; f[y]}; P[x]} @equiv @forall x@colon T. P[f(x)]$$

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

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
   @email{jyh@cs.cornell.edu}
   @end[license]
>>

doc <:doc< @parents >>
extends Czf_itt_all
extends Czf_itt_set_ind
doc docoff

open Dtactic
open Top_conversionals

open Itt_dfun

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc terms
declare "dall"{'T; x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites

   The @tt{dall} term is defined by set induction on the
   set argument as a universal quantification over the
   index type.
>>
prim_rw unfold_dall : "dall"{'s; x. 'A['x]} <-->
   set_ind{'s; a, f, g. (x: 'a -> 'A['f 'x])}

interactive_rw reduce_dall {| reduce |} : "dall"{collect{'T; x. 'f['x]}; y. 'A['y]} <-->
   (t: 'T -> 'A['f['t]])
doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform dall_df1 : parens :: except_mode[src] :: "prec"[prec_lambda] :: "dall"{'s; x. 'A} =
   pushm[0] forall slot{'x} " " Mpsymbols!member `"s " slot{'s} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Well-formedness}

   The $@dall{x; s; P[x]}$ proposition is well-formed
   if $s$ is a set, and $P[x]$ is a proposition for any
   set $x$.
>>
interactive dall_type {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s} } -->
   ["wf"] sequent { <H>; y: set >- "type"{'A['y]} } -->
   sequent { <H> >- "type"{."dall"{'s; x. 'A['x]}} }

doc <:doc<
   @modsubsection{Introduction}

   The proposition $@dall{x; s; P[x]}$ is true if it is
   well-formed, and $P[a]$ is true for any set $@mem{a; s}$.
>>
interactive dall_intro {| intro [] |} :
   ["wf"]   sequent { <H> >- isset{'s} } -->
   ["wf"]   sequent { <H>; a: set >- "type"{'A['a]} } -->
   ["main"] sequent { <H>; a: set; b: mem{'a; 's} >- 'A['a] } -->
   sequent { <H> >- "dall"{'s; x. 'A['x]} }

doc <:doc<
   @modsubsection{Elimination}

   The elimination form instantiates the universal quantification
   $@dall{x; s; P[x]}$ on a particular argument $@mem{z; s}$.  It
   produces an additional assumption $A[z]$.
>>
interactive dall_elim {| elim [] |} 'H 'z :
   ["wf"]   sequent { <H>; x: "dall"{'s; y. 'A['y]}; <J['x]>; w: set >- "type"{'A['w]} } -->
   ["wf"]   sequent { <H>; x: "dall"{'s; y. 'A['y]}; <J['x]> >- fun_prop{w. 'A['w]} } -->
   ["antecedent"] sequent { <H>; x: "dall"{'s; y. 'A['y]}; <J['x]> >- member{'z; 's} } -->
   ["main"] sequent { <H>; x: "dall"{'s; y. 'A['y]}; <J['x]>; w: 'A['z] >- 'C['x] } -->
   sequent { <H>; x: "dall"{'s; y. 'A['y]}; <J['x]> >- 'C['x] }

doc <:doc<
   @modsubsection{Functionality}

   The @tt{dall} proposition is functional in it's set
   and proposition arguments.
>>
interactive dall_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 'A['z]} } -->
   sequent { <H>; z: set >- fun_prop{x. 'B['z; 'x]} } -->
   sequent { <H>; z: set >- fun_prop{x. 'B['x; 'z]} } -->
   ["wf"] sequent { <H>; z: set; x: set >- "type"{'B['z; 'x]} } -->
   sequent { <H> >- fun_prop{z. "dall"{'A['z]; y. 'B['z; 'y]}} }

doc <:doc<
   @modsubsection{Restriction}

   The proposition $@dall{x; s; P[x]}$ is restricted for any
   set $s$ because the proposition quantifies over the @emph{index}
   type of the set argument (which is a restricted proposition
   itself).
>>
interactive dall_res {| intro [] |} :
   ["wf"]   sequent { <H> >- isset{'A} } -->
   sequent { <H>; x: set >- restricted{'B['x]} } -->
   sequent { <H> >- restricted{. "dall"{'A; y. 'B['y]}} }
doc docoff

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
