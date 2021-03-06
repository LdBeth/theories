doc <:doc<
   @module[Itt_void]

   The @tt{Itt_void} module defines the @emph{empty} type.
   The <<void>> type is a subtype of every other type (since
   it has no elements).

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1997-2006 MetaPRL Group, Cornell University, and
   California Institute of Technology

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}
   Modified by: Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_equal
extends Itt_squash
extends Itt_subtype
doc docoff

open Opname
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

open Auto_tactic
open Dtactic

open Itt_equal
open Itt_subtype
open Itt_squash

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< @terms >>
declare const void

doc <:doc<
   <<any{'a}>> can be a member of any type when <<'a>> is instantiated
   by a member of <<void>>. It can be any term but currently default to
   the simplest term <<it>>.
>>
define unfold_any : any{'x} <--> it
doc docoff

let void_term = << void >>
let void_opname = opname_of_term void_term
let is_void_term = is_no_subterms_term void_opname
let top_opname = mk_opname "top" (mk_opname "Itt_isect" nil_opname)
let top_term = mk_simple_term top_opname []

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform void_df1 : except_mode[src] :: void = `"Void"
dform any_df1 : except_mode[src] :: any{'x} = `"any " slot{'x}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules

   @modsubsection{Equality and typehood}

   The <<void>> type is a member of every universe, and it
   is a type.

>>
prim voidEquality {| intro [] |} :
   sequent { <H> >- void in univ[i:l] } =
   it

(*
 * Typehood.
 *)
interactive voidType {| intro [] |} :
   sequent { <H> >- "type"{void} }

doc <:doc<
   @modsubsection{Elimination}

   Since the <<void>> type is empty, induction over the
   <<void>> type produces no cases. And <<any{'x}>> is used for
   witness.
>>
prim voidElimination {| elim []; squash; nth_hyp |} 'H :
   sequent { <H>; x: void; <J['x]> >- 'C['x] } =
   any{'x}

doc <:doc<
   @modsubsection{Subtyping}

   The <<void>> type is a subtype of every other type.
   This rule is derived from the definition of subtyping, and the
   @hrefrule[voidElimination] rule.
>>
interactive void_subtype {| intro[] |} :
   sequent { <H> >- 'T Type } -->
   sequent { <H> >- void subtype 'T }

doc docoff

(*
 * H >- Ui ext Void
 * by voidFormation
 *)
interactive voidFormation :
   sequent { <H> >- univ[i:l] }

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

let resource sub += (RLSubtype ([void_term, << 'a >>], void_subtype))

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (void_term, infer_univ1)

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
