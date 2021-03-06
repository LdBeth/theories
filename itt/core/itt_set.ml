doc <:doc<
   @module[Itt_set]

   The @tt[Itt_set] module defines a ``set'' type, or more precisely,
   it defines a type by quantified @emph{separation}.  The form of the type is
   $@set{x; T; P[x]}$, where $T$ is a type, and $P[x]$ is a type for
   any element $x @in T$.  The elements of the set type are those elements
   of $x @in T$ where the proposition $P[x]$ is true.

   The set type is a ``squash'' type: the type is similar to the
   dependent product $x@colon T @times P[x]$ (Section @refmodule[Itt_dprod]),
   but the proof $P[x]$ is omitted (squashed).  The set type <<{x: 'T| 'P['x]}>>
   is always a subtype of $T$.

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1997-2006 MetaPRL Group, Cornell University and
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
extends Itt_squash
extends Itt_equal
extends Itt_unit
extends Itt_subtype
extends Itt_struct
extends Itt_dprod
extends Itt_image
doc docoff

open Basic_tactics

open Itt_equal
open Itt_subtype

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @terms

   The @tt{set} term defines the set type.
>>

define unfold_set: set{'A; x. 'B['x]} <--> Img{x:'A * 'B['x]; p.fst{'p}}

doc docoff

let set_term = << { a: 'A | 'B['a] } >>
let set_opname = opname_of_term set_term
let is_set_term = is_dep0_dep1_term set_opname
let dest_set = dest_dep0_dep1_term set_opname
let mk_set_term = mk_dep0_dep1_term set_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform set_df1 : {x:'A | 'B} = math_set {'x; 'A; 'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Equality and typehood}

   The set type $@set{x; A; B[x]}$ is a type if $A$ is a type,
   and $B[x]$ is a type for any $x @in A$.  Equality of the set
   type is @emph{intensional}.  Two set types are equal only if their
   parts are equal. Note that it is possible to define
   an @emph{extensional} version of a set type using the @emph{intensional} one
   by applying the @hrefterm[esquash] operator to the set predicate.
>>
interactive setEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; a1: 'A1 >- 'B1['a1] = 'B2['a1] in univ[i:l] } -->
   sequent { <H> >- { a1:'A1 | 'B1['a1] } = { a2:'A2 | 'B2['a2] } in univ[i:l] }

interactive setType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; a: 'A >- "type"{'B['a]} } -->
   sequent { <H> >- "type"{ { a:'A | 'B['a] } } }

doc <:doc<
   @modsubsection{Membership}

   Two terms $a_1$ and $a_2$ are equal in the set type $@set{a; A; B[a]}$
   if they are equal in $A$ and also $B[a_1]$ is true.
>>
interactive setMemberEquality {| intro [] |} :
   [wf] sequent { <H> >- 'a1 = 'a2 in 'A } -->
   [assertion] sequent { <H> >- squash{'B['a1]} } -->
   [wf] sequent { <H>; a: 'A >- "type"{'B['a]} } -->
   sequent { <H> >- 'a1 = 'a2 in { a:'A | 'B['a] } }

doc <:doc<
   @modsubsection{Introduction}

   A set type $@set{x; A; B[x]}$ is true if there is an element $a @in A$
   where $B[a]$ is true.
>>
interactive setMemberFormation {| intro [] |} 'a :
   [wf] sequent { <H> >- 'a = 'a in 'A } -->
   [main] sequent { <H> >- squash{'B['a]} } -->
   [wf] sequent { <H>; x: 'A >- "type"{'B['x]} } -->
   sequent { <H> >- { x:'A | 'B['x] } }

doc <:doc<
   @modsubsection{Elimination}

   An assumption with a set type $u@colon @set{x; A; B[x]}$ asserts two facts:
   that $u @in A$ and $B[u]$.  However, the proof of $B[u]$ is unavailable.  The
   $@squash{B[u]}$ hypothesis states that $B[u]$ is true, but its proof is
   omitted.
>>
interactive setElimination {| elim [AutoOK] |} 'H :
   ('t['u;'i] : sequent { <H>; u: 'A; i: squash{'B['u]}; <J['u]> >- 'T['u] }) -->
   sequent { <H>; u: { x:'A | 'B['x] }; <J['u]> >- 'T['u] }

interactive set_member {| nth_hyp |} 'H :
   sequent { <H>; u: { x: 'A | 'B['x] }; <J['u]> >- 'u in 'A }

doc <:doc<
   @modsubsection{Subtyping}

   The set type $@set{x; A; B[x]}$ is always a subtype of $A$ if
   the set type is really a type.  This rule is added to the
   @hrefresource[subtype_resource].
>>
interactive set_subtype {| intro [] |} :
   [wf] sequent { <H> >- 'A Type } -->
   [wf] sequent { <H> >- { a: 'A | 'B['a] } Type } -->
   sequent { <H> >- { a: 'A | 'B['a] } subtype 'A  }

interactive set_monotone {| intro [] |} :
   [wf] sequent { <H> >-  { a: 'A_1 | 'B_1['a] } Type } -->
   [wf] sequent { <H>; a:'A_2 >- 'B_2['a] Type } -->
   sequent { <H> >- 'A_1 subtype 'A_2 } -->
   sequent { <H>; a:'A_1; 'B_1['a] >-  squash{'B_2['a]} } -->
   sequent { <H> >- { a: 'A_1 | 'B_1['a] } subtype { a: 'A_2 | 'B_2['a] } }

doc docoff


(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (set_term,  infer_univ_dep0_dep1 dest_set)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

let resource sub += (LRSubtype ([<< { a: 'A | 'B['a] } >>, << 'A >>], set_subtype))

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
