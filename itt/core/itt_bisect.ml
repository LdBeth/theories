doc <:doc<
   @module[Itt_bisect]

   The @tt{Itt_bisect} module derives a binary intersection
   $@bisect{A; B}$ from the intersection @hrefterm[isect] defined
   in the @hrefmodule[Itt_isect] theory, and the Boolean values
   defined in the @hrefmodule[Itt_bool] theory.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998-2006 MetaPRL Group, Cornell University and
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

   Author: Jason Hickey @email{jyh@cs.cornell.edu}
   Modified by: Alexei Kopylov @email{kopylov@cs.cornell.edu}
                Aleksey Nogin @email{nogin@cs.cornell.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_isect
extends Itt_bool
doc docoff

open Basic_tactics
open Itt_struct

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

doc <:doc<
   @terms

   The definition of the binary intersection $@bisect{A; B}$
   is an intersection over the Booleans.
>>
define unfold_bisect : bisect{'A; 'B} <-->
                          "isect"{bool; x. ifthenelse{'x; 'A; 'B}}
doc docoff

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_bisect

dform bisect_df : except_mode[src] :: parens :: "prec"[prec_bisect] :: bisect{'A; 'B} =
   slot["le"]{'A} `" " cap space slot{'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Typehood and equality}

   The binary intersection $@bisect{A; B}$ is well-formed if both $A$
   and $B$ are types.
>>
interactive bisectEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H> >- 'B1 = 'B2 in univ[i:l] } -->
   sequent { <H> >- bisect{'A1; 'B1} = bisect{'A2; 'B2} in univ[i:l] }

interactive bisectType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- "type"{bisect{'A; 'B}} }

doc docoff

(* Formation. *)
interactive bisectFormation :
   sequent { <H> >- univ[i:l] } -->
   sequent { <H> >- univ[i:l] } -->
   sequent { <H> >- univ[i:l] }

doc <:doc<
   @modsubsection{Membership}

   Two terms $x$ and $y$ are equal in the binary intersection
   $@bisect{A; B}$ if they are equal in both $A$ and $B$.  Put another
   way, the elements of the binary intersection are the terms that
   are members of both $A$ and $B$.
>>
interactive bisectMemberEquality {| intro [] |} :
   [wf] sequent { <H> >- 'x = 'y in 'A } -->
   [wf] sequent { <H> >- 'x = 'y in 'B } -->
   sequent { <H> >- 'x = 'y in 'A isect 'B }

doc <:doc<
   @modsubsection{Elimination}

   The elimination rule for an assumption $x@colon @bisect{A; B}$ states that $x$ can be replaced by
   $a @in A$ or by $b @in B$.

   @docoff
>>

interactive bisectElimination_eq 'H bind{x.bind{a,b.'C['x;'a;'b]}} :
   sequent { <H>; x: 'A isect 'B; <J['x]>; a: 'A; u: 'a = 'x in 'A;
                                                   b: 'B; v: 'b = 'x in 'B >- 'C['x;'a;'b] } -->
   sequent { <H>; x: 'A isect 'B; <J['x]> >- 'C['x;'x;'x] }

let bisectEliminationT = argfunT (fun n p ->
   let n = Sequent.get_pos_hyp_num p n in
   let x = Sequent.nth_binding p n in
      match get_with_arg p with
         Some bind when is_bind2_term bind ->
            let bind = mk_bind1_term x bind in
               bisectElimination_eq n bind
       | _ ->
            raise (RefineError
               ("bisectElimination", StringTermError ("required the bind term:",<<bind{a,b.'C['a;'b]}>>))))

let bisectEliminationT = argfunT (fun n p ->
   let n = Sequent.get_pos_hyp_num p n in
      bisectEliminationT n thenT thinIfThinningT [-3;-1;n])

let resource elim += (<<'A isect 'B>>, wrap_elim bisectEliminationT)

doc docon

interactive bisectElimination 'H bind{a,b.'C['a;'b]} :
   sequent { <H>; x: 'A isect 'B; <J['x]>; a: 'A; b: 'B >- 'C['a;'b] } -->
   sequent { <H>; x: 'A isect 'B; <J['x]> >- 'C['x;'x] }

doc <:doc<

   The elimination rule has also two simpler forms.
   The first produces a witness that $x @in A$, and the second produces a witness
   for $x @in B$.
>>

interactive bisectEliminationLeft (*{| elim [SelectOption 1] |}*) 'H :
   sequent { <H>; x: 'A isect 'B; <J['x]>; a: 'A; u: 'a = 'x in 'A; b: 'B; v: 'b = 'x in 'B >- 'C['a] } -->
   sequent { <H>; x: 'A isect 'B; <J['x]> >- 'C['x] }

interactive bisectEliminationRight (*{| elim [SelectOption 2] |}*) 'H :
   sequent { <H>; x: 'A isect 'B; <J['x]>; a: 'A; u: 'a = 'x in 'A; b: 'B; v: 'b = 'x in 'B >- 'C['b] } -->
   sequent { <H>; x: 'A isect 'B; <J['x]> >- 'C['x] }

doc docoff

let bisectEliminationT = argfunT (fun n p ->
   let n = Sequent.get_pos_hyp_num p n in
   match get_sel_arg p with
      None -> bisectEliminationT n
    | Some 1 -> bisectEliminationLeft n thenT thinIfThinningT [-3;-1;n]
    | Some 2 -> bisectEliminationRight n thenT thinIfThinningT [-3;-1;n]
    | Some _ -> raise (RefineError ("bisectElimination", StringError ("select option is out of range ([1,2])"))))

let resource elim += (<<'A isect 'B>>, wrap_elim bisectEliminationT)

doc <:doc< Equality elimination. >>

interactive bisectEqualityElim {| elim [ThinOption thinT] |} 'H :
   sequent{ <H>; x: 't1 = 't2 in 'A isect 'B; u : 't1 = 't2 in 'A; v : 't1 = 't2 in 'B; <J['x]> >- 'C['x] } -->
   sequent{ <H>; x: 't1 = 't2 in 'A isect 'B; <J['x]> >- 'C['x] }

doc <:doc<
   @modsubsection{Subtyping}

   The binary intersection $@bisect{A; B}$ is covariant
   in both $A$ and $B$.
>>
interactive bisectSubtypeLeft {| intro [SelectOption 1] |} :
   sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- 'A subtype 'C } -->
   sequent { <H> >- 'A isect 'B subtype 'C}

interactive bisectSubtypeRight {| intro [SelectOption 2] |} :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- 'B subtype 'C } -->
   sequent { <H> >- 'A isect 'B subtype 'C }

interactive bisectSubtypeBelow {| intro [] |}:
   sequent { <H> >- 'C subtype 'A } -->
   sequent { <H> >- 'C subtype 'B } -->
   sequent { <H> >- 'C subtype 'A isect 'B}

interactive bisectTrivial1 {| nth_hyp |} 'H:
   sequent { <H>; x:'A isect 'B; <J['x]>  >- 'x in 'A}

interactive bisectTrivial2 {| nth_hyp |} 'H:
   sequent { <H>; x:'A isect 'B; <J['x]>  >- 'x in 'B}

interactive bisectSubtype1 {| intro [] |} :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- 'A isect 'B subtype 'A}

interactive bisectSubtype2 {| intro [] |} :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- 'A isect 'B subtype 'B}

doc docoff

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
