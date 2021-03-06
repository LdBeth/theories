doc <:doc<
   @spelling{bi}
   @module[Itt_logic]

   The @tt[Itt_logic] module defines the propositional
   interpretations of the basic types.  This is a @emph{derived}
   module.  All the propositional connectives are coded in
   terms of the existing types.

   This module also defines several tactics.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1997-2006 MetaPRL Group, Cornell University, City
   University of New York, and California Institute of Technology

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
   Modified by: Aleksey Nogin @email{nogin@cs.cornell.edu}
                Yegor Bryukhov @email{ynb@mail.ru}
                Alexei Kopylov @email{kopylov@cs.cornell.edu}
                Lori Lorigo
                Stephan Schmitt
                Carl Witty
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_equal
extends Itt_esquash
extends Itt_dfun
extends Itt_dprod
extends Itt_prod
extends Itt_union
extends Itt_void
extends Itt_unit
extends Itt_struct
doc docoff

open Lm_debug
open Lm_printf

open Browser_resource

open Basic_tactics

open Itt_squash
open Itt_equal
open Itt_dfun
open Itt_dprod
open Itt_struct

module TermMan = Refiner.Refiner.TermMan

let debug_auto =
   create_debug (**)
      { debug_name = "auto";
        debug_description = "Display auto tactic operations";
        debug_value = false
      }

(************************************************************************
 * REWRITES								*
 ************************************************************************)

doc <:doc<
   @terms

   The following terms define the propositional connectives.
   The @tt{prop} term defines the space of @emph{propositions}
   (the same as the type universes).

   The propositional interpretations have the following
   definitions:

   $$
   @begin[array, rcl]
   @line{@true  @equiv  @unit}
   @line{@false  @equiv  <<void>>}
   @line{@not{A}  @equiv  <<'A -> void>>}
   @line{@and{A; B}  @equiv  @prod{A; B}}
   @line{@or{A; B}  @equiv  @union{A; B}}
   @line{@implies{A; B}  @equiv  <<'A -> 'B>>}
   @line{@iff{A; B}  @equiv  @and{(<<'A -> 'B>>); (<<'B -> 'A>>)}}
   @line{@all{x; A; B[x]}  @equiv  <<x:'A -> 'B['x]>>}
   @line{@exists{x; A; B[x]}  @equiv  @prod{x; A; B[x]}}
   @end[array]
   $$

   The @emph{conditional} forms $@cand{A; B}$ and
   $@cor{A; B}$ encode the propositional truth
   from left to right.
>>
define unfold_true : "true" <--> unit
define unfold_false : "false" <--> void
define unfold_not : "not"{'a} <--> ('a -> void)
define unfold_implies : "implies"{'a; 'b} <--> ('a -> 'b)
define unfold_and : "and"{'a; 'b} <--> 'a * 'b
define unfold_or : "or"{'a; 'b} <--> 'a + 'b
define unfold_iff : "iff"{'a; 'b} <--> (('a -> 'b) & ('b -> 'a))
define unfold_cand : "cand"{'a; 'b} <--> ('a & 'b)
define unfold_cor : "cor"{'a; 'b} <--> "or"{'a; ."cand"{"not"{'a}; 'b}}
define unfold_all : "all"{'A; x. 'B['x]} <--> x: 'A -> 'B['x]
define unfold_exists : "exists"{'A; x. 'B['x]} <--> x: 'A * 'B['x]
doc docoff

let fold_true    = makeFoldC << "true" >> unfold_true
let fold_false   = makeFoldC << "false" >> unfold_false
let fold_not     = makeFoldC << not{'a} >> unfold_not
let fold_implies = makeFoldC << 'a => 'b >> unfold_implies
let fold_iff     = makeFoldC << 'a <=> 'b >> unfold_iff
let fold_and     = makeFoldC << 'a & 'b >> unfold_and
let fold_or      = makeFoldC << 'a or 'b >> unfold_or
let fold_cand    = makeFoldC << "cand"{'a; 'b} >> unfold_cand
let fold_cor     = makeFoldC << "cor"{'a; 'b} >> unfold_cor
let fold_all     = makeFoldC << all x: 'A. 'B['x] >> unfold_all
let fold_exists  = makeFoldC << exst x: 'A. 'B['x] >> unfold_exists

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules

   The rules are divided into groups for each of the
   propositional connectives.  Each of the connectives
   has a well-formedness rule, and introduction and elimination
   forms (where possible).

   @modsubsection{True and False}
   The @hrefterm[true] and @hrefterm[false] terms are
   both types.  The @tt{true} term is always true; there is
   no elimination form.  The @tt{false} term is always false;
   there is no introduction form.
>>
interactive true_univ {| intro [] |} :
   sequent { <H> >- "true" in univ[i:l] }

interactive true_type {| intro [] |} :
   sequent { <H> >- "type"{"true"} }

interactive true_intro {| intro [] |} :
   sequent { <H> >- "true" }

interactive true_elim {| elim [AutoOK] |} 'H :
   sequent { <H>; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: "true"; <J['x]> >- 'C['x] }

interactive false_univ {| intro [] |} :
   sequent { <H> >- "false" in univ[i:l] }

interactive false_type {| intro [] |} :
   sequent { <H> >- "type"{"false"} }

interactive false_elim {| elim []; squash; nth_hyp |} 'H :
   sequent { <H>; x: "false"; <J['x]> >- 'C['x] }

interactive false_esquash_elim {| elim []; nth_hyp |} 'H :
   sequent { <H>; x: esquash{"false"}; <J['x]> >- 'C['x] }

doc <:doc<
   @modsubsection{Negation}

   The negation << "not"{'t} >> is well-formed if
   $t$ is a type.  The negation states that the type $t$
   is not inhabited: any proof of $t$ is also a proof of
   <<void>>.  To prove the negation, assume $t$ and find
   a contradiction.  The elimination form forms a proof
   of the goal from a proof of $t$.
>>
interactive not_univ {| intro [] |} :
   [wf] sequent { <H> >- 't1 = 't2 in univ[i:l] } -->
   sequent { <H> >- "not"{'t1} = "not"{'t2} in univ[i:l] }

interactive not_type {| intro [] |} :
   [wf] sequent { <H> >- "type"{'t} } -->
   sequent { <H> >- "type"{"not"{'t}} }

interactive not_intro {| intro [] |} :
   [wf] sequent { <H> >- "type"{'t} } -->
   [main] sequent { <H>; x: 't >- "false" } -->
   sequent { <H> >- "not"{'t} }

interactive not_elim {| elim [ThinOption thinT] |} 'H :
   [main] sequent { <H>; x: "not"{'t}; <J['x]> >- 't } -->
   sequent { <H>; x: "not"{'t}; <J['x]> >- 'C['x] }

interactive squash_not_elim {| elim [] (* squash *) |} 'H :
   [wf] sequent { <H>; "not"{'t}; <J[it]> >- 't Type } -->
   sequent { <H>; "not"{'t}; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: squash{"not"{'t}}; <J['x]> >- 'C['x] }

doc <:doc<
   @modsubsection{Conjunction}

   The conjunction << "and"{'a_1; 'a_2} >> is well-formed if
   both $a_1$ and $a_2$ are types.  It is true if both $a_1$ and
   $a_2$ are true.  The elimination form splits the assumption
   into its two component proofs.
>>
interactive and_univ {| intro [] |} :
   [wf] sequent { <H> >- 'a1 = 'b1 in univ[i:l] } -->
   [wf] sequent { <H>; 'a1 >- 'a2 = 'b2 in univ[i:l] } -->
   sequent { <H> >- "and"{'a1; 'a2} = "and"{'b1; 'b2} in univ[i:l] }

interactive and_type {| intro [] |} :
   [wf] sequent { <H> >- "type"{'a1} } -->
   [wf] sequent { <H>; 'a1 >- "type"{'a2} } -->
   sequent { <H> >- "type"{"and"{'a1; 'a2}} }

interactive and_intro {| intro [] |} :
   [main] sequent { <H> >- 'a1 } -->
   [main] sequent { <H> >- 'a2 } -->
   sequent { <H> >- 'a1 & 'a2 }

interactive and_squash_intro {| intro [] |} :
   [main] sequent { <H> >- squash{'a1} } -->
   [main] sequent { <H> >- squash{'a2} } -->
   sequent { <H> >- squash{('a1 & 'a2)} }

interactive and_elim {| elim [AutoOK] |} 'H :
   [main] sequent { <H>; y: 'a1; z: 'a2; <J['y, 'z]> >- 'C['y, 'z] } -->
   sequent { <H>; x: 'a1 & 'a2; <J['x]> >- 'C['x] }

interactive and_squash_elim {| elim [AutoOK] |} 'H :
   [main] sequent { <H>; y: squash{'a1}; z: squash{'a2}; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: squash{('a1 & 'a2)}; <J['x]> >- 'C['x] }

doc docoff

let resource nth_hyp += [
   <<'A & 'B >>, <<'A>>, wrap_nth_hyp_certain (fun i ->
      and_elim i thenT hypothesis (if i > 0 then i else i - 1));
   <<'A & 'B >>, <<'B>>, wrap_nth_hyp_certain (fun i ->
      and_elim i thenT hypothesis (if i > 0 then i + 1 else i));
]

doc <:doc<
   @modsubsection{Disjunction}

   The disjunction << "or"{'a_1; 'a_2} >> is well-formed if both
   $a_1$ and $a_2$ are types.  The disjunction is true if it is
   a type and one of $a_1$ or $a_2$ is true.  The introduction
   rules use the @tt[SelectOption] to allow application with
   the @hreftactic[selT] tactical.  The @tt{selT 1 (dT 0)} tactic applies
   the @hrefrule[or_intro_left] rule, and @tt{selT 2 (dT 0)} applies the
   @hrefrule[or_intro_right] rule.  The elimination rule performs
   a case analysis on the disjunctive assumption, producing
   a case for the left proof of $a_1$, and another for the
   right proof of $a_2$.
>>
interactive or_univ {| intro [] |} :
   [wf] sequent { <H> >- 'a1 = 'b1 in univ[i:l] } -->
   [wf] sequent { <H> >- 'a2 = 'b2 in univ[i:l] } -->
   sequent { <H> >- "or"{'a1; 'a2} = "or"{'b1; 'b2} in univ[i:l] }

interactive or_type {| intro [] |} :
   [wf] sequent { <H> >- "type"{'a1} } -->
   [wf] sequent { <H> >- "type"{'a2} } -->
   sequent { <H> >- "type"{"or"{'a1; 'a2}} }

interactive or_intro_left {| intro [SelectOption 1] |} :
   [wf] sequent { <H> >- "type"{'a2} } -->
   [main] sequent { <H> >- 'a1 } -->
   sequent { <H> >- "or"{'a1; 'a2} }

interactive or_intro_right {| intro [SelectOption 2] |} :
   [wf] sequent { <H> >- "type"{'a1} } -->
   [main] sequent { <H> >- 'a2 } -->
   sequent { <H> >- "or"{'a1; 'a2} }

interactive or_elim {| elim [] |} 'H :
   [main] sequent { <H>; y: 'a1; <J[inl{'y}]> >- 'C[inl{'y}] } -->
   [main] sequent { <H>; y: 'a2; <J[inr{'y}]> >- 'C[inr{'y}] } -->
   sequent { <H>; x: "or"{'a1; 'a2}; <J['x]> >- 'C['x] }

doc <:doc<
   @modsubsection{Implication}

   The implication << implies{'a_1; 'a_2} >> is well-formed if both
   $a_1$ and $a_2$ are types.  The implication is true if it is a
   type, and a proof of $a_2$ can be produced from a proof of
   $a_1$.  The elimination rule corresponds to @emph{modus-ponens}:
   if a proof of $a_1$ can be found, so can a proof of $a_2$ by
   application of the proof of << implies{'a_1; 'a_2} >>.
>>
interactive implies_univ {| intro [] |} :
   [wf] sequent { <H> >- 'a1 = 'b1 in univ[i:l] } -->
   [wf] sequent { <H> >- 'a2 = 'b2 in univ[i:l] } -->
   sequent { <H> >- "implies"{'a1; 'a2} = "implies"{'b1; 'b2} in univ[i:l] }

interactive implies_type {| intro [] |} :
   [wf] sequent { <H> >- "type"{'a1} } -->
   [wf] sequent { <H>; 'a1 >- "type"{'a2} } -->
   sequent { <H> >- "type"{"implies"{'a1; 'a2}} }

interactive implies_intro {| intro [] |} :
   [wf] sequent { <H> >- "type"{'a1} } -->
   [main] sequent { <H>; x: 'a1 >- 'a2 } -->
   sequent { <H> >- "implies"{'a1; 'a2} }

interactive implies_elim {| elim [ThinOption thinT] |} 'H :
   [assertion] sequent { <H>; x: "implies"{'a1; 'a2}; <J['x]> >- 'a1 } -->
   [main] sequent { <H>; x: "implies"{'a1; 'a2}; <J['x]>; y: 'a2 >- 'C['x] } -->
   sequent { <H>; x: "implies"{'a1; 'a2}; <J['x]> >- 'C['x] }

doc <:doc<
   @modsubsection{Bi-implication}

   The bi-implication << 'a_1 <=> 'a_2 >> is well-formed if
   both $a_1$ and $a_2$ are types.  The introduction and elimination rules
   perform the top-level conjunctive reasoning.
>>
interactive iff_univ {| intro [] |} :
   [wf] sequent { <H> >- 'a1 = 'b1 in univ[i:l] } -->
   [wf] sequent { <H> >- 'a2 = 'b2 in univ[i:l] } -->
   sequent { <H> >- ('a1 <=> 'a2) = ('b1 <=> 'b2) in univ[i:l] }

interactive iff_type {| intro [] |} :
   [wf] sequent { <H> >- "type"{'a1} } -->
   [wf] sequent { <H> >- "type"{'a2} } -->
   sequent { <H> >- "type"{'a1 <=> 'a2} }

interactive iff_intro {| intro [] |} :
   [wf] sequent { <H> >- 'a1 => 'a2 } -->
   [wf] sequent { <H> >- 'a2 => 'a1 } -->
   sequent { <H> >- 'a1 <=> 'a2 }

interactive iff_elim {| elim [] |} 'H :
   sequent { <H>; y: "implies"{'a1; 'a2}; z: "implies"{'a2; 'a1}; <J['y, 'z]> >- 'C['y, 'z] } -->
   sequent { <H>; x: 'a1 <=> 'a2; <J['x]> >- 'C['x] }

doc <:doc<
   @modsubsection{Conditional conjunction}

   The conditional conjunction << "cand"{'a_1; 'a_2} >> differs from
   the conjunction only in the introduction rule.  The conjunction
   is true if $a_1$ is true, and a proof of $a_2$ can be produced from
   a proof of $a_1$.
>>
interactive cand_univ {| intro [] |} :
   [wf] sequent { <H> >- 'a1 = 'b1 in univ[i:l] } -->
   [wf] sequent { <H>; x: 'a1 >- 'a2 = 'b2 in univ[i:l] } -->
   sequent { <H> >- "cand"{'a1; 'a2} = "cand"{'b1; 'b2} in univ[i:l] }

interactive cand_type {| intro [] |} :
   [wf] sequent { <H> >- "type"{'a1} } -->
   [wf] sequent { <H>; x: 'a1 >- "type"{'a2} } -->
   sequent { <H> >- "type"{"cand"{'a1; 'a2}} }

interactive cand_intro {| intro [] |} :
   [main] sequent { <H> >- 'a1 } -->
   [main] sequent { <H>; x: 'a1 >- 'a2 } -->
   sequent { <H> >- "cand"{'a1; 'a2} }

interactive cand_elim {| elim [AutoOK] |} 'H :
   [main] sequent { <H>; y: 'a1; z: 'a2; <J['y, 'z]> >- 'C['y, 'z] } -->
   sequent { <H>; x: "cand"{'a1; 'a2}; <J['x]> >- 'C['x] }

doc <:doc<
   @modsubsection{Conditional disjunction}

   The conditional disjunction << "cor"{'a_1; 'a_2} >> differs from
   the disjunction in that a proof of $a_2$ is needed only if
   a proof of $a_1$ can't be found.  The conditional disjunction
   is true if $a_1$ is true, or $a_2$ is true @emph{assuming} that
   $a_1$ is false.  The elimination rule produces the two cases,
   one where there is a proof of $a_1$, and another where
   there is a proof of $a_2$ and a proof of falsehood for $a_1$.
>>
interactive cor_univ {| intro [] |} :
   [wf] sequent { <H> >- 'a1 = 'b1 in univ[i:l] } -->
   [wf] sequent { <H>; x: "not"{'a1} >- 'a2 = 'b2 in univ[i:l] } -->
   sequent { <H> >- "cor"{'a1; 'a2} = "cor"{'b1; 'b2} in univ[i:l] }

interactive cor_type {| intro [] |} :
   [wf] sequent { <H> >- "type"{'a1} } -->
   [wf] sequent { <H>; x: "not"{'a1} >- "type"{'a2} } -->
   sequent { <H> >- "type"{"cor"{'a1; 'a2}} }

interactive cor_intro_left {| intro [SelectOption 1] |} :
   [wf] sequent { <H>; x: "not"{'a1} >- "type"{'a2} } -->
   [main] sequent { <H> >- 'a1 } -->
   sequent { <H> >- "cor"{'a1; 'a2} }

interactive cor_intro_right {| intro [SelectOption 2] |} :
   [wf] sequent { <H> >- "type"{'a1} } -->
   [main] sequent { <H> >- "not"{'a1} } -->
   [main] sequent { <H>; x: "not"{'a1} >- 'a2 } -->
   sequent { <H> >- "cor"{'a1; 'a2} }

interactive cor_elim {| elim [] |} 'H :
   [main] sequent { <H>; u: 'a1; <J[inl{'u}]> >- 'C[inl{'u}] } -->
   [main] sequent { <H>; u: "not"{'a1}; v: 'a2; <J[inr{'u, 'v}]> >- 'C[inr{'u, 'v}] } -->
   sequent { <H>; x: "cor"{'a1; 'a2}; <J['x]> >- 'C['x] }

doc <:doc<
   @modsubsection{Universal quantification}

   The universal quantification << all x: 'A. 'B['x] >> is well-formed
   if $A$ is a type, and $B[x]$ is a type for any $x @in A$.
   The quantification is true if it is well-formed and
   $B[a]$ is true for any element $a @in A$.  The elimination
   form allows @emph{instantiation} of quantification on
   a particular element $a @in A$, to produce a proof of
   $B[a]$.
>>
interactive all_univ {| intro [] |} :
   [wf] sequent { <H> >- 't1 = 't2 in univ[i:l] } -->
   [wf] sequent { <H>; x1 : 't1 >- 'b1['x1] = 'b2['x1] in univ[i:l] } -->
   sequent { <H> >- "all"{'t1; x1. 'b1['x1]} = "all"{'t2; x2. 'b2['x2]} in univ[i:l] }

interactive all_type {| intro [] |} :
   [wf] sequent { <H> >- "type"{'t} } -->
   [wf] sequent { <H>; v: 't >- "type"{'b['v]} } -->
   sequent { <H> >- "type"{"all"{'t; v. 'b['v]}} }

interactive all_intro {| intro [] |} :
   [wf] sequent { <H> >- "type"{'t} } -->
   [main] sequent { <H>; v: 't >- 'b['v] } -->
   sequent { <H> >- "all"{'t; v. 'b['v]} }

interactive all_elim {| elim [ThinOption thinT] |} 'H 'z :
   [wf] sequent { <H>; x: all a: 'A. 'B['a]; <J['x]> >- 'z in 'A } -->
   [main] sequent { <H>; x: all a: 'A. 'B['a]; <J['x]>; w: 'B['z] >- 'C['x] } -->
   sequent { <H>; x: all a: 'A. 'B['a]; <J['x]> >- 'C['x] }

doc <:doc<
   @modsubsection{Existential quantification}

   The existential quantification << exst x: 'A. 'B['x] >> is well-formed
   if $A$ is a type, and $B[x]$ is a type for any $x @in A$.  The quantification
   is true if it is well-formed and there is a proof $a @in A$ where $B[a]$
   is also true.  The elimination form splits the proof of $@exists{x; A; B[x]}$
   into its parts.
>>
interactive exists_univ {| intro [] |} :
   [wf] sequent { <H> >- 't1 = 't2 in univ[i:l] } -->
   [wf] sequent { <H>; x1 : 't1 >- 'b1['x1] = 'b2['x1] in univ[i:l] } -->
   sequent { <H> >- "exists"{'t1; x1. 'b1['x1]} = "exists"{'t2; x2. 'b2['x2]} in univ[i:l] }

interactive exists_type {| intro [] |} :
   [wf] sequent { <H> >- "type"{'t} } -->
   [wf] sequent { <H>; v: 't >- "type"{'b['v]} } -->
   sequent { <H> >- "type"{"exists"{'t; v. 'b['v]}} }

interactive exists_intro {| intro [] |} 'z :
   [wf] sequent { <H> >- 'z in 't } -->
   [main] sequent { <H> >- 'b['z] } -->
   [wf] sequent { <H>; v: 't >- "type"{'b['v]} } -->
   sequent { <H> >- "exists"{'t; v. 'b['v]} }

interactive exists_elim {| elim [AutoOK] |} 'H :
   [main] sequent { <H>; v: 'a; z: 'b['v]; <J['v, 'z]> >- 'C['v, 'z] } -->
   sequent { <H>; x: exst v: 'a. 'b['v]; <J['x]> >- 'C['x] }
doc docoff

(************************************************************************
 * DISPLAY FORMS							*
 ************************************************************************)

prec prec_iff
prec prec_implies
prec prec_and
prec prec_or
prec prec_not
prec prec_quant

prec prec_implies < prec_iff
prec prec_iff < prec_or
prec prec_or < prec_and
prec prec_and < prec_not
prec prec_quant < prec_iff

dform true_df : except_mode[src] :: "true" =
   `"True"

dform true_df2 : mode[src] :: "true" =
   `"\"true\""

dform false_df : except_mode[src] :: "false" =
   `"False"

dform false_df2 : mode[src] :: "false" =
   `"\"false\""

dform not_df1 : except_mode[src] :: parens :: "prec"[prec_not] :: "not"{'a} =
   Mpsymbols!tneg slot["le"]{'a}

dform not_df2 : mode[src] :: parens :: "prec"[prec_implies] :: "not"{'a} =
   `"\"not\"{" 'a `"}"

(*
 * Implication.
 *)
declare implies_df{'a : Dform } : Dform

dform implies_df1 : parens :: "prec"[prec_implies] :: mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: "implies"{'a; 'b} =
   szone pushm[0] slot["le"]{'a} implies_df{'b} popm ezone

dform implies_df2 : mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: implies_df{"implies"{'a; 'b}} =
   implies_df{'a} implies_df{'b}

dform implies_df3 : mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: implies_df{'a} =
   hspace Mpsymbols!Rightarrow `" " slot{'a}

(*
 * Bi-implication.
 *)
dform iff_df : parens :: "prec"[prec_iff] :: iff{'a; 'b} =
   slot["le"]{'a} `" " Mpsymbols!Leftrightarrow `" " slot["le"]{'b}

(*
 * Disjunction.
 *)
declare or_df{'a : Dform } : Dform

dform or_df1 : parens :: "prec"[prec_or] :: mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: "or"{'a; 'b} =
   szone pushm[0] slot["le"]{'a} or_df{'b} popm ezone

dform or_df2 : mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: or_df{"or"{'a; 'b}} =
   or_df{'a} or_df{'b}

dform or_df3 : mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: or_df{'a} =
   hspace Mpsymbols!vee `" " slot{'a}

(*
 * Disjunction.
 *)
declare cor_df{'a : Dform } : Dform

dform cor_df1 : parens :: "prec"[prec_or] :: "cor"{'a; 'b} =
   szone pushm[0] slot["le"]{'a} cor_df{'b} popm ezone

dform cor_df2 : cor_df{"cor"{'a; 'b}} =
   cor_df{'a} cor_df{'b}

dform cor_df3 : cor_df{'a} =
   hspace Mpsymbols!vee subc `" " slot{'a}

(*
 * Conjunction.
 *)
declare and_df{'a : Dform } : Dform

dform and_df1 : parens :: "prec"[prec_and] :: mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: "and"{'a; 'b} =
   szone pushm[0] slot["le"]{'a} and_df{'b} popm ezone

dform and_df2 : mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: and_df{"and"{'a; 'b}} =
   and_df{'a} and_df{'b}

dform and_df3 : mode[src] :: mode[prl] :: mode[html] :: mode[tex] :: and_df{'a} =
   hspace Mpsymbols!wedge `" " slot{'a}

(*
 * Conjunction.
 *)
declare cand_df{'a : Dform } : Dform

dform cand_df1 : parens :: "prec"[prec_and] :: "cand"{'a; 'b} =
   szone pushm[0] slot["le"]{'a} cand_df{'b} popm ezone

dform cand_df2 : and_df{"cand"{'a; 'b}} =
   cand_df{'a} cand_df{'b}

dform cand_df3 : cand_df{'a} =
   hspace Mpsymbols!wedge subc `" " slot{'a}

(*
 * Quantifiers.
 *)
dform all_df1 : except_mode[src] :: parens :: "prec"[prec_quant] :: "all"{'A; x. 'B} =
   szone pushm[3] Mpsymbols!forall slot{'x} `":" slot{'A} sbreak["",". "] slot{'B} popm ezone

dform all_df2 : mode[src] :: parens :: "prec"[prec_quant] :: "all"{'A; x. 'B} =
   `"all " slot[x:s] `": " slot{'A}`"." slot{'B}

dform exists_df1 : except_mode[src] :: parens :: "prec"[prec_quant] :: "exists"{'A; x. 'B} =
   szone pushm[3] Mpsymbols!"exists" slot{'x} `":" slot{'A} sbreak["",". "] slot{'B} popm ezone

dform exists_df2 : mode[src] :: parens :: "prec"[prec_quant] :: "exists"{'A; x. 'B} =
  `"exst " slot[x:s] `": " slot{'A} `"." slot{'B}

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let is_false_term = is_no_subterms_term (opname_of_term << "false" >>)

let all_term = << all x: 'A. 'B['x] >>
let all_opname = opname_of_term all_term
let is_all_term = is_dep0_dep1_term all_opname
let dest_all = dest_dep0_dep1_term all_opname
let mk_all_term = mk_dep0_dep1_term all_opname

let exists_term = << exst x: 'A. 'B['x] >>
let exists_opname = opname_of_term exists_term
let is_exists_term = is_dep0_dep1_term exists_opname
let dest_exists = dest_dep0_dep1_term exists_opname
let mk_exists_term = mk_dep0_dep1_term exists_opname

let or_term = << 'A or 'B >>
let or_opname = opname_of_term or_term
let is_or_term = is_dep0_dep0_term or_opname
let dest_or = dest_dep0_dep0_term or_opname
let mk_or_term = mk_dep0_dep0_term or_opname

let and_term = << 'A and 'B >>
let and_opname = opname_of_term and_term
let is_and_term = is_dep0_dep0_term and_opname
let dest_and = dest_dep0_dep0_term and_opname
let mk_and_term = mk_dep0_dep0_term and_opname

let cor_term = << "cor"{'A; 'B} >>
let cor_opname = opname_of_term cor_term
let is_cor_term = is_dep0_dep0_term cor_opname
let dest_cor = dest_dep0_dep0_term cor_opname
let mk_cor_term = mk_dep0_dep0_term cor_opname

let cand_term = << "cand"{'A; 'B} >>
let cand_opname = opname_of_term cand_term
let is_cand_term = is_dep0_dep0_term cand_opname
let dest_cand = dest_dep0_dep0_term cand_opname
let mk_cand_term = mk_dep0_dep0_term cand_opname

let implies_term = << 'A => 'B >>
let implies_opname = opname_of_term implies_term
let is_implies_term = is_dep0_dep0_term implies_opname
let dest_implies = dest_dep0_dep0_term implies_opname
let mk_implies_term = mk_dep0_dep0_term implies_opname

let iff_term = << 'A <=> 'B >>
let iff_opname = opname_of_term iff_term
let is_iff_term = is_dep0_dep0_term iff_opname
let dest_iff = dest_dep0_dep0_term iff_opname
let mk_iff_term = mk_dep0_dep0_term iff_opname

let not_term = << "not"{'a} >>
let not_opname = opname_of_term not_term
let is_not_term = is_dep0_term not_opname
let dest_not = dest_dep0_term not_opname
let mk_not_term = mk_dep0_term not_opname

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += [
   <<"true">>, infer_univ1;
   <<"false">>, infer_univ1;
   all_term, infer_univ_dep0_dep1 dest_all;
   exists_term, infer_univ_dep0_dep1 dest_exists;
   or_term, infer_univ_dep0_dep0 dest_or;
   and_term, infer_univ_dep0_dep0 dest_and;
   implies_term, infer_univ_dep0_dep0 dest_implies;
   iff_term, infer_univ_dep0_dep0 dest_iff;
   not_term, Typeinf.infer_map dest_not
]

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

(*
 * Move hyps dependeing on the var to the conclusion.
 *)
(* unused
let rec intersects vars fv =
   match vars with
      [] ->
         false
    | v :: tl ->
         if List.mem v fv then
            true
         else
            intersects tl fv
*)

doc <:doc<
   @tactics

   The @hrefmodule[Itt_logic] module defines several tactics for
   reasoning in the @Nuprl type theory.  The tactics perform
   @emph{generic} reasoning of @Nuprl sequents.

   @begin[description]
   @item{@tactic[moveToConclT];
   {  The @tt[moveToConclT] tactic ``moves'' a hypothesis to the conclusion
      using the implication form.  The generic usage is as follows:

      $$
      @rulebox{moveToConclT; i;
      <<sequent{ <H>; <J> >- all x:'T_1. 'T_2}>>;
      <<sequent{ <H>; "i. x": 'T_1; <J> >- 'T_2}>>.}
      $$

      The argument $i$ is the index of the hypothesis.  In some
      cases, there may be additional hypotheses following
      $x@colon T_1$ that @emph{depend} on the hypothesis $x$.
      These hypotheses are also moved to the conclusion.

      $$
      @rulebox{moveToConclT; @tt[2];
      <<sequent{ <H>; j: <:doc<@int>> >- all i:(<:doc<@int>>).(<:doc< (i < j) @Rightarrow T_2[i]>>)}>>;
      <<sequent{ <H>; i:<:doc<@int>>; j: <:doc<@int>>; <:doc<i < j>> >- 'T_2['i]}>>}
      $$
   }}
   @end[description]
   @docoff
>>

(* unused
let none_var = Lm_symbol.add "none"
*)

let moveToConclT =
   let err = RefineError("moveToConclT",StringError "is a context") in
   let rec tac len goal = function
      (i, v, hyp) :: tl ->
         if is_var_free v goal then
            let goal' = mk_all_term v hyp goal in
               assertT goal'
               thenLT [thinT i thenT tac len goal' tl;
                       all_elim (len + 1) (mk_var_term v) (**)
                          thenLT [equalityAxiom i; hypothesis (-1)]]

         else
            let goal' = mk_implies_term hyp goal in
               assertT goal'
               thenLT [thinT i thenT tac len goal' tl;
                       (implies_elim (len + 1)) thenLT [hypothesis i; hypothesis (-1)]]
    | [] ->
         idT
   in
   let rec collect hyps len i vars indices =
      if i > len then
         indices
      else
         match SeqHyp.get hyps (i - 1) with
            Hypothesis (v, hyp) ->
               if is_some_var_free vars hyp then
                  collect hyps len (i + 1) (v :: vars) ((i, v, hyp) :: indices)
               else
                  collect hyps len (i + 1) (Lm_list_util.tryremove v vars) indices
          | Context _ ->
               collect hyps len (i + 1) vars indices
   in argfunT (fun i p ->
      let i = Sequent.get_pos_hyp_num p i in
      let hyps = (Sequent.explode_sequent_arg p).sequent_hyps in
         match SeqHyp.get hyps (i - 1) with
            Context _ -> raise err
          | Hypothesis (v, hyp) ->
               let len = SeqHyp.length hyps in
                  tac len (Sequent.concl p) (collect hyps len (i+1) [v] [i, v, hyp]))

doc <:doc<
   @begin[description]
   @item{@tactic[univCDT], @tactic[genUnivCDT];
    {   The @tt[univCDT] and @tt[genUnivCDT] tactics
        apply introduction reasoning on the goal.  The @tt[univCDT]
        tactic decomposes universal quantifications, implications,
        and function spaces.  The @tt[genUnivCDT] tactic also
        chains through conjunctions and bi-conditionals.

        $$
        @rulebox{univCDT; @space;
         <<sequent{ <H>; x_1: 'T_1; math_cdots; x_n: 'T_n >- <:doc<T_{n + 1}>>}>>@cr
         <<sequent{ <H>; x_1: 'T_1; math_cdots; (<:doc<x_{n - 1}@colon T_{n - 1}>>) >- "type"{'T_n}}>>@cr
         @vdots@cr
         <<sequent{ <H> >- "type"{'T_1}}>>;
         <<sequent{ <H> >- all x_1:'T_1.(<:doc< @ldots @all{x_n; T_n; T_{n + 1}}>>)}>>}
        $$}}
   @end[description]
   @docoff
>>
let univCDT =
   let rec tac p =
      let concl = Sequent.concl p in
         if is_all_term concl
            || is_dfun_term concl
            || is_implies_term concl
         then
            dT 0 thenMT (funT tac)
         else
            idT
   in
      funT tac

let genUnivCDT =
   let rec tac p =
      let concl = Sequent.concl p in
         if is_all_term concl
            || is_dfun_term concl
            || is_implies_term concl
            || is_and_term concl
            || is_prod_term concl
            || is_iff_term concl
         then
            dT 0 thenMT (funT tac)
         else
            idT
   in
      funT tac

doc <:doc<
   @begin[description]
   @item{@tactic[instHypT];
    {   The @tt[instHypT] tactic performs instantiation
        of a hypothesis.  The hypothesis must be a universal quantification
        or an implication.

        $$
        @rulebox{instHypT; t_1@space @cdots  t_n;
         <<sequent{ <H>; y: all x_1: 'T_1.(<:doc< @ldots T_{n + 1}[x_1, @ldots, x_n]>>); <J['y]>;
                        z: <:doc<T_{n + 1}[t_1, @ldots, t_n]>> >- 'C}>>@cr
         <<sequent{ <H>; y: all x_1: 'T_1.(<:doc< @ldots T_{n + 1}[x_1, @ldots, x_n]>>); <J['y]> >-
                          't_1 in 'T_1}>>@cr
         @vdots@cr
         <<sequent{ <H>; y: all x_1: 'T_1.(<:doc<@ldots . T_{n + 1}[x_1, @ldots, x_n]>>); <J['y]> >-
                          't_n in 'T_n}>>;
         <<sequent{ <H>; y : all x_1: 'T_1.(<:doc<@ldots . T_{n + 1}[x_1, @ldots, x_n]>>); <J['y]> >- 'C}>>}
        $$}}
   @end[description]
   @docoff
>>
let instHypT args i =
   let rec inst i firstp args = funT (fun p ->
      match args with
         [] ->
            idT
       | arg :: args' ->
            let hyp = Sequent.nth_hyp p i in
            let tailT args =
               if firstp then
                  inst ((Sequent.hyp_count p) + 1) false args
               else
                  thinT i thenT inst i false args
            in
               if is_all_term hyp then
                  all_elim i arg thenMT tailT args'
               else if is_dfun_term hyp then
                  withT arg (dT i) thenMT (thinT (-1) thenT tailT args')
               else if is_implies_term hyp || is_fun_term hyp then
                  implies_elim i thenMT tailT args
               else
                  raise (RefineError ("instHypT", StringTermError ("hyp is not quantified", hyp))))
   in
      thinningT false (inst i true args)

(*
 * This type is used to collect the arguments to instantiate.
 *)
type formula_args =
   AllTerm of var * term
 | ImpliesTerm
 | IffLeft
 | IffRight

(*
 * Print an info list.
 *)
let eprint_info info =
   let print_item = function
      AllTerm (v, t) ->
         eprintf "\tAllTerm %a: %a\n" output_symbol v SimplePrint.print_simple_term_fp t
    | ImpliesTerm ->
         eprintf "\tImpliesTerm\n"
    | IffLeft ->
         eprintf "\tIffLeft\n"
    | IffRight ->
         eprintf "\tIffRight\n"
   in
      List.iter print_item info;
      eprintf "\t.%t" eflush

(*
 * Lookup and remove a value from an association list.
 *)
let rec assoc v = function
   (v', t) :: tl ->
      if Lm_symbol.eq v' v then
         t, tl
      else
         let t', tl = assoc v tl in
            t', (v', t) :: tl
 | [] ->
      mk_var_term v, []

(*
 * Check for exact matches.
 *)
let check_subst subst =
   let check (v, t) =
      if !debug_auto then
         eprintf "check_subst: checking %a/%a%t" output_symbol v SimplePrint.print_simple_term_fp t eflush;
      if not (is_var_term t && dest_var t = v) then
         raise (RefineError ("check_subst", StringError "bad match"))
   in
      List.iter check subst

(*
 * Instantiate the vars with the values in the substitution.
 * If any vars in the subst don't match, they are global,
 * and they should match exactly.
 *)
let instantiate_vars args subst =
   if !debug_auto then
      begin
            eprintf "instantiate_vars: got subst\n";
            List.iter (fun (v,t) -> eprintf "\t%a: %a%t" output_symbol v SimplePrint.print_simple_term_fp t eflush) subst
      end;
   let rec collect result args subst =
      match args with
         [] ->
            check_subst subst;
            result
       | hd::tl ->
            match hd with
               AllTerm (v, t) ->
                  let t', subst' = assoc v subst in
                     collect (AllTerm (v, t') :: result) tl subst'
             | ImpliesTerm
             | IffLeft
             | IffRight ->
                  collect (hd :: result) tl subst
   in
      collect [] args subst

(*
 * Walk down an implication and look for the goal.
 *)
let rec match_goal args form goal =
   try
      if !debug_auto then
         eprintf "Matching form%t" eflush;
      let subst = match_terms [] form goal in
      let info = instantiate_vars args subst in
         if !debug_auto then
            eprintf "Form matched%t" eflush;
         info
   with
      RefineError _ ->
         if is_all_term form then
            let v, v_T, v_P = dest_all form in
               match_goal (AllTerm (v, v_T) :: args) v_P goal
         else if is_dfun_term form then
            let v, v_T, v_P = dest_dfun form in
               match_goal (AllTerm (v, v_T) :: args) v_P goal
         else if is_implies_term form then
            let v_T, v_P = dest_implies form in
               match_goal (ImpliesTerm :: args) v_P goal
         else if is_fun_term form then
            let v_T, v_P = dest_fun form in
               match_goal (ImpliesTerm :: args) v_P goal
         else if is_iff_term form then
            let left, right = dest_iff form in
               try match_goal (IffLeft :: args) left goal with
                  RefineError _ ->
                     match_goal (IffRight :: args) right goal
         else
            raise (RefineError ("match_goal", StringError "no match"))

doc <:doc<
   @begin[description]
   @item{@tactic[backThruHypT];
    {   The @tt[backThruHypT] performs backward-chaining through a
        hypothesis.  The conclusion must match a suffix of the hypothesis,
        which must be a sequence of universal quantifications or
        implications through that suffix.

        $$
        @rulebox{backThruHypT; i;
         <<sequent{ <H>; y: all x_1:'T_1.(<:doc<@ldots . T_{n + 1}[x_1, @ldots, x_n]>>); <J['y]> >-
                           't_1 in 'T_1}>>@cr
         @vdots@cr
         <<sequent{ <H>; y: all x_1:'T_1.(<:doc<@ldots . T_{n + 1}[x_1, @ldots, x_n]>>); <J['y]> >-
                           't_n in 'T_n}>>;
         <<sequent{ <H>; y: all x_1:'T_1.(<:doc<@ldots . T_{n + 1}[x_1, @ldots, x_n]>>); <J['y]> >-
                        (<:doc<T_{n + 1}[t_1, @ldots, t_n]>>)}>>}
        $$

        The @tt[backThruHypT] computes the argument terms $t_1, @ldots, t_n$ by matching
        the goal with the hypothesis.}}
   @end[description]
   @docoff
>>
let backThruHypT = argfunT (fun i p ->
   if !debug_auto then
      eprintf "Starting backThruHyp %d%t" i eflush;
   let rec tac info i firstp = funT (fun p ->
      match info with
          [] ->
             hypothesis i
        | hd :: args ->
             if !debug_auto then
                eprintf "\tbackThruHyp step%t" eflush;
             let tailT =
                if firstp then
                   [idT; tac args ((Sequent.hyp_count p) + 1) false]
                else
                   [thinT i; thinT i thenT tac args i false]
             in
                match hd with
                   ImpliesTerm ->
                      dT i thenLT tailT
                 | IffRight ->
                      dT i thenT thinT (i + 1) thenT dT i thenLT tailT
                 | IffLeft ->
                      dT i thenT thinT i thenT dT i thenLT tailT
                 | AllTerm (v, t) ->
                      withT t (dT i) thenLT tailT)
   in
   let info = match_goal [] (Sequent.nth_hyp p i) (Sequent.concl p) in
      if !debug_auto then
         begin
            eprintf "backThruHyp %d%t" i eflush;
            eprint_info info
         end;
      thinningT false (tac info i true))

doc <:doc<
   @begin[description]
   @item{@tactic[assumT];
    {   @emph{Assumptions} correspond to the subgoals of the outermost
        theorem statement.  The @tt[assumT] tactic instantiates an
        assumption as a universally quantified hypothesis.

        $$
        @rulebox{assumT; i;
         <<sequent{ <H>; math_ldots >- 'T_1}>>@cr
         @vdots@cr
         <<sequent{ <H>; x_1: 'A_1; math_cdots; x_n: 'A_n >- 'T_i}>>@cr
         @vdots@cr
         <<sequent{ <H>; math_ldots >- 'T_m}>>@cr
         @hline
         <<sequent{ <H>; <J>; w: all x_1: 'A_1.(<:doc<@ldots. @all{x_n; A_n; T_i}>>) >- 'C}>>@cr
         <<sequent{ <H>; <J> >- "type"{'A_1}}>>@cr
         @vdots@cr
         <<sequent{ <H>; <J> >- "type"{'A_n}}>>;

         <<sequent{ <H>; math_ldots >- 'T_1}>>@cr
         @vdots@cr
         <<sequent{ <H>; x_1: 'A_1; math_cdots; x_n: 'A_n >- 'T_i}>>@cr
         @vdots@cr
         <<sequent{ <H>; math_ldots >- 'T_m}>>@cr
         @hline
         <<sequent{ <H>; <J> >- 'C}>>}
        $$}}
   @end[description]
   @docoff
>>
let assum_term goal assum =
   (*
    * Compute the number of matching hyps.
    * This is approximate.
    *)
   let eassum = TermMan.explode_sequent assum in
   let egoal = TermMan.explode_sequent goal in
   let index = Match_seq.match_some_hyps egoal eassum in
   let _ =
      if !debug_auto then
         eprintf "Last_match: %d%t" (succ index) eflush
   in
   let hyps = eassum.sequent_hyps in
   let len = SeqHyp.length hyps in

   (* Construct the assumption as a universal formula *)
   let rec collect j assum =
      if j = 0 then
         assum, 1
      else let j = pred j in
         match SeqHyp.get hyps j with
            Hypothesis (v, hyp) when is_var_free v assum ->
               collect j (mk_all_term v hyp assum)
          | Hypothesis (_, hyp) when j >= index ->
               collect j (mk_implies_term hyp assum)
          | _ -> assum, j + 2
   in
   let res = collect len eassum.sequent_concl in
      if !debug_auto then
         eprintf "Found assumption: %a%t" debug_print (fst res) eflush;
      res

let make_assumT i goal assum form index tac =
   let len = TermMan.num_hyps assum in

   (* Call intro form on each arg *)
   let rec introT j =
      if j > len then begin
         Itt_struct.nthAssumT i
      end else
         (dT 0 thenMT introT (succ j))
   in
      tryAssertT form (introT index) tac

let assumT = argfunT (fun i p ->
   let goal = Sequent.goal p in
   let assum = Sequent.nth_assum p i in
   let form, index = assum_term goal assum in
      make_assumT i goal assum form index (addHiddenLabelT "main"))

let assumsT l =
   match l with
      [] ->
         idT
    | [i] ->
         assumT i
    | i :: l ->
         List.fold_left (fun tac i ->
               tac thenT assumT i) (assumT i) l

doc <:doc<
   @begin[description]
   @item{@tactic[backThruAssumT];
    { The @tt[backThruAssumT] performs backward chaining similar
      to the @hreftactic[backThruHypT], but on an @emph{assumption}.}}
   @end[description]
   @docoff
>>
let backThruAssumT i =
   assumT i thenMT (backThruHypT (-1) thenT thinT (-1))

doc <:doc<
   @begin[description]
   @item{@tactic[genAssumT];
    {The @tt[genAssumT] generalizes on an assumption.

     $$
     @rulebox{genAssumT; i;
      <<sequent{ <H>; math_ldots >- 'T_1}>>@cr
      @vdots@cr
      <<sequent{ <H> >- 't in 'T_i}>>@cr
      @vdots@cr
      <<sequent{ <H>; math_ldots >- 'T_n}>>@cr
      @hline
      <<sequent{ <H>; x:'T_i >- 'C}>>;

      <<sequent{ <H>; math_ldots >- 'T_1}>>@cr
      @vdots@cr
      <<sequent{ <H> >- 't in 'T_i}>>@cr
      @vdots@cr
      <<sequent{ <H>; math_ldots >- 'T_n}>>@cr
      @hline
      <<sequent{ <H> >- 'C}>>}
     $$}}
   @end[description]
   @docoff
>>
let genAssumT =
   let var_v = Lm_symbol.add "v" in argfunT (fun indices p ->
      let goal = Sequent.goal p in
      let len = Sequent.num_assums p in
      let _ =
         List.iter (fun i ->
               if i <= 0 || i > len then
                  raise (RefineError ("genAssumT", StringIntError ("assum index is out of range", i)))) indices
      in
      let rec make_gen_term t = function
         [] ->
            t, hypothesis (-1), idT
       | i :: indices ->
            let t, tac1, tac2 = make_gen_term t indices in
            let t' = TermMan.concl (Sequent.nth_assum p i) in
            if is_member_term t' then
               let t_type, t_var, _ = dest_equal t' in
                  (if is_var_term t_var then
                     mk_all_term (dest_var t_var) t_type t
                  else
                     let v = maybe_new_var_set var_v (free_vars_terms [t;t_var]) in
                        mk_all_term v t_type (var_subst t t_var v)),
                  (all_elim (-1) t_var thenLT [nthAssumT i; tac1]),
                  (all_intro thenLT [equalTypeT t_var t_var thenT nthAssumT i; idT])
            else
               mk_implies_term t' t,
               (implies_elim (-1) thenLT [nthAssumT i; tac1]),
               (implies_intro thenLT [typeAssertT thenT nthAssumT i; tac2])
      in
      let t, tac1, tac2 = make_gen_term (TermMan.concl goal) indices in
         (assertT t thenLT [tac2; tac1]))

(************ logic instance for j-prover in refiner/reflib/jall.ml  **********)

module Itt_JLogic =
struct
   open Jlogic_sig

   let is_all_term = is_all_term
   let dest_all = dest_all
   let is_exists_term = is_exists_term
   let dest_exists = dest_exists
   let is_and_term t = is_and_term t || is_iff_term t
   let dest_and t =
      if is_iff_term t then let a, b = dest_iff t in
         (mk_implies_term a b, mk_implies_term b a)
      else
         dest_and t
   let is_or_term = is_or_term
   let dest_or = dest_or
   let is_implies_term = is_implies_term
   let dest_implies = dest_implies
   let is_not_term = is_not_term
   let dest_not = dest_not

   let is_box_term _ = false
   let dest_box _ =
      raise (Invalid_argument "Itt_logic: at this time there is no box-modality in ITT")

   type inference = (term_subst -> (term * (tactic -> tactic)) list -> tactic) list
   let empty_inf = []

   let rec find_in_assums term tac = function
      [] ->
         raise (RefineForceError("Itt_logic.Itt_JLogic.find_in_assums", "internal error",
                  TermError(term)))
    | (t, tac') :: _ when alpha_equal term t -> tac' (tac (-1))
    | _ :: assums -> find_in_assums term tac assums

   let find_hyp term assums tac = funT (fun p ->
      let hyps = (explode_sequent_arg p).sequent_hyps in
      let len = SeqHyp.length hyps in
      let rec aux i =
         if i = len then find_in_assums term tac assums
         else match SeqHyp.get hyps i with
            Hypothesis(_,t) when alpha_equal t term -> tac (i+1)
          | _ -> aux (i+1)
      in
         aux 0)

   let tryappend_subst subst t assums tact i = funT (fun p ->
      tact (match_terms subst t (Sequent.nth_hyp p i)) assums)

   let append_subst subst t v assums tact =
      match (dest_term t).term_terms with
         [_;bt] ->
            let bt = dest_bterm bt in
            begin match bt.bvars with
               [dv] ->
                  onSomeHypT (tryappend_subst subst (subst1 bt.bterm dv v) assums tact)
             | _ -> raise (Invalid_argument "Itt_logic.append_subst: internal error")
            end
       | _ -> raise (Invalid_argument "Itt_logic.append_subst: internal error")

   let goal_append_subst subst t v assums tact =
      match (dest_term t).term_terms with
         [_;bt] ->
            let bt = dest_bterm bt in
            begin match bt.bvars with
               [dv] ->
                  funT (fun p -> tact (match_terms subst (subst1 bt.bterm dv v) (Sequent.concl p)) assums)
             | _ -> raise (Invalid_argument "Itt_logic.goal_append_subst: internal error")
            end
       | _ -> raise (Invalid_argument "Itt_logic.goal_append_subst: internal error")

   let thenTi tac1 tac2 i = tac1 i thenT tac2
   let thenLTi tac1 tacl i = tac1 i thenLT tacl
   let aTi tac t i = tac i t

   let and_elim =
      argfunT (fun i p -> if is_iff_term (Sequent.nth_hyp p i) then iff_elim i else and_elim i)

   let append_inf inf hyp inst_term r =
      match r, inf with
         Ax,  _ -> (fun subst assums -> find_hyp (apply_subst subst hyp) assums hypothesis ) :: inf
       | Andl,t::ts -> (fun subst assums -> (find_hyp (apply_subst subst hyp) assums (thenTi and_elim (t subst assums)))) :: ts
       | Negl,t::ts -> (fun subst assums -> (find_hyp (apply_subst subst hyp) assums (thenTi not_elim (t subst assums)))) :: ts
       | Orl, t1::t2::ts ->
            (fun subst assums ->
               (find_hyp (apply_subst subst hyp) assums (thenLTi or_elim [t1 subst assums; t2 subst assums])))
            :: ts
       | Impl,t1::t2::ts ->
            (fun subst assums ->
               (find_hyp (apply_subst subst hyp) assums (thenLTi implies_elim [t1 subst assums; t2 subst assums])))
            :: ts
       | Andr,t1::t2::ts -> (fun subst assums -> and_intro thenLT [t1 subst assums; t2 subst assums]) :: ts
       | Orr1,t::ts -> (fun subst assums -> or_intro_left thenLT [idT; t subst assums]) :: ts
       | Orr2,t::ts -> (fun subst assums -> or_intro_right thenLT [idT; t subst assums]) :: ts
       | Impr,t::ts -> (fun subst assums -> implies_intro thenLT [idT; t subst assums]) :: ts
       | Negr,t::ts -> (fun subst assums -> not_intro thenLT [idT; t subst assums]) :: ts
       | Exr, t::ts ->
            (fun subst assums ->
               exists_intro (apply_subst subst inst_term) thenLT [idT; t subst assums; idT]) :: ts
       | Alll,t::ts ->
            (fun subst assums ->
               (find_hyp (apply_subst subst hyp) assums
                  (thenLTi (aTi all_elim (apply_subst subst inst_term)) [idT; t subst assums])))
            :: ts
       | Exl, t::ts ->
            (fun subst assums ->
               (find_hyp (apply_subst subst hyp) assums
                  (thenTi exists_elim (append_subst subst (apply_subst subst hyp) inst_term assums t))))
            :: ts
       | Allr,t::ts ->
            (fun subst assums ->
               all_intro thenLT [idT;goal_append_subst subst (apply_subst subst hyp) inst_term assums t])
            :: ts
    (* | Orr, ->  *)
       | Fail,_ -> raise (RefineError("Itt_JLogic.create_inf", StringError "failed"))
       | _ -> raise (Invalid_argument "Itt_JLogic.create_inf")
end;;

module ITT_JProver = Jall.JProver (Itt_JLogic);;

let base_jproverT =
   let rec make_j_assums p goal len i =
      if i > len then
         []
      else
         let assum = Sequent.nth_assum p i in
         let rest = make_j_assums p goal len (succ i) in
            try
               let form, index = assum_term goal assum in
                  (form, make_assumT i goal assum form index) :: rest
            with
               RefineError _ ->
                  rest
   in
   let jprogressT = argfunT (fun t p ->
      if alpha_equal (Sequent.concl p) t then
         raise (RefineError ("Itt_logic.jprogressT", StringError "JProver failed to make progress"))
      else
         idT)
   in
   let logic_opnames =
      OpnameSet.of_list
         [all_opname; exists_opname; or_opname; and_opname; implies_opname; iff_opname; not_opname]
   in
   let logic_opnames_num = OpnameSet.cardinal logic_opnames in
   let rec get_useful_opnames opnames t =
      if (is_or_term t) || (is_and_term t) || (is_implies_term t) || (is_iff_term t) then
         let t1, t2 = two_subterms t in
            get_useful_opnames (get_useful_opnames opnames t1) t2
      else if is_all_term t then
         let _, _, t = dest_all t in
            get_useful_opnames opnames t
      else if is_exists_term t then
         let _, _, t = dest_exists t in
            get_useful_opnames opnames t
      else if is_not_term t then
         get_useful_opnames opnames (one_subterm t)
      else
         OpnameSet.add opnames (opname_of_term t)
   in
   let useful_opname opnames t =
      if OpnameSet.mem logic_opnames (opname_of_term t) then
         get_useful_opnames opnames t
      else
         opnames
   in
   let useful_hyp opnames t = OpnameSet.mem opnames (opname_of_term t) in
   (fun def_mult p ->
      let goal = Sequent.goal p in
      let seq = TermMan.explode_sequent goal in
      let () =
         if not (alpha_equal itt_sequent_arg seq.sequent_args) then
            raise (RefineError("Itt_logic.base_jproverT", StringError "Not an ITT sequent"))
      in
      let assums = make_j_assums p goal (Sequent.num_assums p) 1 in
      let hyps = (Sequent.all_hyps p) @ (List.map fst assums) in
      let concl = seq.sequent_concl in
      let opnames = List.fold_left useful_opname logic_opnames (concl :: hyps) in
      let hyps =
         if OpnameSet.cardinal opnames = logic_opnames_num then
            raise (RefineError("Itt_logic.base_jproverT", StringError "No logical formulas found in the goal"))
         else
            List.filter (useful_hyp opnames) hyps
      in
      let mult_limit =
         match Sequent.get_int_arg p "jprover" with
            None -> def_mult
          | Some _ as ml -> ml
      in
         match ITT_JProver.prover mult_limit hyps concl with
            [t] ->
               let substs =
                  match get_with_arg p with
                     Some t -> [Lm_symbol.make "n_jprover" 0, t]
                   | None -> []
               in
                  t substs assums thenT jprogressT concl
          | _ ->
               raise (Invalid_argument "Problems decoding ITT_JProver.prover proof"))

declare jprover : SelectOption
let jprover_selector = << select["jprover":t] >>
let jprover_options = rule_labels_of_terms [jprover_selector]

let simple_jproverT =
   let err = RefineError("Itt_logic.simple_jproverT", StringError ("JProver is excluded")) in
      funT (fun p ->
         if rule_labels_are_allowed (get_option_args p) jprover_options then
            base_jproverT (Some 1) p
         else
            raise err)

let jproverT = argfunT base_jproverT (Some 100)

(************************************************************************
 * AUTO TACTIC                                                          *
 ************************************************************************)

let jprover_prec = create_auto_prec [trivial_prec] [d_prec]

let resource auto +=
     { auto_name = "simple_jproverT";
       auto_prec = jprover_prec;
       auto_tac = simple_jproverT;
       auto_type = AutoComplete;
     }

let jAutoT i = withIntT "jprover" i autoT

let resource menubar +=
    [<< menuitem["refine", "jAutoT 5", "Command('refine jAutoT 5')"] >>, refine_is_enabled]

(* aux is either a hyp or an assum *)
let autoBackT compare_aux get_aux tac_aux onsome auto_aux =
   let mem aux goal (aux', goal') =
      compare_aux aux aux' && alpha_equal goal goal'
   in
   let backHyp tac history (i: int) = funT (fun p ->
      let goal = Sequent.goal p in
      let aux = get_aux p i in
      let tac' =
         if List.exists (mem aux goal) history then failT else
            tac_aux i thenT tac ((aux,goal)::history)
      in
         tac')
   in
   let rec auto_back history =
      auto_aux thenT tryT (onsome (backHyp auto_back history))
   in
      auto_back []

let hypAutoT =
   autoBackT alpha_equal Sequent.nth_hyp backThruHypT onSomeHypT autoT

let logicAutoT = autoBackT (==) (fun p _ -> p) backThruAssumT onSomeAssumT hypAutoT

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
