(*
 * Lists.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
 *
 * Copyright (C) 1998-2006 MetaPRL Group, Cornell University and
 * California Institute of Technology
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
 * Author: Jason Hickey <jyh@cs.cornell.edu>
 * Modified by: Aleksey Nogin <nogin@cs.caltech.edu>
 *
 *)
extends Itt_equal
extends Itt_dfun

open Lm_symbol

open Refiner.Refiner.TermType

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare nil
declare cons{'a; 'b}

declare list{'a}
declare list_ind{'e; 'base; h, t, f. 'step['h; 't; 'f]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_cons
prec prec_list

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Reduction.
 *)
rewrite reduce_listindNil :
   list_ind{nil; 'base; h, t, f. 'step['h; 't; 'f]} <--> 'base

rewrite reduce_listindCons :
   list_ind{('u :: 'v); 'base; h, t, f. 'step['h; 't; 'f]} <-->
      'step['u; 'v; list_ind{'v; 'base; h, t, f. 'step['h; 't; 'f]}]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext list(A)
 * by listFormation
 *
 * H >- Ui ext A
 *)
rule listFormation :
   sequent { <H> >- univ[i:l] } -->
   sequent { <H> >- univ[i:l] }

(*
 * H >- list{A} Type
 * by listType
 * H >- A Type
 *)
rule listType :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- "type"{list{'A}} }

(*
 * H >- list(A) = list(B) in Ui
 * by listEquality
 *
 * H >- A = B in Ui
 *)
rule listEquality :
   sequent { <H> >- 'A = 'B in univ[i:l] } -->
   sequent { <H> >- list{'A} = list{'B} in univ[i:l] }

(*
 * H >- list(A) ext nil
 * by nilFormation
 *
 * H >- A = A in Ui
 *)
rule nilFormation :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- list{'A} }

(*
 * H >- nil = nil in list(A)
 * by nilEquality
 *
 * H >- A = A in Ui
 *)
rule nilEquality :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- nil in list{'A} }

(*
 * H >- list(A) ext cons(h; t)
 * by consFormation
 *
 * H >- A ext h
 * H >- list(A) ext t
 *)
rule consFormation :
   sequent { <H> >- 'A } -->
   sequent { <H> >- list{'A} } -->
   sequent { <H> >- list{'A} }

(*
 * H >- u1::v1 = u2::v2 in list(A)
 * consEquality
 *
 * H >- u1 = u2 in A
 * H >- v1 = v2 in list(A)
 *)
rule consEquality :
   sequent { <H> >- 'u1 = 'u2 in 'A } -->
   sequent { <H> >- 'v1 = 'v2 in list{'A} } -->
   sequent { <H> >- cons{'u1; 'v1} = cons{'u2; 'v2} in list{'A} };;

(*
 * H; l: list(A); J[l] >- C[l]
 * by listElimination w u v
 *
 * H; l: list(A); J[l] >- C[nil]
 * H; l: list(A); J[l]; u: A; v: list(A); w: C[v] >- C[u::v]
 *)
rule listElimination 'H :
   sequent { <H>; l: list{'A}; <J['l]> >- 'C[nil] } -->
   sequent { <H>; l: list{'A}; <J['l]>; u: 'A; v: list{'A}; w: 'C['v] >- 'C['u::'v] } -->
   sequent { <H>; l: list{'A}; <J['l]> >- 'C['l] }

(*
 * H >- rec_case(e1; base1; u1, v1, z1. step1[u1; v1]
 *      = rec_case(e2; base2; u2, v2, z2. step2[u2; v2]
 *      in T[e1]
 *
 * by list_indEquality lambda(r. T[r]) list(A)
 *
 * H >- e1 = e2 in list(A)
 * H >- base1 = base2 in T[nil]
 * H, u: A; v: list(A); w: T[v] >- step1[u; v; w] = step2[u; v; w] in T[u::v]
 *)
rule list_indEquality lambda{l. 'T['l]} list{'A} :
   sequent { <H> >- 'e1 = 'e2 in list{'A} } -->
   sequent { <H> >- 'base1 = 'base2 in 'T[nil] } -->
   sequent { <H>; u: 'A; v: list{'A}; w: 'T['v] >-
             'step1['u; 'v; 'w] = 'step2['u; 'v; 'w] in 'T['u::'v]
           } -->
   sequent { <H> >- list_ind{'e1; 'base1; u1, v1, z1. 'step1['u1; 'v1; 'z1]}
                   = list_ind{'e2; 'base2; u2, v2, z2. 'step2['u2; 'v2; 'z2]}
                   in 'T['e1]
           }

(*
 * H >- list(A1) <= list(A2)
 * by listSubtype
 *
 * H >- A1 <= A2
 *)
rule listSubtype :
   sequent { <H> >- \subtype{'A1; 'A2} } -->
   sequent { <H> >- \subtype{list{'A1}; list{'A2}}}

(*
 * Nil is canonical.
 *)
rule nilSqequal 'T :
   sequent { <H> >- 'u = nil in list{'T} } -->
   sequent { <H> >- 'u ~ nil }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val list_term : term
val is_list_term : term -> bool
val dest_list : term -> term
val mk_list_term : term -> term

val nil_term : term
val is_nil_term : term -> bool

val is_cons_term : term -> bool
val dest_cons : term -> term * term
val mk_cons_term : term -> term -> term

val is_list_ind_term : term -> bool
val dest_list_ind : term -> term * term * var * var * var * term
val mk_list_ind_term : term -> term -> var -> var -> var -> term -> term

val mk_list_of_list : term list -> term
val dest_list_term  : term -> term list

(************************************************************************
 * Grammar.
 *)
declare itt_list{'l} : Nonterminal
declare itt_nonempty_list{'l} : Nonterminal

production xterm_term{cons{'t1; 't2}} <--
   xterm_term{'t1}; tok_colon_colon; xterm_term{'t2}

production xterm_term{'l} <--
   tok_left_brack; itt_list{'l}; tok_right_brack

production itt_list{nil} <--
   (* empty *)

production itt_list{'l} <--
   itt_nonempty_list{'l}

production itt_nonempty_list{cons{'t; nil}} <--
   xterm_term{'t}

production itt_nonempty_list{cons{'t; 'l}} <--
   xterm_term{'t}; tok_semi; itt_list{'l}

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
