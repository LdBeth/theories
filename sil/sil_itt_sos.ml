(*
 * Operational semantics of the imperative programs,
 * coded in ITT.
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
 * Copyright (C) 1999 Jason Hickey, Cornell University
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

extends Itt_theory

extends Sil_state
extends Sil_programs
extends Sil_sos
extends Sil_itt_state

open Basic_tactics
open Base_rewrite

module TermMan = Refiner.Refiner.TermMan

open Sil_sos

(************************************************************************
 * EVALSTO DEFINITION                                                   *
 ************************************************************************)

(*
 * New terms we need to define the syntax.
 * prog is the abstraction of an expression over the state,
 * match splits the value/state pair returned by evaluation.
 *)
declare prog{s. 'e['s]}
declare "val"{'v; 's}
declare "match"{'t1; x, y. 't2['x; 'y]}
declare progof{'t}
declare stateof{'t}
declare exprof{'v}
declare valueof{'e}

prim_rw unfold_value : "value"{'v; 's2} <-->
   (Perv!"rewrite"{prog{s. eval{'v; 's}}; prog{s. "val"{progof{eval{'v; 's2}}; 's}}})

prim_rw unfold_evalsto : evalsto{'e1; 'e2} <-->
   (Perv!"rewrite"{'e1; 'e2})

prim_rw unfold_eq_int : Sil_sos!eq_int{number[i:n]; number[j:n]} <--> "assert"{.Itt_int_base!beq_int{.Itt_int_base!number[i:n]; .Itt_int_base!number[j:n]}}
prim_rw unfold_neq_int : Sil_sos!neq_int{number[i:n]; number[j:n]} <--> "assert"{bnot{.Itt_int_base!beq_int{.Itt_int_base!number[i:n]; .Itt_int_base!number[j:n]}}}

prim_rw unfold_eval : eval{'e; 's} <--> Itt_dfun!apply{'e; 's}
prim_rw unfold_prog : prog{s. 'e['s]} <--> Itt_dfun!lambda{s. 'e['s]}
prim_rw unfold_val : "val"{'v; 's} <--> Itt_dprod!pair{'v; 's}
prim_rw unfold_match : "match"{'t1; x, y. 't2['x; 'y]} <--> Itt_dprod!spread{'t1; x, y. 't2['x; 'y]}
prim_rw unfold_progof : progof{'t} <--> "match"{'t; x, y. 'x}
prim_rw unfold_stateof : stateof{'t} <--> "match"{'t; x, y. 'y}
prim_rw unfold_exprof : exprof{'v} <--> prog{s. "val"{'v; 's}}
prim_rw unfold_valueof : valueof{'e} <--> progof{eval{'e; .Sil_itt_state!empty}}

let fold_eq_int = makeFoldC << eq_int{number[i:n]; number[j:n]} >> unfold_eq_int
let fold_neq_int = makeFoldC << neq_int{number[i:n]; number[j:n]} >> unfold_neq_int
let fold_val = makeFoldC << "val"{'v; 's} >> unfold_val
let fold_evalsto = makeFoldC << evalsto{'e1; 'e2} >> unfold_evalsto
let fold_eval = makeFoldC << eval{'e; 's} >> unfold_eval
let fold_value = makeFoldC << "value"{'v; 'c} >> unfold_value
let fold_prog = makeFoldC << prog{s. 'e['s]} >> unfold_prog
let fold_match = makeFoldC << "match"{'t1; x, y. 't2['x; 'y]} >> unfold_match
let fold_progof = makeFoldC << "progof"{'t1} >> unfold_progof
let fold_stateof = makeFoldC << "stateof"{'t1} >> unfold_stateof
let fold_exprof = makeFoldC << exprof{'v} >> unfold_exprof
let fold_valueof = makeFoldC << valueof{'v} >> unfold_valueof

let eval_term = << eval{'e1; 's1} >>
let eval_opname = opname_of_term eval_term
let mk_eval_term = mk_dep0_dep0_term eval_opname

let val_term = << "val"{'v1; 's1} >>
let val_opname = opname_of_term val_term
let mk_val_term = mk_dep0_dep0_term val_opname

let progof_term = << progof{'t} >>
let progof_opname = opname_of_term progof_term
let mk_progof_term = mk_dep0_term progof_opname

let empty_term = << Sil_itt_state!empty >>

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_match
prec prec_match < prec_evalsto

dform prog_df : prog{s. 'e} =
   `"prog(" pushm[0] slot{'s} `"." hspace slot{'e} `")" popm

dform exprof_df : exprof{'v} =
   `"exprof(" slot{'v} `")"

dform valueof_df : valueof{'v} =
   `"valueof(" slot{'v} `")"

dform match_df : parens :: "prec"[prec_match] :: "match"{'t1; x, y. 't2} =
   szone pushm[3] keyword["match "] slot{'t1} keyword[" with"] hspace
   "val"{'x; 'y} `" ->" hspace slot{'t2} popm ezone

dform val_df : "val"{'v; 's} =
   `"val(" slot{'v} `"," slot{'s} `")"

dform progof_df : "progof"{'t} =
   `"progof(" slot{'t} `")"

dform stateof_df : "stateof"{'t} =
   `"stateof(" slot{'t} `")"

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Application of a program.
 *)
interactive_rw reduce_eval : eval{prog{s1. 'e1['s1]}; 's2} <--> 'e1['s2]
interactive_rw reduce_eval_exprof : eval{exprof{'v}; 's} <--> "val"{'v; 's}

interactive_rw reduce_match : "match"{."val"{'v; 's}; x, y. 't['x; 'y]} <--> 't['v; 's]

(*
 * Matching.
 *)
interactive_rw reduce_progof : progof{."val"{'v; 's}} <--> 'v
interactive_rw reduce_stateof : stateof{."val"{'v; 's}} <--> 's

let resource reduce += [
   << eval{prog{s1. 'e['s1]}; 's2} >>, wrap_reduce reduce_eval;
   << eval{exprof{'v}; 's} >>, wrap_reduce reduce_eval_exprof;
   (* << "value"{prog{s1. 'e['s1]}; 's2} >>, wrap_reduce reduce_value; *)
   << "match"{."val"{'v; 's}; x, y. 't['x; 'y]} >>, wrap_reduce reduce_match;
   << progof{."val"{'v; 's}} >>, wrap_reduce reduce_progof;
   << stateof{."val"{'v; 's}} >>, wrap_reduce reduce_stateof
]

interactive evals_identity {| intro [] |} :
   sequent { <H> >- evalsto{'t1; 't1} }

let rwevalT = argfunT (fun i p ->
   let assum = Sequent.nth_assum p i in
   let concl = TermMan.concl assum in
   let a, b = two_subterms concl in
   let t = mk_xrewrite_term a b in
      rewriteT t thenAT (rw fold_evalsto 0 ta))

(*
 * Value.
 *)
interactive value_thm :
   [main] sequent { <H> >- "value"{'e1; 's} } -->
   sequent { <H> >- Perv!"rewrite"{eval{'e1; 's}; ."val"{progof{eval{'e1; .Sil_itt_state!empty}}; 's}} }

let rwvalueT s2 i = funT (fun p ->
   let assum = Sequent.nth_assum p i in
   let b = TermMan.concl assum in
   let e2 = one_subterm b in
   let a = mk_eval_term e2 s2 in
   let b = mk_val_term (mk_progof_term (mk_eval_term e2 empty_term)) s2 in
   let t = mk_xrewrite_term a b in
      rewriteT t thenAT value_thm ta)

let rwvalueRevT s2 i = funT (fun p ->
   let assum = Sequent.nth_assum p i in
   let b = TermMan.concl assum in
   let e2 = one_subterm b in
   let b = mk_eval_term e2 s2 in
   let a = mk_val_term (mk_progof_term (mk_eval_term e2 empty_term)) s2 in
   let t = mk_xrewrite_term a b in
      rewriteT t thenAT (rewriteSymT thenT value_thm ta))

(*
 * Need eta-contraction.
 *)
prim_rw eta : prog{s. eval{'v; 's}} <--> 'v

(*
 * Squashing.
 *)
interactive squash_evalsto :
   sequent { <H> >- evalsto{'t1; 't2} } -->
   sequent { <H> >- evalsto{'t1; 't2} }

interactive squash_value :
   sequent { <H> >- "value"{'e1; 's} } -->
   sequent { <H> >- "value"{'e1; 's} }

let squash_evalstoT = squash_evalsto
let squash_valueT = squash_value

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * Translation between the states.
 *)
prim_rw unfold_empty1 : Sil_state!empty <--> Sil_itt_state!empty

prim_rw unfold_fetch1 : Sil_state!fetch{'s; 'l} <-->
   exprof{.Sil_itt_state!fetch{'s; valueof{'l}}}

prim_rw unfold_store1 : Sil_state!store{'s; 'l; 'v} <-->
   Sil_itt_state!store{'s; valueof{'l}; valueof{'v}}

prim_rw unfold_alloc1 : Sil_state!alloc{'s; 'v; s2, l. 't['s2; 'l]} <-->
   Sil_itt_state!alloc{'s; valueof{'v}; s2, l. 't['s2; pointer{'l}]}

(*
 * Numbers.
 *)
prim_rw unfold_snumber : Sil_programs!number[i:n] <--> exprof{.Itt_int_base!number[i:n]}

prim_rw unfold_add : Sil_programs!add{'e1; 'e2} <-->
   prog{s1.
      "match"{.eval{'e1; 's1}; v1, s2.
      "match"{.eval{'e2; 's2}; v2, s3.
         "val"{.Itt_int_base!add{'v1; 'v2}; 's3}}}}

prim_rw unfold_sub : Sil_programs!sub{'e1; 'e2} <-->
   prog{s1.
      "match"{.eval{'e1; 's1}; v1, s2.
      "match"{.eval{'e2; 's2}; v2, s3.
         "val"{.Itt_int_base!sub{'v1; 'v2}; 's3}}}}

prim_rw unfold_if : "if"{'e1; 'e2; 'e3; 'e4} <-->
   prog{s1.
      "match"{.eval{'e1; 's1}; v1, s2.
      "match"{.eval{'e2; 's2}; v2, s3.
         ifthenelse{.Itt_int_base!beq_int{'v1; 'v2}; .eval{'e3; 's3}; .eval{'e4; 's3}}}}}

(*
 * Disjoint union.
 *)
prim_rw unfold_inl : Sil_programs!inl{'e1} <--> prog{s1. "match"{.eval{'e1; 's1}; v1, s2. "val"{.Itt_union!inl{'v1}; 's2}}}
prim_rw unfold_inr : Sil_programs!inr{'e1} <--> prog{s1. "match"{.eval{'e1; 's1}; v1, s2. "val"{.Itt_union!inr{'v1}; 's2}}}

prim_rw unfold_decide : Sil_programs!decide{'e1; x. 'e2['x]; y. 'e3['y]} <-->
   prog{s1.
      "match"{.eval{'e1; 's1}; v1, s2.
         Itt_union!decide{'v1; x. eval{'e2[exprof{'x}]; 's2}; y. eval{'e3[exprof{'y}]; 's2}}}}

(*
 * Pairs.
 *)
prim_rw unfold_pair : Sil_programs!pair{'e1; 'e2} <-->
   prog{s1.
      "match"{.eval{'e1; 's1}; v1, s2.
      "match"{.eval{'e2; 's2}; v2, s3.
         "val"{.Itt_dprod!pair{'v1; 'v2}; 's3}}}}

prim_rw unfold_spread : Sil_programs!spread{'e1; x, y. 'e2['x; 'y]} <-->
   prog{s1.
      "match"{.eval{'e1; 's1}; v1, s2.
         Itt_dprod!spread{'v1; x, y.
            eval{'e2[exprof{'x}; exprof{'y}]; 's2}}}}

(*
 * Reference cells.
 *)
prim_rw unfold_dot : dot <--> exprof{it}

prim_rw unfold_pointer : pointer{'l} <-->
   exprof{'l}

prim_rw unfold_ref : ref{'e1} <-->
   prog{s1.
      "match"{.eval{'e1; 's1}; v1, s2.
         Sil_itt_state!alloc{'s2; 'v1; s3, l. "val"{'l; 's3}}}}

prim_rw unfold_deref : deref{'e1} <-->
   prog{s1.
      "match"{.eval{'e1; 's1}; v1, s2.
         "val"{.Sil_itt_state!fetch{'s2; 'v1}; 's2}}}

prim_rw unfold_assign : assign{'e1; 'e2} <-->
   prog{s1.
      "match"{.eval{'e1; 's1}; v1, s2.
      "match"{.eval{'e2; 's2}; v2, s3.
         "val"{it; .Sil_itt_state!store{'s3; 'v1; 'v2}}}}}

(*
 * Functions.
 *)
prim_rw unfold_lambda : Sil_programs!lambda{v. 'e1['v]} <-->
   exprof{Itt_dfun!lambda{v. 'e1['v]}}

prim_rw unfold_apply : Sil_programs!apply{'e1; 'e2} <-->
   prog{s1.
      "match"{.eval{'e2; 's1}; v2, s2.
      "match"{.eval{'e1; 's2}; v1, s3.
         eval{.Itt_dfun!apply{'v1; exprof{'v2}}; 's3}}}}

(************************************************************************
 * NATURAL SEMANTICS                                                    *
 ************************************************************************)

interactive exprof_value {| intro [] |} :
   sequent { <H> >- "value"{exprof{'e}; 's} }

interactive exprof_eval {| intro [] |} :
   sequent { <H> >- evalsto{eval{exprof{'e}; 's}; eval{exprof{'e}; 's}} }

(*
 * Number values.
 *)
interactive number_value :
   sequent { <H> >- "value"{.Sil_programs!number[i:n]; 's} }

interactive number_eval :
   sequent { <H> >- evalsto{eval{number[i:n]; 's}; eval{number[i:n]; 's}}}

interactive add_eval 's2 :
   [main] sequent { <H> >- evalsto{eval{'e1; 's1}; eval{number[i:n]; 's2}} } -->
   [main] sequent { <H> >- evalsto{eval{'e2; 's2}; eval{number[j:n]; 's3}} } -->
   sequent { <H> >- evalsto{eval{add{'e1; 'e2}; 's1}; eval{meta_sum[i:n, j:n]; 's3}} }

interactive sub_eval 's2 :
   [main] sequent { <H> >- evalsto{eval{'e1; 's1}; eval{number[i:n]; 's2}} } -->
   [main] sequent { <H> >- evalsto{eval{'e2; 's2}; eval{number[j:n]; 's3}} } -->
   sequent { <H> >- evalsto{eval{sub{'e1; 'e2}; 's1}; eval{meta_diff[i:n, j:n]; 's3}} }

interactive if_eval (number[i:n]) 's2 (number[j:n]) 's3 :
   [main] sequent { <H> >- evalsto{eval{'e1; 's1}; eval{number[i:n]; 's2}} } -->
   [main] sequent { <H> >- evalsto{eval{'e2; 's2}; eval{number[j:n]; 's3}} } -->
   [main] sequent { <H>; p: Sil_sos!eq_int{number[i:n]; number[j:n]} >- evalsto{eval{'e3; 's3}; eval{'v3; 's4}} } -->
   [main] sequent { <H>; p: Sil_sos!neq_int{number[i:n]; number[j:n]} >- evalsto{eval{'e4; 's3}; eval{'v3; 's4}} } -->
   sequent { <H> >- evalsto{eval{."if"{'e1; 'e2; 'e3; 'e4}; 's1}; eval{'v3; 's4}} }

(*
 * Union values.
 *)
interactive inl_value :
   [main] sequent { <H> >- "value"{'e1; 's} } -->
   sequent { <H> >- "value"{.Sil_programs!inl{'e1}; 's} }

interactive inr_value :
   [main] sequent { <H> >- "value"{'e1; 's} } -->
   sequent { <H> >- "value"{.Sil_programs!inr{'e1}; 's} }

interactive inl_eval :
   [main] sequent { <H> >- evalsto{eval{'e1; 's1}; eval{'v1; 's2}} } -->
   [main] sequent { <H> >- "value"{'v1; 's2} } -->
   sequent { <H> >- evalsto{eval{inl{'e1}; 's1}; eval{inl{'v1}; 's2}} }

interactive inr_eval :
   [main] sequent { <H> >- evalsto{eval{'e1; 's1}; eval{'v1; 's2}} } -->
   [main] sequent { <H> >- "value"{'v1; 's2} } -->
   sequent { <H> >- evalsto{eval{inr{'e1}; 's1}; eval{inr{'v1}; 's2}} }

interactive decide_left_eval 'v1 's2 :
   [main] sequent { <H> >- evalsto{eval{'e1; 's1}; eval{inl{'v1}; 's2}} } -->
   [main] sequent { <H> >- evalsto{eval{'e2['v1]; 's2}; eval{'v3; 's3}} } -->
   [main] sequent { <H> >- "value"{'v1; 's2} } -->
   sequent { <H> >- evalsto{eval{decide{'e1; x. 'e2['x]; y. 'e3['y]}; 's1}; eval{'v3; 's3}} }

interactive decide_right_eval 'v1 's2 :
   [main] sequent { <H> >- evalsto{eval{'e1; 's1}; eval{inr{'v1}; 's2}} } -->
   [main] sequent { <H> >- evalsto{eval{'e3['v1]; 's2}; eval{'v3; 's3}} } -->
   [main] sequent { <H> >- "value"{'v1; 's2} } -->
   sequent { <H> >- evalsto{eval{decide{'e1; x. 'e2['x]; y. 'e3['y]}; 's1}; eval{'v3; 's3}} }

(*
 * Pairs.
 *)
interactive pair_value :
   [main] sequent { <H> >- "value"{'e1; 's} } -->
   [main] sequent { <H> >- "value"{'e2; 's} } -->
   sequent { <H> >- "value"{pair{'e1; 'e2}; 's} }

interactive pair_eval 's2 :
   [wf] sequent { <H> >- "value"{'v1; 's2} } -->
   [wf] sequent { <H> >- "value"{'v2; 's3} } -->
   [main] sequent { <H> >- evalsto{eval{'e1; 's1}; eval{'v1; 's2}} } -->
   [main] sequent { <H> >- evalsto{eval{'e2; 's2}; eval{'v2; 's3}} } -->
   sequent { <H> >- evalsto{eval{pair{'e1; 'e2}; 's1}; eval{pair{'v1; 'v2}; 's3}} }

interactive spread_eval 'v1 'v2 's2 :
   [wf] sequent { <H> >- "value"{'v1; 's2} } -->
   [wf] sequent { <H> >- "value"{'v2; 's2} } -->
   [wf] sequent { <H> >- "value"{'v3; 's3} } -->
   [main] sequent { <H> >- evalsto{eval{'e1; 's1}; eval{pair{'v1; 'v2}; 's2}} } -->
   [main] sequent { <H> >- evalsto{eval{'e2['v1; 'v2]; 's2}; eval{'v3; 's3}} } -->
   sequent { <H> >- evalsto{eval{spread{'e1; x, y. 'e2['x; 'y]}; 's1}; eval{'v3; 's3}} }

(*
 * Reference cells.
 *)
interactive pointer_value :
   sequent { <H> >- "value"{pointer{'l}; 's} }

interactive ref_eval 'v1 's2 :
   [wf] sequent { <H> >- "value"{'v1; 's2} } -->
   [main] sequent { <H> >- evalsto{eval{'e1; 's1}; eval{'v1; 's2}} } -->
   sequent { <H> >- evalsto{eval{ref{'e1}; 's1}; .Sil_state!alloc{'s2; 'v1; s3, l. eval{'l; 's3}}} }

interactive deref_eval 'v1 :
   [wf] sequent { <H> >- "value"{'v1; 's2} } -->
   [main] sequent { <H> >- evalsto{eval{'e1; 's1}; eval{'v1; 's2}} } -->
   sequent { <H> >- evalsto{eval{deref{'e1}; 's1}; eval{.Sil_state!fetch{'s2; 'v1}; 's2}} }

interactive assign_eval 's2 :
   [wf] sequent { <H> >- "value"{'v1; 's2} } -->
   [wf] sequent { <H> >- "value"{'v2; 's3} } -->
   [main] sequent { <H> >- evalsto{eval{'e1; 's1}; eval{'v1; 's2}} } -->
   [main] sequent { <H> >- evalsto{eval{'e2; 's2}; eval{'v2; 's3}} } -->
   sequent { <H> >- evalsto{eval{assign{'e1; 'e2}; 's1}; eval{.dot; .Sil_state!store{'s3; 'v1; 'v2}}} }

interactive dot_value :
   sequent { <H> >- "value"{dot; 's} }

interactive dot_eval :
   sequent { <H> >- evalsto{eval{dot; 's1}; eval{dot; 's1}} }

(*
 * Functions.
 *)
interactive lambda_value :
   sequent { <H> >- "value"{lambda{v. 'e1['v]}; 's} }

interactive lambda_eval :
   sequent { <H> >- evalsto{eval{lambda{v. 'e1['v]}; 's1}; eval{lambda{v. 'e1['v]}; 's1}} }

interactive apply_eval 'v2 's2 (lambda{v. 'e3['v]}) 's3 :
   [wf] sequent { <H> >- "value"{'v2; 's2} } -->
   [wf] sequent { <H> >- "value"{'v3; 's4} } -->
   [main] sequent { <H> >- evalsto{eval{'e2; 's1}; eval{'v2; 's2}} } -->
   [main] sequent { <H> >- evalsto{eval{'e1; 's2}; eval{lambda{v. 'e3['v]}; 's3}} } -->
   [main] sequent { <H> >- evalsto{eval{'e3['v2]; 's3}; eval{'v3; 's4}} } -->
   sequent { <H> >- evalsto{eval{apply{'e1; 'e2}; 's1}; eval{'v3; 's4}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
