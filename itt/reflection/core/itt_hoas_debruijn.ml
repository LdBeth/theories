doc <:doc<
   @module[Itt_hoas_debruijn]
   The @tt[Itt_hoas_debruijn] module defines a mapping from de Bruijn-like
   representation of syntax into the HOAS.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2005, MetaPRL Group

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

   Author: Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
>>

doc <:doc< @parents >>
extends Itt_hoas_base
extends Itt_hoas_vector
extends Itt_nat
extends Itt_list2
extends Itt_image2

doc docoff

open Basic_tactics
open Itt_dfun
open Itt_sqsimple
open Itt_hoas_vector

(*
 * Options.
 *)
let resource private select +=
   [denormalize_term, OptionAllow]

doc <:doc<
   @terms
   @modsubsection{A de Bruijn-like representation of syntax}
   Our de Bruijn-like representation of (bound) terms consists of two operators. <<var{'left; 'right}>>
   represents a variable bterm, whose ``left index'' is <<'left>> and whose ``right index'' is <<'right>>.
   Namely, it represent the term
   <<bind{x_1.math_ldots bind{x_left.bind{y.bind{z_1.math_ldots bind{z_right. 'v} math_ldots}}} math_ldots}>>.

   The <<mk_bterm{'n; 'op; 'btl}>> represents the compound term of depth $n$. In other words,
   <<mk_bterm{'n; 'op; (bind{'n; v.'bt_1['v]} :: math_ldots :: bind{'n; v.'bt_k['v]}::nil)}>> is
   <<bind{'n; v. mk_term{'op; ('bt_1['v] :: math_ldots :: 'bt_k['v]::nil)}}>>.
>>
define unfold_var:
   var{'left; 'right} <--> bind{'left; bind{v. bind{'right; 'v}}}

define opaque unfold_mk_bterm:
   mk_bterm{'n; 'op; 'btl}
   <-->
   ind{'n;
      lambda{btl. mk_term{'op; 'btl }};
      "_", r. lambda{btl. bind{v. 'r subst_list{'btl; 'v}}}}
   'btl

doc <:doc<
   @modsubsection{Basic operations on syntax}
   <<bdepth{'bt}>> is the ``binding depth'' (i.e. the number of outer bindings) of a bterm <<'bt>>.

   <<left{'v}>> and <<right{'v}>> provide a way of computing the $l$ and $r$ indices of a variable <<var{'l; 'r}>>.

   <<get_op{'bt; 'op}>> returns the <<'bt>>'s operator, if <<'bt>> is a @tt[mk_bterm] and returns
   <<'op>> if <<'bt>> is a variable.

   <<subterms{'bt}>> computes the subterms of the bterm <<'bt>>.
>>

define opaque unfold_bdepth:
   bdepth{'bt} <--> fix{f.lambda{bt. weak_dest_terms{'bt; 1 +@ 'f subst{'bt; mk_term{it; nil}}; y. 0}}} 'bt

define opaque unfold_left:
   left{'bt} <-->
   fix{f.lambda{bt. lambda{l. weak_dest_bterm{'bt; 'f subst{'bt; mk_term{'l; nil}} ('l +@ 1); op, "_". 'op}}}} 'bt 0

define opaque unfold_right:
   right{'bt} <--> bdepth{'bt} -@ left{'bt} -@ 1

define opaque unfold_get_op:
   get_op{'bt; 'op} <--> fix{f.lambda{bt. weak_dest_bterm{'bt;  'f subst{'bt; mk_term{'op; nil}}; op, "_". 'op}}} 'bt

declare not_found

define iform unfold_get_op1:
   get_op{'bt} <--> get_op{'bt; not_found}

(*private*) define unfold_num_subterms:
   num_subterms{'bt}
   <-->
   fix{f. lambda{bt. weak_dest_bterm{'bt;  'f subst{'bt; mk_term{it; nil}}; "_", btl.  length{'btl}}}} 'bt

(*private*) define unfold_nth_subterm:
   nth_subterm{'bt; 'n}
   <-->
   fix{f. lambda{bt. weak_dest_bterm{'bt; bind{v. 'f subst{'bt; 'v}}; "_", btl. nth{'btl; 'n}}}} 'bt

define opaque unfold_subterms:
   subterms{'bt} <--> list_of_fun{n.nth_subterm{'bt; 'n}; num_subterms{'bt}}

doc <:doc< @rewrites >>

(*
 * The following 3 rules are "denormalization" rules,
 * which causes trouble for the term normalizer.  For the moment,
 * do not add them to the reduce resource.
 *)
interactive_rw reduce_mk_bterm_base {| reduce ~labels:denormalize_labels |} :
   mk_bterm{0; 'op; 'btl} <--> mk_term{'op; 'btl }

interactive_rw reduce_mk_bterm_step {| reduce ~labels:denormalize_labels |} :
   'n in nat -->
   mk_bterm{'n +@ 1; 'op; 'btl} <--> bind{v. mk_bterm{'n; 'op; subst_list{'btl; 'v}}}

interactive_rw reduce_mk_bterm_empty {| reduce ~labels:denormalize_labels |} :
   'n in nat -->
   mk_bterm{'n; 'op; nil} <--> bind{'n; mk_term{'op; nil}}

interactive_rw fold_mk_term :
   mk_term{'op; 'subterms}
   <-->
   mk_bterm{0; 'op; 'subterms}

interactive_rw reduce_bdepth_mk_term {| reduce |}:
   bdepth{mk_term{'op; 'btl}} <--> 0

interactive_rw reduce_bdepth_mk_terms {| reduce |}:
   bdepth{mk_terms{'e}} <--> 0

interactive_rw reduce_bdepth_bind {| reduce |} :
   bdepth{bind{v.'t['v]}} <--> 1 +@ bdepth{'t[mk_term{it; nil}]}

interactive_rw reduce_bdepth_var {| reduce |} :
   'l in nat -->
   'r in nat -->
   bdepth{var{'l; 'r}} <--> 'l +@ 'r +@ 1

interactive_rw reduce_bdepth_mk_bterm {| reduce |} :
   'n in nat -->
   bdepth{mk_bterm{'n; 'op; 'btl}} <--> 'n

interactive_rw reduce_getop_var {| reduce |} :
   'l in nat -->
   'r in nat -->
   get_op{var{'l; 'r}; 'op} <--> 'op

interactive_rw reduce_getop_mkbterm {| reduce |} :
   'n in nat -->
   get_op{mk_bterm{'n; 'op; 'btl}; 'op'} <--> 'op

interactive_rw num_subterms_id {| reduce |} :
   'btl in list -->
   'n in nat -->
   num_subterms{mk_bterm{'n; 'op; 'btl}} <--> length{'btl}

interactive_rw nth_subterm_id {| reduce |} :
   'n in nat -->
   'm in nat -->
   'k in nat -->
   'k < 'm -->
   nth_subterm{mk_bterm{'n; 'op; list_of_fun{x.'f['x]; 'm}}; 'k} <--> bind{'n; v. substl{'f['k]; 'v}}

interactive_rw subterms_id {| reduce |} :
   'btl in list -->
   'n in nat -->
   subterms{mk_bterm{'n; 'op; 'btl}} <--> map{bt. bind{'n; v. substl{'bt; 'v}}; 'btl}

interactive_rw left_id {| reduce |} :
   'l in nat -->
   'r in nat -->
   left{var{'l; 'r}} <--> 'l

interactive_rw right_id {| reduce |} :
   'l in nat -->
   'r in nat -->
   right{var{'l; 'r}} <--> 'r

interactive_rw subst_var0 {| reduce |} :
   'r in nat -->
   subst{var{0; 'r};'t} <--> bind{'r;'t}

interactive_rw subst_var {| reduce |} :
   'l in nat -->
   'r in nat -->
   subst{var{'l+@1; 'r};'t} <--> var{'l;'r}

interactive_rw subst_mkbterm {| reduce |} :
   'bdepth in nat -->
   subst{mk_bterm{'bdepth+@1;'op;'btl};'t} <-->  mk_bterm{'bdepth; 'op; subst_list{'btl; 't}}

interactive_rw bind_var {| reduce |} :
   'l in nat -->
   'r in nat -->
   bind{x.var{'l; 'r}} <--> var{'l+@1;'r}

interactive_rw lemma {| reduce |} :
   'btl in list -->
   subst_list{bind_list{'btl}; 'v} <--> 'btl

interactive_rw bind_mkbterm  {| reduce |} :
   'bdepth in nat -->
   'btl in list -->
   bind{x.mk_bterm{'bdepth;'op;'btl}} <-->  mk_bterm{'bdepth+@1; 'op; bind_list{'btl}}

interactive_rw lemma1 {| reduce |} :
   'r in nat -->
   'n in nat -->
   'r >= 'n  -->
   bind{'n; gamma. substl{bind{'r; 't}; 'gamma}} <--> bind{'r; 't}

interactive_rw lemma2 {| reduce |} :
   'l in nat -->
   'r in nat -->
   'n in nat -->
   'l+@'r+@1 >= 'n  -->
   bind{'n; gamma. substl{var{'l;'r}; 'gamma}} <--> var{'l;'r}

interactive_rw lemma3 {| reduce |} :
   'm in nat -->
   'n in nat -->
   'm >= 'n  -->
   bind{'n; gamma. substl{mk_bterm{'m;'op;'btl}; 'gamma}} <--> mk_bterm{'m;'op;'btl}
doc docoff

dform var_df : var{'l; 'r} =
   pushm[3] tt["var"] `"(" slot{'l} `"," slot{'r} `")" popm

dform mk_bterm_df : mk_bterm{'n; 'op; 'btl} =
   szone pushm[3] tt["mk_bterm"] `"(" slot{'n} `";" hspace slot{'op} `";" hspace slot{'btl} `")" popm ezone

dform bdepth_df: parens :: "prec"[prec_apply] :: bdepth{'bt} =
   tt["D"] space slot["le"]{'bt}

dform left_df: parens :: "prec"[prec_apply] :: left{'bt} =
   tt["l"] space slot["le"]{'bt}

dform right_df: parens :: "prec"[prec_apply] :: right{'bt} =
   tt["r"] space slot["le"]{'bt}

dform get_op_df: get_op{'bt; 'op} =
   pushm[0] szone pushm[3] keyword["try"] hspace tt["get_op"] space slot{'bt}
   popm hspace pushm[3] keyword["with"] tt[" Not_found ->"] hspace slot{'op} popm ezone popm

dform subterms_df: "prec"[prec_apply] :: parens :: subterms{'bt} =
   tt["subterms"] space slot["le"]{'bt}

doc <:doc<
   Define a type of variables << Var >> that is more abstract than the
   raw de Bruijn representation.
>>
define unfold_Var : Var <--> Img{nat * nat; v. spread{'v; i, j. var{'i; 'j}}}

let fold_Var = makeFoldC << Var >> unfold_Var

interactive var_type_univ {| intro [] |} :
   sequent { <H> >- Var in univ[i:l] }

interactive var_type_wf {| intro [] |} :
   sequent { <H> >- Var Type }

interactive var_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l in nat } -->
   [wf] sequent { <H> >- 'r in nat } -->
   sequent { <H> >- var{'l; 'r} in Var }

interactive var_elim {| elim [] |} 'H :
   sequent { <H>; i: nat; j: nat; <J[var{'i; 'j}]> >- 'C[var{'i; 'j}] } -->
   sequent { <H>; x: Var; <J['x]> >- 'C['x] }

interactive var_sqsimple {| intro []; sqsimple |} :
   sequent { <H> >- sqsimple{Var} }

doc <:doc<
   Boolean operations on variables.
>>
define unfold_beq_var : beq_var{'x; 'y} <-->
   band{beq_int{left{'x}; left{'y}}; beq_int{right{'x}; right{'y}}}

interactive_rw reduce_beq_var :
   'l1 in nat -->
   'r1 in nat -->
   'l2 in nat -->
   'r2 in nat -->
   beq_var{var{'l1; 'r1}; var{'l2; 'r2}}
   <-->
   band{beq_int{'l1; 'l2}; beq_int{'r1; 'r2}}

interactive beq_var_wf {| intro [] |} :
   [wf] sequent { <H> >- 'x in Var } -->
   [wf] sequent { <H> >- 'y in Var } -->
   sequent { <H> >- beq_var{'x; 'y} in bool }

interactive beq_var_assert_intro {| intro [] |} :
   sequent { <H> >- 'x = 'y in Var } -->
   sequent { <H> >- "assert"{beq_var{'x; 'y}} }

interactive beq_var_assert_elim {| elim [] |} 'H :
   [wf] sequent { <H>; u: "assert"{beq_var{'x; 'y}}; <J['u]> >- 'x in Var } -->
   [wf] sequent { <H>; u: "assert"{beq_var{'x; 'y}}; <J['u]> >- 'y in Var } -->
   sequent { <H>; u: 'x = 'y in Var; <J['u]> >- 'C['u] } -->
   sequent { <H>; u: "assert"{beq_var{'x; 'y}}; <J['u]> >- 'C['u] }

doc <:doc<
   This is the main theorem that shows that << bind{x. 'e['x]} >> commutes with
   << mk_bterm{'n; 'op; 'subterms} >>.
>>
interactive_rw reduce_bind_of_mk_bterm_of_list_of_fun :
   'n in nat -->
   'm in nat -->
   bind{x. mk_bterm{'n; 'op; list_of_fun{y. 'f['x; 'y]; 'm}}}
   <-->
   mk_bterm{'n +@ 1; 'op; list_of_fun{y. bind{x. 'f['x; 'y]}; 'm}}

interactive_rw reduce_vec_bind_of_mk_bterm_of_list_of_fun :
   'i in nat -->
   'n in nat -->
   'm in nat -->
   bind{'i; x. mk_bterm{'n; 'op; list_of_fun{y. 'f['x; 'y]; 'm}}}
   <-->
   mk_bterm{'n +@ 'i; 'op; list_of_fun{y. bind{'i; x. 'f['x; 'y]}; 'm}}

doc <:doc<
   Some equivalences on binds.
>>
interactive_rw reduce_bindn_nth {| reduce |} : <:xrewrite<
   'n in nat -->
   'm in nat -->
   'm < 'n -->
   bind{'n; x. nth{'x; 'm}}
   <-->
   var{'m; 'n -@ 'm -@ 1}
>>

interactive_rw reduce_bindn_nth2 {| reduce |} : <:xrewrite<
   'n1 in nat -->
   'n2 in nat -->
   'm in nat -->
   'm < 'n1 -->
   bind{'n1; x1. bind{'n2; x2. nth{'x1; 'm}}}
   <-->
   var{'m; 'n1 +@ 'n2 -@ 'm -@ 1}
>>

interactive_rw reduce_bind_var {| reduce |} : <:xrewrite<
   'n in nat -->
   'l in nat -->
   bind{'n; var{'l; 'r}}
   <-->
   var{'n +@ 'l; 'r}
>>

doc docoff

(************************************************************************
 * Tactics and terms.
 *)
let mk_bterm_term = << mk_bterm{'n; 'op; 'subterms} >>
let mk_bterm_opname = opname_of_term mk_bterm_term
let is_mk_bterm_term = is_dep0_dep0_dep0_term mk_bterm_opname
let dest_mk_bterm_term = dest_dep0_dep0_dep0_term mk_bterm_opname
let mk_mk_bterm_term = mk_dep0_dep0_dep0_term mk_bterm_opname

let bdepth_term = << bdepth{'e} >>
let bdepth_opname = opname_of_term bdepth_term
let is_bdepth_term = is_dep0_term bdepth_opname
let dest_bdepth_term = dest_dep0_term bdepth_opname
let mk_bdepth_term = mk_dep0_term bdepth_opname

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
