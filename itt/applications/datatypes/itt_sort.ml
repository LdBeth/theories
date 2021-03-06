(*
 * Define a simple sorting algorithm.
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
 * Copyright (C) 1999-2006 MetaPRL Group, Cornell University and
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
 * Modified By: Aleksey Nogin <nogin@cs.cornell.edu>
 * Modified By: Xin Yu <xiny@cs.caltech.edu>
 *)

extends Itt_theory

open Basic_tactics

open Itt_list

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*
 * Comparisons.
 *)
define unfold_compare_lt : compare_lt{'lt; 'a; 'b} <-->
   "assert"{('lt 'a 'b)}

(*
 * Type for partial order.
 *)
define unfold_partial_order : partial_order{'A; 'lt} <-->
   ((all a: 'A. not{compare_lt{'lt; 'a; 'a}})
    & (all a: 'A. all b: 'A. all c: 'A. (compare_lt{'lt; 'a; 'b} => compare_lt{'lt; 'b; 'c} => compare_lt{'lt; 'a; 'c})))

(*
 * Definition of a sorted list.
 *)

define unfold_bounded : bounded{'u1; 'l; 'lt} <-->
   list_ind{'l; "true"; u2, v, g. "and"{"not"{compare_lt{'lt; 'u2; 'u1}}; 'g}}

define unfold_sorted : sorted{'l; 'lt} <-->
   list_ind{'l; "true"; u, v, g. "and"{bounded{'u; 'v; 'lt}; 'g}}

(*
 * Sorting algorithm.
 *)
define unfold_insert : insert{'u1; 'l; 'lt} <-->
   list_ind{'l; cons{'u1; nil}; u2, v, g.
      ifthenelse{('lt 'u1 'u2); cons{'u1; cons{'u2; 'v}}; cons{'u2; 'g}}}

define unfold_sort : sort{'l; 'lt} <-->
   list_ind{'l; nil; u, v, g. insert{'u; 'g; 'lt}}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * Folding.
 *)
let fold_compare_lt = makeFoldC << compare_lt{'lt; 'u; 'v} >> unfold_compare_lt
let fold_bounded = makeFoldC << bounded{'u; 'l; 'lt} >> unfold_bounded
let fold_sorted = makeFoldC << sorted{'l; 'lt} >> unfold_sorted
let fold_insert = makeFoldC << insert{'u; 'l; 'lt} >> unfold_insert
let fold_sort = makeFoldC << sort{'l; 'lt} >> unfold_sort

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

(*
 * Type for partial order.
 *)
dform partial_order_df : except_mode[src] :: partial_order{'A; 'lt} =
   `"PartialOrder(" slot{'lt} " " Mpsymbols!member " " slot{'A} `")"

dform compare_lt_df : except_mode[src] :: compare_lt{'lt; 'a; 'b} =
   `"(" slot{'a} " " `"<[" slot{'lt} `"] " slot{'b} `")"

(*
 * Definition of being sorted.
 *)
dform sorted_df : except_mode[src] :: sorted{'l; 'lt} =
   `"Sorted[" slot{'lt} `"](" slot{'l} `")"

dform bounded_df : except_mode[src] :: bounded{'u; 'l; 'lt} =
   `"(" slot{'u} " " Mpsymbols!le `"[" slot{'lt} `"] " slot{'l} `")"

(*
 * Sorting algorithm.
 *)
dform insert_df : except_mode[src] :: insert{'u; 'l; 'lt} =
   pushm[3] szone
   keyword["insert"] `"{" 'u `";" hspace 'l `";" hspace 'lt `"}"
   ezone popm

dform sort_df : except_mode[src] :: sort{'l; 'lt} =
   pushm[3] szone
   keyword["sort"] `"{" 'l `";" hspace 'lt `"}"
   ezone popm

dform list_ind_df : except_mode[src] :: parens :: "prec"[prec_list] :: list_ind{'l; 'base; u, v, g. 'step['g]} =
   szone pushm[0] pushm[1] `"let rec " slot{'g :> Term} `" = function" hbreak["",""]
   pushm[5] `"  " cons{'u; 'v} `" ->" hspace slot{'step[('g 'v)]} popm hspace
   pushm[5] `"| [] ->" hspace slot{'base} popm popm hspace
   pushm[3] `"in" hspace slot{'g} `" " slot{'l} popm popm ezone

(************************************************************************
 * REWRITE LEMMAS                                                       *
 ************************************************************************)

interactive_rw reduce_bounded_nil {| reduce |} : bounded{'u; nil; 'lt} <--> "true"

interactive_rw reduce_bounded_cons {| reduce |} : bounded{'u1; cons{'u2; 'v}; 'lt} <-->
   "and"{"not"{compare_lt{'lt; 'u2; 'u1}}; bounded{'u1; 'v; 'lt}}

interactive_rw reduce_sorted_nil {| reduce |} : sorted{nil; 'lt} <--> "true"

interactive_rw reduce_sorted_cons {| reduce |} : sorted{cons{'u; 'v}; 'lt} <-->
   "and"{bounded{'u; 'v; 'lt}; sorted{'v; 'lt}}

interactive_rw reduce_insert_nil {| reduce |} : insert{'u1; nil; 'lt} <--> cons{'u1; nil}

interactive_rw reduce_insert_cons {| reduce |} : insert{'u1; cons{'u2; 'v}; 'lt} <-->
   ifthenelse{('lt 'u1 'u2); cons{'u1; cons{'u2; 'v}}; cons{'u2; insert{'u1; 'v; 'lt}}}

interactive_rw reduce_sort_nil {| reduce |} : sort{nil; 'lt} <--> nil

interactive_rw reduce_sort_cons {| reduce |} : sort{cons{'u; 'v}; 'lt} <-->
   insert{'u; sort{'v; 'lt}; 'lt}

(************************************************************************
 * WELL-FORMEDNESS
 ************************************************************************)

(*
 * Well-formedness of comparisons.
 *)
interactive compare_lt_wf {| intro [intro_typeinf << 'a >>] |} 'A :
   [wf] sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   [wf] sequent { <H> >- 'a in 'A } -->
   [wf] sequent { <H> >- 'b in 'A } -->
   sequent { <H> >- "type" {compare_lt{'lt; 'a; 'b}} }

(*
 * Well-typing of partial_order predicate.
 *)
interactive partial_order_wf {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   sequent { <H> >- "type"{partial_order{'A; 'lt}} }

(*
 * Well-formedness of bounded and sorted Boolean functions.
 *)
interactive bounded_wf {| intro [intro_typeinf << 'l >>] |} list{'A} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   [wf] sequent { <H> >- 'u in 'A } -->
   [wf] sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   sequent { <H> >- "type"{bounded{'u; 'l; 'lt}} }

interactive sorted_wf {| intro [intro_typeinf << 'l >>] |} list{'A} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   [wf] sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   sequent { <H> >- "type"{sorted{'l; 'lt}} }

(*
 * Well formedness of sort and insert functions.
 *)
interactive insert_wf {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'u in 'A } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   [wf] sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   sequent { <H> >- insert{'u; 'l; 'lt} in list{'A} }

interactive sort_wf {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   [wf] sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   sequent { <H> >- sort{'l; 'lt} in list{'A} }

(*
 * Some useful ordering theorems.
 *)
interactive symetric_elim {| elim [elim_typeinf << 'a >>] |} 'H 'A :
   [wf] sequent { <H>; w: compare_lt{'lt; 'a; 'b}; <J['w]> >- 'lt in 'A -> 'A -> bool } -->
   [wf] sequent { <H>; w: compare_lt{'lt; 'a; 'b}; <J['w]> >- 'a in 'A } -->
   [wf] sequent { <H>; w: compare_lt{'lt; 'a; 'b}; <J['w]> >- 'b in 'A } -->
   [main] sequent { <H>; w: compare_lt{'lt; 'a; 'b}; <J['w]> >- partial_order{'A; 'lt} } -->
   [main] sequent { <H>; w: compare_lt{'lt; 'a; 'b}; <J['w]>; v: not{compare_lt{'lt; 'b; 'a}} >- 'C['w] } -->
   sequent { <H>; w: (compare_lt{'lt; 'a; 'b}); <J['w]> >- 'C['w] }

interactive bounded_inclusion list{'A} 'u1 :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'u in 'A } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   [wf] sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   [wf] sequent { <H> >- 'u1 in 'A } -->
   [main] sequent { <H> >- partial_order{'A; 'lt} } -->
   [main] sequent { <H> >- compare_lt{'lt; 'u; 'u1} } -->
   [main] sequent { <H> >- bounded{'u1; 'l; 'lt} } -->
   sequent { <H> >- bounded{'u; 'l; 'lt} }

let boundInclusionT = argfunT (fun t p ->
   let goal = Sequent.concl p in
   let _, l, _ =
      try three_subterms goal with
         RefineError _ ->
            raise (RefineError("boundInclusion", StringTermError("not a \"bounded\" term",goal)))
   in
   let a_type =
      match get_with_arg p with
         Some t ->
            t
       | None ->
            begin try infer_type p l with
               RefineError _ ->
                  raise (RefineError("boundInclusion", StringTermError("can not infer type",l)))
            end
   in
      bounded_inclusion a_type t)

interactive insert_inclusion 'A :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'u in 'A } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   [wf] sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   [wf] sequent { <H> >- 'u1 in 'A } -->
   [main] sequent { <H> >- partial_order{'A; 'lt} } -->
   [main] sequent { <H> >- not{compare_lt{'lt; 'u1; 'u}} } -->
   [main] sequent { <H> >- bounded{'u; 'l; 'lt} } -->
   sequent { <H> >- bounded{'u; insert{'u1; 'l; 'lt}; 'lt} }

let insertInclusionT = funT (fun p ->
   let goal = Sequent.concl p in
   let u, _, _ = three_subterms goal in
   let a_type =
      match get_with_arg p with
         Some t -> t
       | None -> infer_type p u
   in
      insert_inclusion a_type)

(*
 * Properties of insert
 *)
interactive insert_mem {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   [wf] sequent { <H> >- 'u in 'A } -->
   [wf] sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   [wf] sequent { <H> >- partial_order{'A; 'lt} } -->
   sequent { <H> >- mem{'u; insert{'u; 'l; 'lt}; 'A} }

interactive insert_subset {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'u in 'A } -->
   [wf] sequent { <H> >- 'v in list{'A} } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   [wf] sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   [wf] sequent { <H> >- partial_order{'A; 'lt} } -->
   sequent { <H> >- \subset{'v; 'l; 'A} } -->
   sequent { <H> >- \subset{'v; insert{'u; 'l; 'lt}; 'A} }

interactive subset_insert_cons {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'u in 'A } -->
   [wf] sequent { <H> >- 'v in list{'A} } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   [wf] sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   [wf] sequent { <H> >- partial_order{'A; 'lt} } -->
   sequent { <H> >- \subset{'v; 'l; 'A} } -->
   sequent { <H> >- \subset{insert{'u; 'v; 'lt}; cons{'u; 'l}; 'A} }

(*
 * Verifications of the functions.
 *)
interactive insert_thm {| intro [intro_typeinf << 'l >>] |} list{'A} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   [wf] sequent { <H> >- 'u in 'A } -->
   [wf] sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   [wf] sequent { <H> >- partial_order{'A; 'lt} } -->
   [main] sequent { <H> >- sorted{'l; 'lt} } -->
   sequent { <H> >- sorted{insert{'u; 'l; 'lt}; 'lt} }

interactive sorted_thm {| intro [intro_typeinf << 'l >>] |} list{'A} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   [wf] sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   [wf] sequent { <H> >- partial_order{'A; 'lt} } -->
   sequent { <H> >- sorted{sort{'l; 'lt}; 'lt} }

interactive sort_sameset {| intro [intro_typeinf << 'l >>] |} list{'A} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   [wf] sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   [wf] sequent { <H> >- partial_order{'A; 'lt} } -->
   sequent { <H> >- sameset{sort{'l; 'lt}; 'l; 'A} }

(*
 * This rule can be used to demonstrate the extractor.
 *)
interactive smallest_element :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- 'l in list{'A} } -->
   sequent { <H> >- 'lt in 'A -> 'A -> bool } -->
   sequent { <H> >- not{"assert"{is_nil{'l}}}} -->
   sequent { <H> >- partial_order{'A; 'lt} } -->
   sequent { <H> >- exst a : 'A. (mem{'a; 'l; 'A} and bounded{'a; 'l; 'lt}) }

(*
 * -*-
 * LOCAL Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
