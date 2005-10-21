doc <:doc<
   @spelling{th}
   @module[Itt_list2]

   The @tt{Itt_list2} module defines a ``library'' of
   additional operations on the lists defined in
   the @hrefmodule[Itt_list] module.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998-2005 MetaPRL Group

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
   Modified By: Aleksey Nogin @email{nogin@cs.cornell.edu}
   Modified By: Alexei Kopylov @email{kopylov@cs.cornell.edu}
   Modified By: Xin Yu @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @parents >>
extends Itt_dfun
extends Itt_list
extends Itt_logic
extends Itt_bool
extends Itt_nat
extends Itt_isect
extends Itt_struct2
extends Itt_nequal
extends Itt_int_base
extends Itt_int_ext
extends Itt_int_arith
extends Itt_omega
extends Itt_tunion
extends Itt_ext_equal
extends Itt_sqsimple
extends Itt_esquash
doc docoff

open Basic_tactics

open Itt_equal
open Itt_rfun
open Itt_logic
open Itt_squash
open Itt_list
open Itt_struct

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

doc <:doc<
   @terms

   The @tt[all_list] and @tt[exists_list] term define quantifiers for lists.
>>
define unfold_all_list : all_list{'l; x. 'P['x]} <-->
   list_ind{'l; "true"; x, t, g. 'P['x] and 'g}

define unfold_all_list_witness : all_list_witness{'l; x. 'f['x]} <-->
   list_ind{'l; it; x, t, g. ('f['x],'g)}

define unfold_exists_list : exists_list{'l; x. 'P['x]} <-->
   list_ind{'l; "false"; x, t, g. 'P['x] or 'g}

doc <:doc<
     The @em[head] of the list is the first element of a list, and the @em[tail] is the rest.
     Both these operations undefined when list is empty.
>>
declare undefined

define unfold_hd :
   hd{'l} <--> list_ind{'l; undefined; h, t, g. 'h}

define unfold_tl :
   tl{'l} <--> list_ind{'l; undefined; h, t, g. 't}

doc <:doc<
   @noindent

   The @tt{is_nil} term defines a Boolean value that is true
   @emph{iff} the argument list $l$ is empty.
>>
define unfold_is_nil :
   is_nil{'l} <--> list_ind{'l; btrue; h, t, g. bfalse}

doc <:doc<
   @noindent

   The @tt[mem] term defines list membership.
>>
define unfold_mem :
   mem{'x; 'l; 'T} <-->
      list_ind{'l; "false"; h, t, g. "or"{('x = 'h in 'T); 'g}}

doc <:doc<
   @noindent

   The @tt{subset} term determines whether the elements in $<<'l_1>>$ are also
   in $<<'l_2>>$.
>>
define unfold_subset :
   \subset{'l1; 'l2; 'T} <-->
      list_ind{'l1; "true"; h, t, g. "and"{mem{'h; 'l2; 'T}; 'g}}

doc <:doc<
   @noindent

   The @tt[sameset] term determines whether the two lists contain the same
   set of elements.
>>
define unfold_sameset :
   sameset{'l1; 'l2; 'T} <-->
      "and"{\subset{'l1; 'l2; 'T}; \subset{'l2; 'l1; 'T}}

doc <:doc<
   @noindent
   The @tt{append} term takes two lists and concatenates them.
>>
define unfold_append :
   append{'l1; 'l2} <-->
      list_ind{'l1; 'l2; h, t, g. 'h :: 'g}

doc <:doc<
   @noindent
   The @tt{ball2} term defines a Boolean universal quantification
   over two lists.  The test $b[x, y]$ must compute a Boolean value
   given elements of the two lists, and the test is $@bfalse$ if
   the lists have different lengths.
>>
define unfold_ball2 :
   ball2{'l1; 'l2; x, y. 'b['x; 'y]} <-->
      (list_ind{'l1; lambda{z. list_ind{'z; btrue; h, t, g. bfalse}};
                     h1, t1, g1. lambda{z. list_ind{'z; bfalse;
                     h2, t2, g2. band{'b['h1; 'h2]; .'g1 't2}}}} 'l2)

doc <:doc<
   @noindent
   The @tt[assoc] term defines an associative lookup on
   the list $l$.  The list $l$ should be a list of pairs.
   The @tt[assoc] term searches for the element $x$ as
   the first element of one of the pairs.  On the first
   occurrence of a pair $(x, y)$, the value $b[y]$ is returned.
   The $z$ term is returned if a pair is not found.
>>
define unfold_assoc :
   assoc{'eq; 'x; 'l; y. 'b['y]; 'z} <-->
      list_ind{'l; 'z; h, t, g.
         spread{'h; u, v.
            ifthenelse{'eq 'u 'x; 'b['v]; 'g}}}

doc <:doc<
   @noindent
   The @tt[rev_assoc] term also performs an associative search,
   but it keys on the second element of each pair.
>>
define unfold_rev_assoc :
   rev_assoc{'eq; 'x; 'l; y. 'b['y]; 'z} <-->
      list_ind{'l; 'z; h, t, g.
         spread{'h; u, v.
            ifthenelse{'eq 'v 'x; 'b['u]; 'g}}}

doc <:doc<
   @noindent
   The @tt{map} term applies the function $f$ to each element
   of the list $l$, and returns the list of the results (in
   the same order).
>>
define unfold_map : map{'f; 'l} <-->
   list_ind{'l; nil; h, t, g. cons{'f 'h; 'g}}

define unfold_map2 : map{x.'f['x]; 'l} <--> map{lambda{x.'f['x]};'l}


doc <:doc<
   @noindent
   The @tt{fold_left} term applies the function $f$ to each element
   of the list $l$, together with an extra argument $v$.  The result
   of each computation is passed as the argument $v$ to the
   next stage of the computation.
>>
define unfold_fold_left :
   fold_left{'f; 'v; 'l} <-->
      (list_ind{'l; lambda{x. 'x}; h, t, g. lambda{x. 'g ('f 'h 'x)}} 'v)

doc <:doc<
   @noindent
   The @tt[nth] term returns the $i$-th element of list $l$.
   The argument $i$ must be within the bounds of the list.
>>
define unfold_nth :
   nth{'l; 'i} <-->
      (list_ind{'l; undefined; u, v, g. lambda{j. if 'j =@  0 then  'u else ('g ('j -@ 1))}} 'i)

doc <:doc<
   @noindent
   The @tt[replace_nth] term replaces the $i$-th element of list $l$
   with the term $v$.
>>
define unfold_replace_nth :
   replace_nth{'l; 'i; 't} <-->
      (list_ind{'l; nil; u, v, g. lambda{j. if 'j =@ 0 then  cons{'t; 'v} else cons{'u; .'g ('j -@ 1)}}} 'i)

doc <:doc<
   @noindent
   The @tt[insert_at] term inserts a new element into the $i$-th position of list $l$
   with the term $v$.
>>
define unfold_insert_at :
   insert_at{'l; 'i; 't} <-->
      ind{'i; lambda{l.cons{'t; 'l}}; "_",r. lambda{l. hd{'l} :: ('r tl{'l})}} 'l

doc <:doc<
   @noindent
   The @tt{length} term returns the total number of elements in
   the list $l$.
>>
define unfold_length :
   length{'l} <--> list_ind{'l; 0; u, v, g. 'g +@ 1}


doc <:doc<
      <<Index{'l}>> of the list is a set of indexes of the list $l$, that is
>>

define unfold_index :
   Index{'l} <--> nat{length{'l}}

doc <:doc<
   @noindent
   The @tt[rev] function returns a list with the same elements as
   list $l$, but in reverse order.
>>
define unfold_rev : rev{'l} <-->
   list_ind{'l; nil; u, v, g. append{'g; cons{'u; nil} }}

doc <:doc<
   @noindent
   If $f$ is a function then  $<<mklist{'n;'f}>>$ is the list $<<'f(0) :: 'f(1) :: math_ldots :: 'f('n):: nil>>$.
>>

define unfold_mklist: mklist{'n;'f} <-->
   ind{'n; nil; x,l.('f ('n-@ 'x)) :: 'l}

doc <:doc<
   @noindent
   The type <<list>> contains all lists. It is defined as <<top>> <<list>>.
   Note that all lists of the same length are equal in the <<list>> type.
>>

define iform unfold_list: list <--> list{top}

doc <:doc< Maximal element of a list >>

define unfold_list_max: list_max{'l} <-->
   list_ind{'l; 0; h, t, g. max{'h; 'g}}

doc docoff

let length_term = << length{'l} >>
let length_opname = opname_of_term length_term
let is_length_term = is_dep0_term length_opname
let mk_length_term = mk_dep0_term length_opname
let dest_length = dest_dep0_term length_opname

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_append
prec prec_ball
prec prec_assoc

dform list_df : list = `"List"

dform all_df : except_mode[src] :: parens :: "prec"[prec_quant] :: "all_list"{'A; x. 'B} =
   szone pushm[3] Mpsymbols!forall slot{'x} Mpsymbols!member slot{'A} sbreak["",". "] slot{'B} popm ezone

dform exists_df : except_mode[src] :: parens :: "prec"[prec_quant] :: "exists_list"{'A; x. 'B} =
   szone pushm[3] Mpsymbols!"exists" slot{'x} Mpsymbols!member slot{'A} sbreak["",". "] slot{'B} popm ezone

dform is_nil_df : except_mode[src] :: parens :: "prec"[prec_equal] :: is_nil{'l} =
   slot{'l} `" =" subb `" []"

dform mem_df : except_mode[src] :: mem{'x; 'l; 'T} =
   `"(" slot{'x} " " Mpsymbols!member `" " slot{'l} `" in " slot{list{'T}} `")"

dform index_df : except_mode[src] :: Index{'l} =
   `"Index(" slot{'l} `")"

dform subset_df : except_mode[src] :: \subset{'l1; 'l2; 'T} =
   `"(" slot{'l1} " " Mpsymbols!subseteq `"[" slot{'T} `"] " slot{'l2} `")"

dform sameset_df : except_mode[src] :: sameset{'l1; 'l2; 'T} =
   pushm[3] szone
   keyword["sameset"] `"{" 'l1 `";" hspace 'l2 `";" hspace 'T `"}"
   ezone popm

dform append_df : except_mode[src] :: parens :: "prec"[prec_append] :: append{'l1; 'l2} =
   slot["le"]{'l1} `" @" space slot{'l2}

dform ball2_df : except_mode[src] :: parens :: "prec"[prec_ball] :: ball2{'l1; 'l2; x, y. 'b} =
   pushm[3] Mpsymbols!forall subb slot{'x} `", " slot{'y} space
      Mpsymbols!member space slot{'l1} `", " slot{'l2} sbreak["",". "]
      slot{'b} popm

dform assoc_df : except_mode[src] :: parens :: "prec"[prec_assoc] :: assoc{'eq; 'x; 'l; v. 'b; 'z} =
   szone pushm[0] pushm[3]
   keyword["try"] hspace szone
      pushm[3]
      keyword["let "] slot{'v} keyword[" ="] hspace tt["assoc "] slot{'x} space Mpsymbols!member slot{'eq} space slot{'l} popm hspace
      pushm[3] keyword["in"] hspace
      slot{'b} popm ezone popm hspace
   pushm[3] keyword["with "] tt[ "Not_found ->"] hspace
   slot{'z} popm popm ezone

dform rev_assoc_df : except_mode[src] :: parens :: "prec"[prec_assoc] :: rev_assoc{'eq; 'x; 'l; v. 'b; 'z} =
   szone pushm[0] pushm[3]
   keyword["try"] hspace
      pushm[3]
      keyword["let "] slot{'v} keyword[" ="] hspace tt["rev_assoc "] slot{'x} space Mpsymbols!member slot{'eq} space slot{'l} popm hspace
      pushm[3] keyword["in"] hspace
      slot{'b} popm popm hspace
   pushm[3] keyword["with "] tt["Not_found ->"] hspace
   slot{'z} popm popm ezone

dform map_df : except_mode[src] :: parens :: "prec"[prec_apply] :: map{'f; 'l} =
   `"map" space slot{'f} space slot{'l}

dform map_df : except_mode[src] :: parens :: "prec"[prec_apply] :: map{x.'f; 'l} =
   `"map("slot{'x} `"." slot{'f} `";" slot{'l} `")"

dform fold_left_df : except_mode[src] :: fold_left{'f; 'v; 'l} =
   `"fold_left(" slot{'f} `", " slot{'v} `", " slot{'l} `")"

dform length_df : except_mode[src] :: length{'l} =
   `"|" slot{'l} `"|"

dform nth_df : except_mode[src] :: nth{'l; 'i} =
    slot{'l} sub{slot{'i}}

dform replace_nth_df : except_mode[src] :: replace_nth{'l; 'i; 'v} =
   szone tt["replace_nth"] `"(" pushm[0] slot{'l} `"," hspace slot{'i} `"," hspace slot{'v} `")" popm ezone

dform insert_at_df : except_mode[src] :: insert_at{'l; 'i; 'v} =
   szone tt["insert_at"] `"(" pushm[0] slot{'l} `"," hspace slot{'i} `"," hspace slot{'v} `")" popm ezone

dform rev_df : except_mode[src] :: rev{'l} =
   tt["rev"] `"(" slot{'l} `")"

dform list_max_df : list_max{'l} =
   pushm[0] szone pushm[3] tt["max"] Mpsymbols!subl `"(" slot{'l} popm `")" ezone popm

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

interactive_rw reduce_hd {| reduce |} : hd{cons{'h; 't}} <--> 'h

interactive_rw reduce_tl {| reduce |} : tl{cons{'h; 't}} <--> 't

doc <:doc<
   The @hrefterm[all_list] term performs induction over the list.
>>

interactive_rw reduce_all_list_nil {| reduce |} : all_list{nil; x. 'P['x]} <--> "true"

interactive_rw reduce_all_list_cons {| reduce |} :
   all_list{cons{'u; 'v}; x. 'P['x]} <--> 'P['u] and all_list{'v; x.'P['x]}
doc docoff

interactive_rw reduce_all_list_witness_nil {| reduce |} : all_list_witness{nil; x. 'P['x]} <--> it

interactive_rw reduce_all_list_witness_cons {| reduce |} :
   all_list_witness{cons{'u; 'v}; x. 'P['x]} <--> ('P['u], all_list_witness{'v; x.'P['x]})


doc <:doc<
   @rewrites

   The @hrefterm[is_nil] term is defined with the
   @hrefterm[list_ind] term, with a base case $@btrue$,
   and step case $@bfalse$.
>>
interactive_rw reduce_is_nil_nil {| reduce |} : is_nil{nil} <--> btrue

interactive_rw reduce_is_nil_cons {| reduce |} : is_nil{cons{'h; 't}} <--> bfalse
doc docoff

let fold_is_nil = makeFoldC << is_nil{'l} >> unfold_is_nil

doc <:doc<
   The @hrefterm[mem] term performs induction over the list.
>>

interactive_rw reduce_mem_nil {| reduce |} : mem{'x; nil; 'T} <--> "false"

interactive_rw reduce_mem_cons {| reduce |} :
   mem{'x; cons{'u; 'v}; 'T} <--> "or"{('x = 'u in 'T); mem{'x; 'v; 'T}}
doc docoff

let fold_mem = makeFoldC << mem{'x; 'l; 'T} >> unfold_mem

doc <:doc<
   The @hrefterm[subset] term performs induction over the first list.
>>
interactive_rw reduce_subset_nil {| reduce |} : \subset{nil; 'l; 'T} <--> "true"

interactive_rw reduce_subset_cons {| reduce |} :
   \subset{cons{'u; 'v}; 'l; 'T} <--> "and"{mem{'u; 'l; 'T}; \subset{'v; 'l; 'T}}

doc docoff

let fold_subset = makeFoldC << \subset{'l1; 'l2; 'T} >> unfold_subset

let fold_sameset = makeFoldC << sameset{'l1; 'l2; 'T} >> unfold_sameset

doc <:doc<
   The @hrefterm[append] term performs induction over the
   first list.
>>
interactive_rw reduce_append_nil {| reduce |} : append{nil; 'l2} <--> 'l2

interactive_rw reduce_append_cons {| reduce |} :
   append{cons{'x; 'l1}; 'l2} <--> cons{'x; append{'l1; 'l2}}

interactive_rw append_nil 'A :
   ('l in list{'A}) -->
   append{'l;nil} <--> 'l

interactive_rw append_assoc 'A:
   ('l1 in list{'A}) -->
   append{append{'l1;'l2};'l3} <-->
   append{'l1;append{'l2;'l3}}

doc docoff

let fold_append = makeFoldC << append{'l1; 'l2} >> unfold_append

doc <:doc<
   The @hrefterm[ball2] term performs simultaneous induction
   over both lists, comparing the elements of the lists with
   the comparison $b[x, y]$.
>>
interactive_rw reduce_ball2_nil_nil {| reduce |} :
   ball2{nil; nil; x, y. 'b['x; 'y]} <--> btrue

interactive_rw reduce_ball2_nil_cons {| reduce |} :
   ball2{nil; cons{'h; 't}; x, y.'b['x; 'y]} <--> bfalse

interactive_rw reduce_ball2_cons_nil {| reduce |} :
   ball2{cons{'h; 't}; nil; x, y. 'b['x; 'y]} <--> bfalse

interactive_rw reduce_ball2_cons_cons {| reduce |} :
   ball2{cons{'h1; 't1}; cons{'h2; 't2}; x, y. 'b['x; 'y]} <-->
      band{'b['h1; 'h2]; ball2{'t1; 't2; x, y. 'b['x; 'y]}}

doc docoff

let fold_ball2 = makeFoldC << ball2{'l1; 'l2; x, y. 'b['x; 'y]} >> unfold_ball2

doc <:doc<
   The @hrefterm[assoc] term performs induction over the list,
   splitting each pair and comparing it with the key.
>>
interactive_rw reduce_assoc_nil {| reduce |} :
   assoc{'eq; 'x; nil; y. 'b['y]; 'z} <--> 'z

interactive_rw reduce_assoc_cons {| reduce |} :
   assoc{'eq; 'x; cons{pair{'u; 'v}; 'l}; y. 'b['y]; 'z} <-->
      ifthenelse{'eq 'u 'x; 'b['v]; assoc{'eq; 'x; 'l; y. 'b['y]; 'z}}

doc docoff

let fold_assoc = makeFoldC << assoc{'eq; 'x; 'l; v. 'b['v]; 'z} >> unfold_assoc

doc <:doc<
   The @hrefterm[rev_assoc] term also performs induction over the list,
   but it keys on the second element of each pair.
>>
interactive_rw reduce_rev_assoc_nil {| reduce |} :
   rev_assoc{'eq; 'x; nil; y. 'b['y]; 'z} <--> 'z

interactive_rw reduce_rev_assoc_cons {| reduce |} :
   rev_assoc{'eq; 'x; cons{pair{'u; 'v}; 'l}; y. 'b['y]; 'z} <-->
      ifthenelse{'eq 'v 'x; 'b['u]; rev_assoc{'eq; 'x; 'l; y. 'b['y]; 'z}}

doc docoff

let fold_rev_assoc = makeFoldC << rev_assoc{'eq; 'x; 'l; v. 'b['v]; 'z} >> unfold_rev_assoc

doc <:doc<
   The @hrefterm[fold_left] term performs induction over the
   list argument, applying the function to the head element
   and the argument computed by the previous stage of the computation.
>>
interactive_rw reduce_fold_left_nil {| reduce |} :
   fold_left{'f; 'v; nil} <--> 'v

interactive_rw reduce_fold_left_cons {| reduce |} :
   fold_left{'f; 'v; cons{'h; 't}} <-->
   fold_left{'f; .'f 'h 'v; 't}

doc docoff

let fold_fold_left = makeFoldC << fold_left{'f; 'v; 'l} >> unfold_fold_left

doc <:doc<
   The @hrefterm[length] function counts the total number of elements in the
   list.
>>
interactive_rw reduce_length_nil {| reduce |} : length{nil} <--> 0

interactive_rw reduce_length_cons {| reduce |} : length{cons{'u; 'v}} <--> (length{'v} +@ 1)

doc docoff

let fold_length = makeFoldC << length{'l} >> unfold_length

doc <:doc<
   The @hrefterm[nth] term performs induction over the
   list, comparing the index to 0 at each step and returning the head element
   if it reaches 0.  The $@it$ term is returned if the index never reaches 0.
>>
interactive_rw reduce_nth_cons {| reduce |} :
   nth{cons{'u; 'v}; 'i} <--> ifthenelse{beq_int{'i; 0}; 'u; nth{'v; .'i -@ 1}}

doc docoff

let fold_nth = makeFoldC << nth{'l; 'i} >> unfold_nth

doc <:doc<
   The @hrefterm[replace_nth] term is similar to the @hrefterm[nth]
   term, but it collects the list, and replaces the head element
   when the index reaches 0.
>>
interactive_rw reduce_replace_nth_cons {| reduce |} :
   replace_nth{cons{'u; 'v}; 'i; 't} <-->
      ifthenelse{beq_int{'i; 0}; cons{'t; 'v}; cons{'u; replace_nth{'v; .'i -@ 1; 't}}}

doc docoff

let fold_replace_nth = makeFoldC << replace_nth{'l; 'i; 't} >> unfold_replace_nth

doc <:doc<
   The @hrefterm[inset_at] inserts a new element into a list at the given location.
>>
interactive_rw insert_at_base {| reduce |} :
   insert_at{'l; 0; 't} <--> 't :: 'l

interactive_rw insert_at_step {| reduce |} :
   'n in nat -->
   insert_at{'l; 'n +@ 1; 't} <--> hd{'l} :: insert_at{tl{'l}; 'n; 't}

interactive_rw insert_at_cons {| reduce |} :
   'n in nat -->
   insert_at{'hd::'tl; 'n +@ 1; 't} <--> 'hd :: insert_at{'tl; 'n; 't}

doc <:doc<
   The @hrefterm[rev] term reverses the list.
   This particular computation is rather inefficient;
   it appends the head of the list to the reversed tail.
>>
interactive_rw reduce_rev_nil {| reduce |} : rev{nil} <--> nil

interactive_rw reduce_rev_cons {| reduce |} : rev{cons{'u;'v}} <--> append{rev{'v};cons{'u;nil}}

doc docoff

let fold_rev = makeFoldC << rev{'l} >> unfold_rev

doc <:doc<
   The @hrefterm[map] term performs induction over the list $l$,
   applying the function to each element, and collecting the results.
>>
interactive_rw reduce_map_nil {| reduce |} :
   map{'f; nil} <--> nil

interactive_rw reduce_map_cons {| reduce |} :
   map{'f; cons{'h; 't}} <--> cons{'f 'h; map{'f; 't}}

interactive_rw reduce_map2_nil {| reduce |} :
   map{x.'f['x]; nil} <--> nil

interactive_rw reduce_map2_cons {| reduce |} :
   map{x.'f['x]; cons{'h; 't}} <--> cons{'f['h]; map{x.'f['x]; 't}}

interactive_rw reduce_map_id {| reduce |} :
   ('l in list) -->
   map{x.'x; 'l} <--> 'l

interactive_rw length_map {| reduce |} :
   ('l in list) -->
   length{map{'f; 'l}} <--> length{'l}

interactive_rw length_map2 {| reduce |} :
   ('l in list) -->
   length{map{x.'f['x]; 'l}} <--> length{'l}

interactive_rw index_map {| reduce |} :
   ('l in list) -->
   Index{map{'f; 'l}} <--> Index{'l}

interactive_rw index_map2 {| reduce |} :
   ('l in list) -->
   Index{map{x.'f['x]; 'l}} <--> Index{'l}

doc docoff

let fold_map = makeFoldC << map{'f; 'l} >> unfold_map

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let t_var = Lm_symbol.add "T"

let infer_hd inf consts decls eqs opt_eqs defs t =
   let l = one_subterm t in
   let eqs, opt_eqs, defs, tp_l = inf consts decls eqs opt_eqs defs l in
      if is_list_term tp_l then
         eqs, opt_eqs, defs, dest_list tp_l
      else
         let t = Typeinf.vnewname consts defs t_var in
         let tt = mk_var_term t in
         let eqs = Unify_mm.eqnlist_append_eqn eqs tp_l (mk_list_term tt) in
            eqs, opt_eqs, (t, <<top>>) :: defs, tt

let infer_append inf consts decls eqs opt_eqs defs t =
   let l1, l2 = two_subterms t in
   let eqs, opt_eqs, defs, tp_l1 = inf consts decls eqs opt_eqs defs l1 in
   let eqs, opt_eqs, defs, tp_l2 = inf consts decls eqs opt_eqs defs l2 in
      eqs, (tp_l1, tp_l2) :: opt_eqs, defs, tp_l1

let resource typeinf += [
   << length{'l}>>, Typeinf.infer_const << nat >>;
   << tl{'l} >>, Typeinf.infer_map one_subterm;
   << hd{'l} >>, infer_hd;
   << append{'l1; 'l2} >>, infer_append
]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules

   The rules in the @hrefmodule[Itt_list2] are mostly limited to
   well-formedness of each of the constructions.
>>

interactive listelim {| elim [] |} 'H :
   sequent { <H>; l: list; <J['l]> >- 'C[nil] } -->
   sequent { <H>; l: list; <J['l]>; u: top; v: list; w: 'C['v] >- 'C['u::'v] } -->
   sequent { <H>; l: list; <J['l]> >- 'C['l] }

interactive hd_wf {| intro [] |} :
   [wf] sequent  { <H> >- 'l in list{'T} } -->
   sequent  { <H> >- not{'l = nil in list{'T}} } -->
   sequent  { <H> >- hd{'l} in 'T }

interactive hd_wf1 {| intro [] |} :
   [wf] sequent  { <H> >- 'l1 = 'l2 in list{'T} } -->
   sequent  { <H> >- not{'l1 = nil in list{'T}} } -->
   sequent  { <H> >- hd{'l1} = hd{'l2} in 'T }

interactive tl_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l in list{'T} } -->
   sequent  { <H> >- not{'l = nil in list{'T}} } -->
   sequent  { <H> >- tl{'l} in list{'T} }

interactive tl_wf1 {| intro [] |} :
   [wf] sequent  { <H> >- 'l1 = 'l2 in list{'T} } -->
   sequent  { <H> >- not{'l1 = nil in list{'T}} } -->
   sequent  { <H> >- tl{'l1} = tl{'l2} in list{'T} }

interactive_rw tl_hd_rw list{'T} :
   ('l in list{'T})  -->
   (not{'l = nil in list{'T}}) -->
     cons{hd{'l};tl{'l}} <--> 'l

interactive is_nil_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l in list } -->
   sequent { <H> >- is_nil{'l} in bool }

(*
 * Membership.
 *)
interactive mem_univ_wf {| intro [] |} :
   [wf] sequent { <H> >- 'T1 = 'T2 in univ[i:l] } -->
   [wf] sequent { <H> >- 'x1 = 'x2 in 'T1 } -->
   [wf] sequent { <H> >- 'l1 = 'l2 in list{'T1} } -->
   sequent { <H> >- mem{'x1; 'l1; 'T1} = mem{'x2; 'l2; 'T2} in univ[i:l] }

interactive mem_wf {| intro [] |} :
   [wf] sequent { <H> >- "type"{'T} } -->
   [wf] sequent { <H> >- 'x in 'T } -->
   [wf] sequent { <H> >- 'l in list{'T} } -->
   sequent { <H> >- "type"{mem{'x; 'l; 'T}} }

(*
 * Subset.
 *)
interactive subset_wf {| intro [] |} :
   [wf] sequent { <H> >- "type"{'T} } -->
   [wf] sequent { <H> >- 'l1 in list{'T} } -->
   [wf] sequent { <H> >- 'l2 in list{'T} } -->
   sequent { <H> >- "type"{\subset{'l1; 'l2; 'T}} }

(*
 * Sameset.
 *)
interactive sameset_wf {| intro [] |} :
   [wf] sequent { <H> >- "type"{'T} } -->
   [wf] sequent { <H> >- 'l1 in list{'T} } -->
   [wf] sequent { <H> >- 'l2 in list{'T} } -->
   sequent { <H> >- "type"{sameset{'l1; 'l2; 'T}} }

(*
 * Append.
 *)
interactive append_wf2 {| intro [] |} :
   [wf] sequent { <H> >- 'l1 in list{'T} } -->
   [wf] sequent { <H> >- 'l2 in list{'T} } -->
   sequent { <H> >- append{'l1; 'l2} in list{'T} }

(*
 * Ball2.
 *)
interactive ball2_wf2 {| intro [] |} 'T1 'T2 :
   [wf] sequent { <H> >- "type"{'T1} } -->
   [wf] sequent { <H> >- "type"{'T2} } -->
   [wf] sequent { <H> >- 'l1 in list{'T1} } -->
   [wf] sequent { <H> >- 'l2 in list{'T2} } -->
   [wf] sequent { <H>; u: 'T1; v: 'T2 >- 'b['u; 'v] in bool } -->
   sequent { <H> >- ball2{'l1; 'l2; x, y. 'b['x; 'y]} in bool }

(*
 * assoc2.
 *)
interactive assoc_wf {| intro [intro_typeinf <<'l>>] |} 'z list{'T1 * 'T2} :
   [wf] sequent { <H> >- "type"{'T2} } -->
   [wf] sequent { <H> >- 'eq in 'T1 -> 'T1 -> bool } -->
   [wf] sequent { <H> >- 'x in 'T1 } -->
   [wf] sequent { <H> >- 'l in list{'T1 * 'T2} } -->
   [wf] sequent { <H>; z: 'T2 >- 'b['z] in 'T } -->
   [wf] sequent { <H> >- 'z in 'T } -->
   sequent { <H> >- assoc{'eq; 'x; 'l; v. 'b['v]; 'z} in 'T }

interactive rev_assoc_wf {| intro [intro_typeinf <<'l>>] |} 'z list{'T1 * 'T2} :
   [wf] sequent { <H> >- "type"{'T1} } -->
   [wf] sequent { <H> >- 'eq in 'T2 -> 'T2 -> bool } -->
   [wf] sequent { <H> >- 'x in 'T2 } -->
   [wf] sequent { <H> >- 'l in list{'T1 * 'T2} } -->
   [wf] sequent { <H>; z: 'T1 >- 'b['z] in 'T } -->
   [wf] sequent { <H> >- 'z in 'T } -->
   sequent { <H> >- rev_assoc{'eq; 'x; 'l; v. 'b['v]; 'z} in 'T }

(*
 * Fold_left.
 *)
interactive fold_left_wf {| intro [intro_typeinf <<'l>>] |} list{'T1} :
   [wf] sequent { <H> >- "type"{'T1} } -->
   [wf] sequent { <H> >- "type"{'T2} } -->
   [wf] sequent { <H> >- 'f in 'T1 -> 'T2 -> 'T2 } -->
   [wf] sequent { <H> >- 'v in 'T2 } -->
   [wf] sequent { <H> >- 'l in list{'T1} } -->
   sequent { <H> >- fold_left{'f; 'v; 'l} in 'T2 }

(*
 * Length.
 *)
interactive length_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l in list } -->
   sequent { <H> >- length{'l} in int }
(*
interactive length_eq_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l1 = 'l2 in list } -->
   sequent { <H> >- length{'l1} =  length{'l2}  in int }
*)
interactive length_nonneg {| intro [] |}  :
   [wf] sequent { <H> >- 'l in list } -->
   sequent { <H> >- 0 <= length{'l} }

interactive length_wf2 {| intro [] |} :
   [wf] sequent { <H> >- 't in list } -->
   sequent { <H> >- length{cons{'h;'t}} in nat }

interactive length_wf1 {| intro [] |} :
   [wf] sequent { <H> >- 'l in list } -->
   sequent { <H> >- length{'l} in nat }

interactive length_cons_pos {| intro [] |} :
   [wf] sequent { <H> >- 't in list } -->
   sequent { <H> >- 0 < length{cons{'h;'t}} }

interactive listTop {| nth_hyp |} 'H :
   sequent { <H>; l : list{'A}; <J['l]> >- 'l in list }

interactive listTop2 {| intro[AutoMustComplete; intro_typeinf <<'l>>] |} list{'A} :
   sequent { <H> >- 'l in list{'A} } -->
   sequent { <H> >- 'l in list }
(*
interactive listTop3 {| intro[AutoMustComplete; intro_typeinf <<'l1>>] |} list{'A} :
   sequent { <H> >- 'l1 = 'l2 in list{'A} } -->
   sequent { <H> >- 'l1 = 'l2 in list }
*)
interactive index_wf {| intro [] |}  :
   [wf] sequent { <H> >- 'l in list } -->
   sequent { <H> >- Index{'l} Type }

interactive index_mem {| intro [AutoMustComplete] |} :
    sequent { <H> >- 'i in nat } -->
    sequent { <H> >- 'i < length{'l} } -->
    sequent { <H> >- 'l in list } -->
    sequent { <H> >- 'i in Index{'l} }

interactive index_elim {| elim [] |} 'H :
   sequent { <H>; i:nat; 'i<length{'l}; <J['i]> >-  'P['i] } -->
   sequent { <H>; i:Index{'l}; <J['i]> >-  'P['i] }

interactive index_is_int {| nth_hyp |} 'H :
    sequent { <H>; i:Index{'l}; <J['i]> >- 'i in int }

interactive index_nil_elim {| elim []; squash; nth_hyp |} 'H :
   sequent { <H>; i:Index{nil}; <J['i]> >-  'P['i] }

interactive nth_wf {| intro [] |} :
   [wf] sequent { <H> >- "type"{'T} } -->
   [wf] sequent { <H> >- 'l in list{'T} } -->
   [wf] sequent { <H> >- 'i in Index{'l} } -->
   sequent { <H> >- nth{'l; 'i} in 'T }

interactive index_rev_wf {| intro[] |} :
   [wf] sequent { <H> >- 'l in list } -->
   sequent { <H> >-  'i in Index{'l} } -->
   sequent { <H> >-  length{'l} -@ ('i +@ 1) in Index{'l} }

interactive replace_nth_wf {| intro [] |} :
   [wf] sequent { <H> >- "type"{'T} } -->
   [wf] sequent { <H> >- 'l in list{'T} } -->
   [wf] sequent { <H> >- 'i in Index{'l} } -->
   [wf] sequent { <H> >- 't in 'T } -->
   sequent { <H> >- replace_nth{'l; 'i; 't} in list{'T} }

interactive insert_at_wf {| intro [] |} :
   [wf] sequent { <H> >- "type"{'T} } -->
   [wf] sequent { <H> >- 'l in list{'T} } -->
   [wf] sequent { <H> >- 'i in Index{'t::'l} } -->
   [wf] sequent { <H> >- 't in 'T } -->
   sequent { <H> >- insert_at{'l; 'i; 't} in list{'T} }

interactive list_lengthzero {| elim [] |} 'H 'A :
   sequent { <H>; x: (length{'l} = 0 in int); <J[it]> >- 'A Type } -->
   sequent { <H>; x: (length{'l} = 0 in int); <J[it]> >- 'l in list{'A} } -->
   sequent { <H>; x: (length{'l} = 0 in int); <J[it]>; y: 'l = nil in list{'A} >- 'C[it] } -->
   sequent { <H>; x: (length{'l} = 0 in int); <J['x]> >- 'C['x] }

interactive_rw nth_map {| reduce |} :
   ('l in list) -->
   ('i in Index{'l}) -->
   nth{map{'f; 'l};'i} <--> 'f(nth{'l;'i})

interactive_rw nth_map2 {| reduce |} :
   ('l in list) -->
   ('i in Index{'l}) -->
   nth{map{x.'f['x]; 'l};'i} <--> 'f[nth{'l;'i}]

interactive nth_eq {| intro [] |} :
   [wf] sequent { <H> >- "type"{'T} } -->
   [wf] sequent { <H> >- 'l1 = 'l2 in list{'T} } -->
   [wf] sequent { <H> >- 'i in Index{'l1} } -->
   sequent { <H> >- nth{'l1; 'i} = nth{'l2; 'i} in 'T }

(*
 * Reverse.
 *)
interactive rev_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l in list{'A} } -->
   sequent { <H> >- rev{'l} in list{'A} }

interactive_rw rev_append 'A :
   ('a in list{'A}) -->
   ('b in list{'A}) -->
   rev{append{'a;'b}} <--> append{rev{'b};rev{'a}}

doc <:doc< Double-reverse is identity. >>

interactive_rw rev2 'A :
   ('l in list{'A}) -->
   rev{rev{'l}} <--> 'l


doc <:doc<
   @rules
   Rules for the @tt[mem] operator.
>>
interactive mem_nil {| intro[] |} :
   sequent { <H> >- "false" } -->
   sequent { <H> >- mem{'x; nil; 'T} }

interactive mem_cons2 {| intro[AutoMustComplete] |} :
   [wf] sequent { <H> >- 'x in 'T } -->
   [wf] sequent { <H> >- 'h in 'T } -->
   sequent { <H> >- mem{'x; 't; 'T}  } -->
   sequent { <H> >- mem{'x; 'h::'t; 'T} }

interactive mem_cons1 {| intro[] |} :
   [wf] sequent { <H> >- 'x in 'T } -->
   [wf] sequent { <H> >- 't in list{'T} } -->
   sequent { <H> >- mem{'x; 'x::'t; 'T} }

interactive restrict_list {| intro[] |} :
   sequent { <H> >- 'A Type } -->
   sequent { <H> >- 'l in list{'A} } -->
   sequent { <H> >- 'l in list{{x:'A | mem{'x;'l;'A}}} }

doc <:doc<
    The following induction principle is used for simultaneous induction on two lists.
>>
(*
interactive list_induction2 :
   sequent { <H> >- 'P[nil; nil] } -->
   sequent { <H>; h2:'B; t2:list{'B} >- 'P[nil; 'h2::'t2] } -->
   sequent { <H>; h1:'A; t1:list{'A} >- 'P['h1::'t1; nil] } -->
   sequent { <H>; h1:'A; t1:list{'A}; h2:'B; t2:list{'B};  'P['t1;'t2] >- 'P['h1::'t1;'h2::'t2] } -->
   sequent { <H>; l1:list{'A}; l2:list{'B} >- 'P['l1; 'l2] }
*)
define unfold_list_of_fun:
   list_of_fun{k.'f['k]; 'n}
   <-->
   ind{'n; lambda{f.nil}; k,r. lambda{f.'f 0:: 'r lambda{k. 'f ('k +@ 1)}}} lambda{k.'f['k]}

interactive_rw reduce_list_of_fun_base {| reduce |}:
   list_of_fun{k.'f['k]; 0} <--> nil

interactive_rw reduce_list_of_fun_step {| reduce |}:
   'n in nat -->
   list_of_fun{k.'f['k]; 'n +@ 1} <--> 'f[0]:: list_of_fun{k.'f['k +@ 1]; 'n}

interactive_rw reduce_length_lof {| reduce |}:
   'n in nat -->
   length{list_of_fun{k.'f['k]; 'n}} <--> 'n

interactive list_of_fun_id {| intro [] |} :
   sequent { <H> >- 'n1 = 'n2 in nat } -->
   sequent { <H>; k: nat; 'k < 'n1 >- 'f1['k] ~ 'f2['k] } -->
   sequent { <H> >- list_of_fun{k.'f1['k]; 'n1} ~ list_of_fun{k.'f2['k]; 'n2} }

interactive_rw list_elements_id {| reduce |} :
   'l in list -->
   list_of_fun{k.nth{'l;'k}; length{'l}} <--> 'l

doc <:doc<
   We also provide the @conv[listIntoElementsC] for exploding a list according to the above
   @hrefrewrite[list_elements_id] rewrite.
   @docoff
>>
let listIntoElementsC =
   let k = Lm_symbol.add "k" in
   fun l ->
      let k = maybe_new_var_set k (free_vars_set l) in
      foldC <:con< list_of_fun{$k$.nth{$l$;'$k$}; length{$l$}} >> list_elements_id

doc docon

interactive_rw map_list_of_fun {| reduce |} :
   'n in nat -->
   map{v.'f1['v]; list_of_fun{k.'f2['k]; 'n}} <--> list_of_fun{k.'f1['f2['k]]; 'n}

interactive_rw nth_map_list_of_fun {| reduce |} :
   'n in nat -->
   'm in nat -->
   'm < 'n -->
   nth{list_of_fun{k.'f['k]; 'n}; 'm} <--> 'f['m]

interactive list_of_fun_wf {| intro [] |} :
   sequent { <H> >- 'n in nat } -->
   sequent { <H>; k: nat; 'k < 'n >- 'f['k] in 'A } -->
   sequent { <H> >- 'A Type } -->
   sequent { <H> >- list_of_fun{k.'f['k]; 'n} in list{'A} }

define unfold_tail: tail{'l;'n} <--> ind{'n; nil;   k,r. cons{nth{'l;length{'l} -@ 'k}; 'r} }

interactive_rw tail_reduce1 {| reduce |}:
   tail{'l;0} <--> nil
interactive_rw tail_reduce2 {| reduce |}: ('n in nat) -->
   tail{'l;'n+@1} <-->  cons{nth{'l;length{'l} -@ ('n +@ 1)};  tail{'l;'n} }

interactive tail_does_not_depend_on_the_head {| intro[] |}:
   sequent { <H> >-  'l in list } -->
   sequent { <H> >-  'n in nat } -->
   sequent { <H> >- 'n <= length{'l} } -->
   sequent { <H> >- tail{'l;'n} ~ tail{cons{'h;'l};'n}  }

interactive list_is_its_own_tail {| intro[] |}:
   sequent { <H> >-  'l in list } -->
   sequent { <H> >- 'l ~ tail{'l;length{'l}} }

interactive tail_squiggle {| intro[] |}:
   sequent { <H> >-  'n in nat } -->
   sequent { <H>; i:nat; 'i<'n >-  nth{'l_1;length{'l_1}-@('i+@1)} ~ nth{'l_2;length{'l_2}-@('i+@1)} } -->
   sequent { <H> >-  tail{'l_1;'n} ~ tail{'l_2;'n} }

interactive tail_wf {| intro[] |}:
   [wf] sequent { <H> >- 'A Type } -->
   [wf] sequent { <H> >-  'l in list{'A} } -->
   [wf] sequent { <H> >-  'n in nat } -->
   sequent { <H> >- 'n <= length{'l} } -->
   sequent { <H> >- tail{'l;'n} in list{'A} }

interactive listSquiggle :
   [wf] sequent { <H> >- 'l1 in list } -->
   [wf] sequent { <H> >- 'l2 in list } -->
   [wf] sequent { <H> >- length{'l1} = length{'l2} in nat } -->
   sequent { <H>; i: Index{'l1} >- nth{'l1; 'i} ~ nth{'l2; 'i} } -->
   sequent { <H> >- 'l1 ~ 'l2 }

interactive tail_induction 'H :
   sequent { <H>; l:list{'A}; <J['l]> >-  'P[nil] } -->
   sequent { <H>; l:list{'A}; <J['l]>; n:Index{'l}; 'P[tail{'l;'n}] >- 'P[ cons{nth{'l;length{'l} -@ ('n +@ 1)};  tail{'l;'n}}] } -->
   sequent { <H>; l:list{'A}; <J['l]> >-  'P['l] }

doc <:doc<
   @rules
   Rules for quantifiers are the following:
>>
interactive all_list_wf  {| intro[] |} :
   sequent { <H> >- 'l in list  } -->
   sequent { <H>; i:Index{'l}  >- 'P[nth{'l;'i}] Type } -->
   sequent { <H> >- all_list{'l;  x. 'P['x]} Type }

interactive all_list_intro_nil  {| intro[] |} :
   sequent { <H> >- all_list{nil;  x. 'P['x]} }

interactive all_list_intro_cons  {| intro[] |} :
   sequent { <H> >-  'P['a] } -->
   sequent { <H> >-  all_list{'l; x. 'P['x]} } -->
   sequent { <H> >- all_list{cons{'a; 'l};  x. 'P['x]} }

interactive all_list_intro  {| intro[] |} :
   sequent { <H> >- 'l in list  } -->
   sequent { <H>; i:Index{'l}  >- 'P[nth{'l;'i}]  } -->
   sequent { <H> >- all_list{'l;  x. 'P['x]} }

interactive all_list_intro1  {| intro[SelectOption 1;  intro_typeinf <<'l>>] |} list{'A} :
   sequent { <H> >- 'A Type  } -->
   sequent { <H> >- 'l in list{'A}  } -->
   sequent { <H>; x:'A; mem{'x; 'l; 'A}  >- 'P['x]  } -->
   sequent { <H> >- all_list{'l;  x. 'P['x]} }

interactive all_list_elim {| elim[] |} 'H  'i :
   sequent { <H>; u: all_list{'l;  x. 'P['x]}; <J['u]> >- 'l in list  } -->
   sequent { <H>; u: all_list{'l;  x. 'P['x]}; <J['u]> >- 'i in Index{'l}  } -->
   sequent { <H>; u: all_list{'l;  x. 'P['x]}; <J['u]>; 'P[nth{'l;'i}] >- 'C['u] } -->
   sequent { <H>; u: all_list{'l;  x. 'P['x]}; <J['u]> >- 'C['u] }

interactive all_list_map  {| intro[] |} :
   [wf] sequent { <H> >- 'l in list  } -->
   sequent { <H> >-  all_list{'l; x. 'P['f('x)]} } -->
   sequent { <H> >- all_list{map{'f;'l};  y. 'P['y]} }

interactive all_list_witness_wf  {| intro[intro_typeinf <<'l>>] |} list{'A} :
   sequent { <H> >- 'A Type  } -->
   sequent { <H> >- 'l in list{'A}  } -->
   sequent { <H>; x:'A; mem{'x; 'l; 'A} >- 'p['x] in 'P['x]  } -->
   sequent { <H> >- all_list_witness{'l;  x. 'p['x]} in all_list{'l;  x. 'P['x]} }

interactive all_list_witness_wf2  {| intro[] |} :
   sequent { <H> >- 'l in list } -->
   sequent { <H> >- all_list{'l;  x. 'p['x] in 'P['x]}  } -->
   sequent { <H> >- all_list_witness{'l;  x. 'p['x]} in all_list{'l;  x. 'P['x]} }

(*
 * map.
 *)
interactive map_wf {| intro [intro_typeinf <<'l>>] |} list{'T1} :
   [wf] sequent { <H> >- "type"{'T1} } -->
   [wf] sequent { <H> >- "type"{'T2} } -->
   [wf] sequent { <H> >- 'f in 'T1 -> 'T2 } -->
   [wf] sequent { <H> >- 'l in list{'T1} } -->
   sequent { <H> >- map{'f; 'l} in list{'T2} }

interactive map_wf2 {| intro [] |} :
   [wf] sequent { <H> >- "type"{'T2} } -->
   [wf] sequent { <H> >- 'l in list } -->
   [wf] sequent { <H> >- all_list{'l;x.'f['x] in 'T2} } -->
   sequent { <H> >- map{x.'f['x]; 'l} in list{'T2} }

interactive list_wf2  :
   [wf] sequent { <H> >- "type"{'T2} } -->
   [wf] sequent { <H> >- 'l in list } -->
   [wf] sequent { <H> >- all_list{'l;x.'x in 'T2} } -->
   sequent { <H> >- 'l in list{'T2} }

interactive map_wf3 {| intro [] |} :
   [wf] sequent { <H> >- 'l in list } -->
   sequent { <H> >- map{x.'f['x]; 'l} in list }

doc <:doc<
   A list $v$ is a subset of the list <<cons{'u; 'v}>>.
>>
interactive subset_cons {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'u in 'A } -->
   [wf] sequent { <H> >- 'v in list{'A} } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   sequent { <H> >- \subset{'v; 'l; 'A} } -->
   sequent { <H> >- \subset{'v; cons{'u; 'l}; 'A} }

doc <:doc<
   @rules

   @tt[subset] is reflexive and transitive.
>>
interactive subset_ref {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   sequent { <H> >- \subset{'l; 'l; 'A} }

interactive subset_trans 'l2 :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'l1 in list{'A} } -->
   [wf] sequent { <H> >- 'l2 in list{'A} } -->
   [wf] sequent { <H> >- 'l3 in list{'A} } -->
   sequent { <H> >- \subset{'l1; 'l2; 'A} } -->
   sequent { <H> >- \subset{'l2; 'l3; 'A} } -->
   sequent { <H> >- \subset{'l1; 'l3; 'A} }

doc <:doc<
   @rules

   @tt[sameset] is reflexive, symmetric, and transitive.
>>
interactive sameset_ref {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'l in list{'A} } -->
   sequent { <H> >- sameset{'l; 'l; 'A} }

interactive sameset_sym :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'l1 in list{'A} } -->
   [wf] sequent { <H> >- 'l2 in list{'A} } -->
   sequent { <H> >- sameset{'l1; 'l2; 'A} } -->
   sequent { <H> >- sameset{'l2; 'l1; 'A} }

interactive sameset_trans 'l2 :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'l1 in list{'A} } -->
   [wf] sequent { <H> >- 'l2 in list{'A} } -->
   [wf] sequent { <H> >- 'l3 in list{'A} } -->
   sequent { <H> >- sameset{'l1; 'l2; 'A} } -->
   sequent { <H> >- sameset{'l2; 'l3; 'A} } -->
   sequent { <H> >- sameset{'l1; 'l3; 'A} }

doc <:doc<
    The <<find{'l; 'a; x,y.'eq['x;'y]}>> returns an index of an element in the list $l$ equal to the element $a$
    according to equality $@it[eq]$.
    It returns the length of the list otherwise.
>>

define unfold_find: find{'l; 'a; x,y.'eq['x;'y]} <--> list_ind{'l; 0; hd,tl,r. if 'eq['hd;'a] then 0 else 'r +@ 1}

interactive_rw reduce_find_nil {| reduce |} :
   find{nil; 'a; x,y.'eq['x;'y]} <--> 0
interactive_rw reduce_find_cons {| reduce |} :
   find{'hd::'tl; 'a; x,y.'eq['x;'y]} <--> (if 'eq['hd;'a] then 0 else find{'tl; 'a; x,y.'eq['x;'y]} +@ 1)

interactive find_wf  {| intro [intro_typeinf <<'l>>] |}  list{'T} :
   sequent  { <H> >- 'l in list{'T} } -->
   sequent  { <H> >- 'a in 'T } -->
   sequent  { <H>; x:'T; y:'T >- 'eq['x;'y] in bool } -->
   sequent  { <H> >- find{'l; 'a; x,y.'eq['x;'y]} in nat }

interactive find_wf2  {| intro [intro_typeinf <<'l>>] |}  list{'T} :
   sequent  { <H> >- 'l in list{'T} } -->
   sequent  { <H> >- 'a in 'T } -->
   sequent  { <H>; x:'T; y:'T >- 'eq['x;'y] in bool } -->
   sequent  { <H> >- find{'l; 'a; x,y.'eq['x;'y]} in int }

interactive find_when_found_wf  {| intro [intro_typeinf <<'l>>] |}  list{'T} :
   sequent  { <H> >- 'l in list{'T} } -->
   sequent  { <H> >- 'a in 'T } -->
   sequent  { <H> >- mem{'a;'l;'T} } -->
   sequent  { <H>; x:'T; y:'T >- 'eq['x;'y] in bool } -->
   sequent  { <H> >- "assert"{'eq['a;'a]} } -->
   sequent  { <H> >- find{'l; 'a; x,y.'eq['x;'y]} in Index{'l} }

interactive find_correct_when_found  <<find{'l; 'a; x,y.'eq['x;'y]}>>  list{'T}:
   sequent  { <H> >- 'l in list{'T} } -->
   sequent  { <H> >- 'a in 'T } -->
   sequent  { <H>; x:'T; y:'T >- 'eq['x;'y] in bool } -->
   sequent  { <H> >- "assert"{'eq['a;'a]} } -->
   sequent  { <H> >- mem{'a;'l;'T} } -->
   sequent  { <H> >- "assert"{'eq[nth{'l;find{'l; 'a; x,y.'eq['x;'y]}};'a]} }

interactive find_when_not_found_wf  {| intro [intro_typeinf <<'l>>] |}  list{'T} :
   sequent  { <H> >- 'l in list{'T} } -->
   sequent  { <H> >- 'a in 'T } -->
   sequent  { <H>; x:'T; y:'T >- 'eq['x;'y] in bool } -->
   sequent  { <H> >- all_list{'l; x.not{"assert"{'eq['x;'a]}}} } -->
   sequent  { <H> >- find{'l; 'a; x,y.'eq['x;'y]} = length{'l} in int }

doc <:doc<
    The <<diff_list{'T}>> defines a type of lists with @emph{different} elements.
>>

define unfold_diff_list: diff_list{'T} <--> {l:list{'T} | all i:Index{'l}. all j:Index{'l}. ('i < 'j => nth{'l;'i} <> nth{'l;'j} in 'T)}

interactive diff_list_wf  {| intro[] |} :
   sequent  { <H> >- 'T Type } -->
   sequent  { <H> >- diff_list{'T} Type }

interactive diff_list_mem  {| intro[] |} :
   sequent  { <H> >- 'T Type } -->
   sequent  { <H> >- 'l in list{'T} } -->
   sequent { <H>; i: Index{'l}; j: Index{'l}; 'i < 'j >- nth{'l;'i} <> nth{'l;'j} in 'T } -->
   sequent  { <H> >- 'l in diff_list{'T} }

interactive diff_list_elim {| elim [] |} 'H :
   sequent { <H>; l: diff_list{'T}; <J['l]> >- 'T Type } -->
   sequent { <H>; l: list{'T}; all i:Index{'l}. all j:Index{'l}. ('i < 'j => nth{'l;'i} <> nth{'l;'j} in 'T); <J['l]> >- 'C['l] } -->
   sequent { <H>; l: diff_list{'T}; <J['l]> >- 'C['l] }

interactive difflist {| nth_hyp |} 'H :
   sequent { <H>; l : diff_list{'A}; <J['l]> >- 'l in list{'A} }

doc <:doc<  The <<list_max{'l}>> defines the maximal element of a list of natural numbers.  >>

interactive_rw reduce_list_max_nil {| reduce |} :
   list_max{nil} <--> 0

interactive_rw reduce_list_max_cons {| reduce |} :
   list_max{cons{'h; 't}} <--> max{'h; list_max{'t}}

interactive list_max_wf {| intro [] |} :
   sequent { <H> >- 'l in list{nat} } -->
   sequent { <H> >- list_max{'l} in nat }

interactive list_max_wf2 {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'l in list{nat} } -->
   sequent { <H> >- list_max{'l} in int }

interactive list_max1 {| intro [] |} 'i:
   [wf] sequent { <H> >- 'l in list{nat} } -->
   [wf] sequent { <H> >- 'i in Index{'l} } -->
   sequent { <H> >- 'a <= nth{'l;'i} } -->
   sequent { <H> >- 'a <= list_max{'l}}

interactive list_max2 {| intro [] |}:
   [wf] sequent { <H> >- 'l in list{nat} } -->
   sequent { <H>; i : Index{'l}  >- nth{'l;'i} <= 'a } -->
   sequent { <H> >- list_max{'l} <= 'a }

doc <:doc<
    The <<list{'X}>> operator is a continuous operator with respect to topology generated by subtyping relation.
>>

interactive list_continuous {| intro[] |}:
   [wf] sequent { <H>; i:nat >- 'A['i] Type} -->
   [monotone] sequent { <H>; i:nat >- 'A['i] subtype 'A['i+@1] } -->
   sequent { <H> >- ext_equal{ list{Union i:nat.'A['i]}; Union i:nat.list{'A['i]} } }

doc <:doc<
    <<listmem_set{'l; 'T}>> defines the set of elements in <<'T>> that are members of list <<'l>>.
>>
define unfold_listmem_set: listmem_set{'l; 'T} <--> { t: 'T | mem{'t; 'l; 'T} }

dform listmem_set_df : listmem_set{'l; 'T} =
   szone `"Mem{" slot{'l} hspace `": " slot{'T} `" list}" ezone

interactive mem_sqstable (*{| squash |}*) :
   [wf] sequent { <H> >- 'l in list{'T} } -->
   [wf] sequent { <H> >- 't in 'T } -->
   [aux] sequent { <H>; x: 'T; y: 'T >- decidable{'x = 'y in 'T} } -->
   sequent { <H> >- squash{mem{'t; 'l; 'T}}  } -->
   sequent { <H> >- mem{'t; 'l; 'T} }

interactive listmem_set_wf {| intro [] |} :
   [wf] sequent { <H> >- 'T Type } -->
   [wf] sequent { <H> >- 'l in list{'T} } -->
   sequent { <H> >- listmem_set{'l; 'T} Type }

interactive listmem_set_intro {| intro [] |} :
   [wf] sequent { <H> >- 'x in 'T } -->
   [wf] sequent { <H> >- 'l in list{'T} } -->
   sequent { <H> >- squash{mem{'x; 'l; 'T}} } -->
   sequent { <H> >- 'x in listmem_set{'l; 'T} }

interactive listmem_set_elim {| elim [] |} 'H :
   sequent { <H>; x: 'T; i: squash{mem{'x;'l;'T}}; <J['x]> >- 'C['x] } -->
   sequent { <H>; x: listmem_set{'l; 'T}; <J['x]> >- 'C['x] }

interactive listmem_set_elim2 {| elim [ThinOption thinT] |} 'H :
   [wf] sequent { <H>; x: listmem_set{'h::'t; 'T}; <J['x]> >- 'h in 'T } -->
   [wf] sequent { <H>; x: listmem_set{'h::'t; 'T}; <J['x]> >- 't in list{'T} } -->
   [aux] sequent { <H>; x: listmem_set{'h::'t; 'T}; <J['x]> >- sqsimple{'T} } -->
   [aux] sequent { <H>; x: listmem_set{'h::'t; 'T}; <J['x]>; u: 'T; v: 'T >- decidable{'u = 'v in 'T} } -->
   sequent { <H>; x: listmem_set{'h::'t; 'T}; <J['h]> >- 'C['h] } -->
   sequent { <H>; x: listmem_set{'t; 'T}; <J['x]> >- 'C['x] } -->
   sequent { <H>; x: listmem_set{'h::'t; 'T}; <J['x]> >- 'C['x] }

doc docoff

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let samesetSymT = sameset_sym
let samesetTransT = sameset_trans

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)