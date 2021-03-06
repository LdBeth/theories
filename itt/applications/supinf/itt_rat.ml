doc <:doc<
   @module[Itt_rat]

   Rational numbers axiomatization.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2003-2006 MetaPRL Group, City University of New York
   Graduate Center and California Institute of Technology

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

   Author: Yegor Bryukhov
   @email{ybryukhov@gc.cuny.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_equal
extends Itt_dfun
extends Itt_bool
extends Itt_logic
extends Itt_struct
extends Itt_decidable
extends Itt_nequal
extends Itt_order
extends Itt_int_arith
extends Itt_field2
extends Itt_labels
doc docoff

open Lm_debug
open Lm_printf

open Basic_tactics

open Itt_dfun
open Itt_squash
open Itt_int_base
open Itt_int_ext
open Itt_int_arith

(* For display *)
declare cdot

dform cdot_df : cdot =
   Mpsymbols!cdot

(********************************************
 *	THIS PART SHOULD GO TO A SEPARATE MODULE *
 ********************************************)
define unfold_abs : abs{'a} <-->
	(if 'a <@ 0 then -'a else 'a)

define unfold_let_in {| reduce |} : let_in{'e1; v.'e2['v]} <--> 'e2['e1]

define unfold_gcd : gcd{'x; 'y} <-->
	(fix{gcd.lambda{a.lambda{b.
		if 'a =@ 1 then 1 else
		if 'b =@ 1 then 1 else
		let_in{abs{'a}; a.
		let_in{abs{'b}; b.
			if 'a =@ 0 then 'b else
			if 'b =@ 0 then 'a else
			if 'a <@ 'b then ('gcd 'a ('b %@ 'a)) else ('gcd ('a %@ 'b) 'b)
		}}
	}}} 'x 'y)

let resource reduce += [
	<<abs{number[i:n]}>>, wrap_reduce unfold_abs;
	<<gcd{number[i:n]; number[j:n]}>>, wrap_reduce (unfold_gcd thenC reduce_fix);
]

dform gcd_df1 : except_mode[src] :: gcd{'a; 'b}
 =
   `"gcd{" slot{'a} `";" slot{'b} `"}"

interactive gcd_wf_nat {| intro [] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- gcd{'a; 'b} in nat }

interactive gcd_wf_int {| intro [] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- gcd{'a; 'b} in int }

interactive gcd_nat_multiplier :
	[wf] sequent { <H> >- 'k in nat } -->
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H> >- gcd{'k *@ 'a; 'k *@ 'b} = 'k *@ gcd{'a; 'b} in int }
(**********************************************)

define unfold_posnat :
   posnat <--> ({x:int | 'x>0})

define unfold_int0 :
   int0 <--> ({x:int | 'x<>0})

define unfold_ratn : ratn{'a; 'b} <--> ('a, 'b)
let fold_ratn = makeFoldC <<ratn{'a; 'b}>> unfold_ratn

define unfold_rat : rat{'a; 'b} <-->
	(if 'b =@ 1 then ratn{'a; 'b} else
	if 'a =@ 0 then ratn{0;1} else
	if 'b >@ 0 then
		let_in{gcd{'a;'b}; d.ratn{('a /@ 'd); ('b /@ 'd)}}
	else
		let_in{gcd{'a;'b}; d.ratn{-( 'a /@ 'd); -('b /@ 'd)}})

define unfold_rat_of_int :
   rat_of_int{'a} <--> rat{'a; 1}

let resource reduce += [
	<<spread{ratn{'a; 'b}; x,y.'f['x; 'y]}>>, wrap_reduce (addrC [Subterm 1] unfold_ratn);
(*	<<rat{number[i:n]; number[j:n]}>>, wrap_reduce unfold_rat;*)
	<<rat_of_int{number[i:n]}>>, wrap_reduce unfold_rat_of_int;
]

define unfold_is_normed : is_normed{'x; 'y} <-->
	"assert"{bor{band{'x=@0; 'y=@1};	band{'y>@0; gcd{'x;'y}=@1}}}

define unfold_rationals : rationals <-->
	{ r: (int * int) | spread{'r; x,y.is_normed{'x; 'y}} }

let fold_rationals = makeFoldC <<rationals>> unfold_rationals

define unfold_neq_rat : neq_rat{'x; 'y} <-->
	spread{'x; x1,x2.spread{'y; y1,y2.(('x1 *@ 'y2) <> ('y1 *@ 'x2))}}

define unfold_mul_rat : mul_rat{'x; 'y} <-->
	spread{'x; x1,x2.spread{'y; y1,y2.rat{'x1 *@ 'y1; 'x2 *@ 'y2}}}

define unfold_add_rat : add_rat{'x; 'y} <-->
	spread{'x; x1,x2.spread{'y; y1,y2.rat{('x1 *@ 'y2) +@ ('x2 *@ 'y1); 'x2 *@ 'y2}}}

define unfold_neg_rat : neg_rat{'x} <-->
	spread{'x; x1,x2.rat{- 'x1; 'x2}}

define unfold_inv_rat : inv_rat{'x} <-->
	spread{'x; x1,x2.rat{'x2; 'x1}}

define unfold_sub_rat : sub_rat{'x; 'y} <-->
	add_rat{'x; neg_rat{'y}}

(*******************************)
(* CHECK !!!                   *)
define unfold_lt_bool_rat : lt_bool_rat{'a;'b} <-->
	spread{'a; a1,a2.spread{'b; b1,b2.lt_bool{('a1 *@ 'b2);('a2 *@ 'b1)}}}

define unfold_le_bool_rat : le_bool_rat{'a;'b} <--> bnot{lt_bool_rat{'b;'a}}
define unfold_gt_bool_rat : gt_bool_rat{'a;'b} <--> lt_bool_rat{'b;'a}
define unfold_ge_bool_rat : ge_bool_rat{'a;'b} <--> le_bool_rat{'b;'a}

define unfold_bneq_rat : bneq_rat{'x; 'y} <-->
	spread{'x; x1,x2.spread{'y; y1,y2.(('x1 *@ 'y2) <>@ ('y1 *@ 'x2))}}

define unfold_beq_rat : beq_rat{'x; 'y} <-->
	spread{'x; a,b.spread{'y; c,d.beq_int{('a *@ 'd) ; ('c *@ 'b)}}}

interactive_rw reduce_beq_rat :
   beq_rat{ ('a,'b) ; ('c,'d) } <--> beq_int{ ('a *@ 'd) ; ('c *@ 'b) }

define unfold_lt_rat : lt_rat{'a;'b} <--> "assert"{lt_bool_rat{'a;'b}}
define unfold_gt_rat : gt_rat{'a;'b} <--> lt_rat{'b;'a}
define unfold_le_rat : le_rat{'a;'b} <--> "assert"{le_bool_rat{'a;'b}}
define unfold_ge_rat : ge_rat{'a;'b} <--> le_rat{'b;'a}

(*                             *)
(*******************************)

define unfold_fieldQ : fieldQ <-->
	{car=rationals; "*"=lambda{x.lambda{y.mul_rat{'x;'y}}}; "1"=rat{1;1};
	 "+"=lambda{x.lambda{y.add_rat{'x;'y}}}; "0"=rat{0;1}; "neg"=lambda{x.(neg_rat{'x})};
	 car0={a: rationals | 'a <> rat{0;1} in rationals};
	 inv=lambda{x.rat{snd{'x};fst{'x}}}
	}

(* unused
let fold_fieldQ = makeFoldC <<fieldQ>> unfold_fieldQ
*)

define unfold_max_rat : max_rat{'a;'b} <-->
	(max{lambda{x.lambda{y.le_bool_rat{'x;'y}}}} 'a 'b)

define unfold_min_rat : min_rat{'a;'b} <-->
	(min{lambda{x.lambda{y.le_bool_rat{'x;'y}}}} 'a 'b)

let rationals_term = << rationals >>
let rationals_opname = opname_of_term rationals_term
let is_rationals_term = is_no_subterms_term rationals_opname

let ratn_term = << ratn{'x; 'y} >>
let ratn_opname = opname_of_term ratn_term
let is_ratn_term = is_dep0_dep0_term ratn_opname
(*let mk_ratn_term = mk_dep0_dep0_term ratn_opname*)
let dest_ratn = dest_dep0_dep0_term ratn_opname

let rat_term = << rat{'x; 'y} >>
let rat_opname = opname_of_term rat_term
let is_rat_term = is_dep0_dep0_term rat_opname
let mk_rat_term = mk_dep0_dep0_term rat_opname
let dest_rat = dest_dep0_dep0_term rat_opname

let rat_of_int_term = << rat_of_int{'x} >>
let rat_of_int_opname = opname_of_term rat_of_int_term
let is_rat_of_int_term = is_dep0_term rat_of_int_opname
let mk_rat_of_int_term = mk_dep0_term rat_of_int_opname
let dest_rat_of_int = dest_dep0_term rat_of_int_opname

let add_rat_term = << add_rat{'x; 'y} >>
let add_rat_opname = opname_of_term add_rat_term
let is_add_rat_term = is_dep0_dep0_term add_rat_opname
let mk_add_rat_term = mk_dep0_dep0_term add_rat_opname
let dest_add_rat = dest_dep0_dep0_term add_rat_opname

let mul_rat_term = << mul_rat{'x; 'y} >>
let mul_rat_opname = opname_of_term mul_rat_term
let is_mul_rat_term = is_dep0_dep0_term mul_rat_opname
let mk_mul_rat_term = mk_dep0_dep0_term mul_rat_opname
let dest_mul_rat = dest_dep0_dep0_term mul_rat_opname

let neg_rat_term = << neg_rat{'x} >>
let neg_rat_opname = opname_of_term neg_rat_term
let is_neg_rat_term = is_dep0_term neg_rat_opname
let mk_neg_rat_term = mk_dep0_term neg_rat_opname
let dest_neg_rat = dest_dep0_term neg_rat_opname

let inv_rat_term = << inv_rat{'x} >>
let inv_rat_opname = opname_of_term inv_rat_term
let is_inv_rat_term = is_dep0_term inv_rat_opname
let mk_inv_rat_term = mk_dep0_term inv_rat_opname
let dest_inv_rat = dest_dep0_term inv_rat_opname

(* unused
let beq_rat_term = << beq_rat{'x; 'y} >>
let beq_rat_opname = opname_of_term beq_rat_term
let is_beq_rat_term = is_dep0_dep0_term beq_rat_opname
let mk_beq_rat_term = mk_dep0_dep0_term beq_rat_opname
let dest_beq_rat = dest_dep0_dep0_term beq_rat_opname
 *)

let le_bool_rat_term = << le_bool_rat{'x; 'y} >>
let le_bool_rat_opname = opname_of_term le_bool_rat_term
let is_le_bool_rat_term = is_dep0_dep0_term le_bool_rat_opname
let mk_le_bool_rat_term = mk_dep0_dep0_term le_bool_rat_opname
let dest_le_bool_rat = dest_dep0_dep0_term le_bool_rat_opname

let ge_bool_rat_term = << ge_bool_rat{'x; 'y} >>
let ge_bool_rat_opname = opname_of_term ge_bool_rat_term
let is_ge_bool_rat_term = is_dep0_dep0_term ge_bool_rat_opname
let mk_ge_bool_rat_term = mk_dep0_dep0_term ge_bool_rat_opname
let dest_ge_bool_rat = dest_dep0_dep0_term ge_bool_rat_opname

let ge_rat_term = << ge_rat{'x; 'y} >>
let ge_rat_opname = opname_of_term ge_rat_term
let is_ge_rat_term = is_dep0_dep0_term ge_rat_opname
let mk_ge_rat_term = mk_dep0_dep0_term ge_rat_opname
let dest_ge_rat = dest_dep0_dep0_term ge_rat_opname

let max_rat_term = << max_rat{'x; 'y} >>
let max_rat_opname = opname_of_term max_rat_term
let is_max_rat_term = is_dep0_dep0_term max_rat_opname
let mk_max_rat_term = mk_dep0_dep0_term max_rat_opname
let dest_max_rat = dest_dep0_dep0_term max_rat_opname

let min_rat_term = << min_rat{'x; 'y} >>
let min_rat_opname = opname_of_term min_rat_term
let is_min_rat_term = is_dep0_dep0_term min_rat_opname
let mk_min_rat_term = mk_dep0_dep0_term min_rat_opname
let dest_min_rat = dest_dep0_dep0_term min_rat_opname

let reduce_lt_bool_rat=((addrC [Subterm 1] unfold_ratn) thenC (addrC [Subterm 2] unfold_ratn) thenC unfold_lt_bool_rat)
let reduce_le_bool_rat = unfold_le_bool_rat thenC (addrC [Subterm 1] reduce_lt_bool_rat)
let reduce_ge_bool_rat = unfold_ge_bool_rat thenC reduce_le_bool_rat
let reduce_ge_rat = unfold_ge_rat thenC unfold_le_rat thenC (addrC [Subterm 1] reduce_le_bool_rat)

let reduce_rat_in_args = (addrC [Subterm 1] (unfold_rat thenC reduceC)) thenC (addrC [Subterm 2] (unfold_rat thenC reduceC))

let resource reduce +=[
	<<mul_rat{ratn{'a; 'b}; ratn{'c; 'd}}>>, wrap_reduce ((addrC [Subterm 1] unfold_ratn) thenC (addrC [Subterm 2] unfold_ratn) thenC unfold_mul_rat);
	<<add_rat{ratn{'a; 'b}; ratn{'c; 'd}}>>, wrap_reduce ((addrC [Subterm 1] unfold_ratn) thenC (addrC [Subterm 2] unfold_ratn) thenC unfold_add_rat);
	<<inv_rat{ratn{'a; 'b}}>>, wrap_reduce ((addrC [Subterm 1] unfold_ratn) thenC unfold_inv_rat);
	<<neg_rat{ratn{'a; 'b}}>>, wrap_reduce ((addrC [Subterm 1] unfold_ratn) thenC unfold_neg_rat);
	<<sub_rat{ratn{'a; 'b}; ratn{'b; 'c}}>>, wrap_reduce unfold_sub_rat;

	<<lt_bool_rat{ratn{'a;'b};ratn{'c;'d}}>>, wrap_reduce reduce_lt_bool_rat;
	<<gt_bool_rat{ratn{'a;'b};ratn{'c;'d}}>>, wrap_reduce unfold_gt_bool_rat;
	<<ge_bool_rat{ratn{'a;'b};ratn{'c;'d}}>>, wrap_reduce reduce_ge_bool_rat;
	<<le_bool_rat{ratn{'a;'b};ratn{'c;'d}}>>, wrap_reduce reduce_le_bool_rat;

	<<lt_rat{ratn{'a;'b};ratn{'c;'d}}>>, wrap_reduce unfold_lt_rat;
	<<gt_rat{ratn{'a;'b};ratn{'c;'d}}>>, wrap_reduce unfold_gt_rat;
	<<ge_rat{ratn{'a;'b};ratn{'c;'d}}>>, wrap_reduce reduce_ge_rat;
	<<le_rat{ratn{'a;'b};ratn{'c;'d}}>>, wrap_reduce unfold_le_rat;

	<<lt_rat{rat{number[i:n];number[j:n]};rat{number[k:n];number[l:n]}}>>, wrap_reduce (reduce_rat_in_args thenC unfold_lt_rat);
	<<gt_rat{rat{number[i:n];number[j:n]};rat{number[k:n];number[l:n]}}>>, wrap_reduce (reduce_rat_in_args thenC unfold_gt_rat);
	<<ge_rat{rat{number[i:n];number[j:n]};rat{number[k:n];number[l:n]}}>>, wrap_reduce (reduce_rat_in_args thenC reduce_ge_rat);
	<<le_rat{rat{number[i:n];number[j:n]};rat{number[k:n];number[l:n]}}>>, wrap_reduce (reduce_rat_in_args thenC unfold_le_rat);
]

dform ratn_df1 : except_mode[src] :: "prec"[prec_mul] :: ratn{'a; 'b}
 =
   `"(" slot{'a} `":" slot{'b} `")"

dform int_ratn_df1 : except_mode[src] :: ratn{'a;1}
 =
   slot{'a} Mpsymbols!subq

dform rat_df1 : except_mode[src] :: "prec"[prec_mul] :: rat{'a; 'b}
 =
   `"(" slot{'a} `"/" slot{'b} `")"

dform zero_rat_df1 : except_mode[src] :: rat{0;'a}
 =
   `"0" Mpsymbols!subq

dform unit_rat_df1 : except_mode[src] :: rat{'a;'a}
 =
   `"1" Mpsymbols!subq

dform int_rat_df1 : except_mode[src] :: rat{'a;1}
 =
   slot{'a} Mpsymbols!subq

dform rat_of_int_df1 : except_mode[src] :: rat_of_int{'a}
 =
   slot{'a} Mpsymbols!subq

dform add_rat_df1 : except_mode[src] :: parens :: "prec"[prec_add] :: add_rat{'a; 'b}
 =
   slot["le"]{'a} `" +" Mpsymbols!subq `" " slot["lt"]{'b}

dform mul_rat_df1 : except_mode[src] :: parens :: "prec"[prec_mul] :: mul_rat{'a; 'b}
 =
   slot["le"]{'a} `" *" Mpsymbols!subq `" " slot["lt"]{'b}

dform sub_rat_df1 : except_mode[src] :: parens :: "prec"[prec_add] :: sub_rat{'a; 'b}
 =
   slot["lt"]{'a} `" -" Mpsymbols!subq `" " slot["le"]{'b}

dform ge_bool_rat_df1 : except_mode[src] :: ge_bool_rat{'a; 'b}
 =
   slot["le"]{'a} `" " Mpsymbols!ge Mpsymbols!subb Mpsymbols!subq `" " slot["lt"]{'b}

dform le_bool_rat_df1 : except_mode[src] :: le_bool_rat{'a; 'b}
 =
   slot["le"]{'a} `" " Mpsymbols!le Mpsymbols!subb Mpsymbols!subq `" " slot["lt"]{'b}

dform gt_bool_rat_df1 : except_mode[src] :: gt_bool_rat{'a; 'b}
 =
   slot["le"]{'a} `" >" Mpsymbols!subb Mpsymbols!subq `" " slot["lt"]{'b}

dform lt_bool_rat_df1 : except_mode[src] :: lt_bool_rat{'a; 'b}
 =
   slot["le"]{'a} `" <" Mpsymbols!subb Mpsymbols!subq `" " slot["lt"]{'b}

dform ge_rat_df1 : except_mode[src] :: ge_rat{'a; 'b}
 =
   slot["le"]{'a} `" " Mpsymbols!ge Mpsymbols!subq `" " slot["lt"]{'b}

dform le_rat_df1 : except_mode[src] :: le_rat{'a; 'b}
 =
   slot["le"]{'a} `" " Mpsymbols!le Mpsymbols!subq `" " slot["lt"]{'b}

dform gt_rat_df1 : except_mode[src] :: gt_rat{'a; 'b}
 =
   slot["le"]{'a} `" >" Mpsymbols!subq `" " slot["lt"]{'b}

dform lt_rat_df1 : except_mode[src] :: lt_rat{'a; 'b}
 =
   slot["le"]{'a} `" <" Mpsymbols!subq `" " slot["lt"]{'b}

interactive int0_mem {| intro [] |} :
	[wf] sequent { <H> >- 'x in int } -->
	sequent { <H> >- 'x<>0 } -->
	sequent { <H> >- 'x in int0 }

interactive int0_int {| nth_hyp |} 'H :
	sequent { <H>; x: int0; <J['x]> >- 'x in int }

interactive mul_int0 {| intro [] |} :
	sequent { <H> >- 'x in int0 } -->
	sequent { <H> >- 'y in int0 } -->
	sequent { <H> >- ('x *@ 'y) in int0 }

interactive is_normed_type {| intro [] |} :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H> >- is_normed{'a; 'b} Type }

interactive denominator_int0 'x :
	[wf] sequent { <H> >- 'x in int } -->
	[wf] sequent { <H> >- 'y in int } -->
	sequent { <H> >- is_normed{'x; 'y} } -->
	sequent { <H> >- 'y in int0 }

interactive is_normed_sqstable {| squash |} :
	sequent { <H> >- squash{is_normed{'a; 'b}} } -->
	sequent { <H> >- is_normed{'a; 'b} }

interactive rationalsType {| intro [] |} :
   sequent { <H> >- "type"{rationals} }

interactive rationalsUniv {| intro [] |} :
   sequent { <H> >- rationals in univ[i:l] }

interactive rationalsElimination {| elim [] |} 'H :
   sequent { <H>; x: int; y: int0; is_normed{'x; 'y}; <J[ratn{'x; 'y}]> >- 'C[ratn{'x; 'y}] } -->
   sequent { <H>; a: rationals; <J['a]> >- 'C['a] }

interactive rat_wf {| intro [] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int0 } -->
	sequent { <H> >- rat{'a; 'b} in rationals }

interactive ratEquality {| intro [] |} :
	sequent { <H> >- 'a *@ 'd = 'b *@ 'c in int } -->
	[wf] sequent { <H> >- rat{'a; 'b} in rationals } -->
	[wf] sequent { <H> >- rat{'c; 'd} in rationals } -->
	sequent { <H> >- rat{'a; 'b} ~ rat{'c; 'd} }

interactive mul_rat_wf {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- mul_rat{'a; 'b} in rationals }

interactive add_rat_wf {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- add_rat{'a; 'b} in rationals }

interactive neg_rat_wf {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- neg_rat{'a} in rationals }

interactive inv_rat_wf {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- neq_rat{'a; rat{0;1}} } -->
	sequent { <H> >- inv_rat{'a} in rationals }

interactive sub_rat_wf {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- sub_rat{'a; 'b} in rationals }

interactive_rw reduce_multiplier_rw :
	('k in int0) -->
	('a in int) -->
	('b in int0) -->
	rat{'k *@ 'a; 'k *@ 'b} <--> rat{'a; 'b}

let reduce_multiplierC = reduce_multiplier_rw

interactive_rw inject_multiplier_rw 'k :
	('k in int0) -->
	('a in int) -->
	('b in int0) -->
	rat{'a; 'b} <--> rat{'k *@ 'a; 'k *@ 'b}

let inject_multiplierC = inject_multiplier_rw

interactive_rw ratn2rat_rw :
	('a in int) -->
	('b in int) -->
	(is_normed{'a; 'b}) -->
	ratn{'a; 'b} <--> rat{'a; 'b}

let ratn2ratC = ratn2rat_rw

interactive_rw reduce_mul_rat {| reduce |} :
	('a in int) -->
	('b in int0) -->
	('c in int) -->
	('d in int0) -->
	mul_rat{rat{'a; 'b}; rat{'c; 'd}} <-->
	rat{'a *@ 'c; 'b *@ 'd}

interactive_rw reduce_add_rat {| reduce |} :
	('a in int) -->
	('b in int0) -->
	('c in int) -->
	('d in int0) -->
	add_rat{rat{'a; 'b}; rat{'c; 'd}} <-->
	rat{('a *@ 'd) +@ ('b *@ 'c); 'b *@ 'd}

let resource reduce += [
	<<mul_rat{ratn{'a; 'b}; rat{'c; 'd}}>>, wrap_reduce ((addrC [Subterm 1] ratn2ratC) thenC reduce_mul_rat);
	<<mul_rat{rat{'a; 'b}; ratn{'c; 'd}}>>, wrap_reduce ((addrC [Subterm 2] ratn2ratC) thenC reduce_mul_rat);
	<<add_rat{ratn{'a; 'b}; rat{'c; 'd}}>>, wrap_reduce ((addrC [Subterm 1] ratn2ratC) thenC reduce_add_rat);
	<<add_rat{rat{'a; 'b}; ratn{'c; 'd}}>>, wrap_reduce ((addrC [Subterm 2] ratn2ratC) thenC reduce_add_rat);
]

interactive_rw reduce_inv_rat {| reduce |} :
	('a in int0) -->
	('b in int0) -->
	inv_rat{rat{'a; 'b}} <-->
	rat{'b; 'a}

interactive_rw reduce_neg_rat {| reduce |} :
	('a in int) -->
	('b in int0) -->
	neg_rat{rat{'a; 'b}} <-->
	rat{- 'a; 'b}

interactive_rw reduce_sub_rat {| reduce |} :
	('a in int) -->
	('b in int0) -->
	('c in int) -->
	('d in int0) -->
	sub_rat{rat{'a; 'b}; rat{'c; 'd}} <-->
	rat{('a *@ 'd) -@ ('b *@ 'c); 'b *@ 'd}

interactive add_rat_Commut :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent { <H> >- add_rat{'a; 'b} ~ add_rat{'b; 'a} }

interactive_rw add_rat_Commut_rw :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   add_rat{'a; 'b} <--> add_rat{'b; 'a}

let add_rat_CommutC = add_rat_Commut_rw

interactive add_rat_Assoc :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [wf] sequent { <H> >- 'c in rationals } -->
   sequent { <H> >- add_rat{'a; add_rat{'b; 'c}} ~ add_rat{add_rat{'a; 'b}; 'c} }

interactive_rw add_rat_Assoc_rw :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   ( 'c in rationals ) -->
   add_rat{'a; add_rat{'b; 'c}} <--> add_rat{add_rat{'a; 'b}; 'c}

let add_rat_AssocC = add_rat_Assoc_rw

interactive_rw add_rat_Assoc2_rw {| reduce |} :
   ( 'a in rationals ) -->
   ( 'b in rationals ) -->
   ( 'c in rationals ) -->
   add_rat{add_rat{'a; 'b}; 'c} <--> add_rat{'a; add_rat{'b; 'c}}

let add_rat_Assoc2C = add_rat_Assoc2_rw

doc <:doc<
   <<rat{0; 1}>> is neutral element for <<add_rat{cdot;cdot}>> in <<rationals>>.
>>

interactive add_rat_Id {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in rationals } -->
   sequent { <H> >- add_rat{'a; rat{0; 1}} ~ 'a }

interactive_rw add_rat_Id_rw {| reduce; arith_unfold |} :
   ( 'a in rationals ) -->
   add_rat{'a; rat{0; 1}} <--> 'a

let add_rat_IdC = add_rat_Id_rw

interactive_rw add_rat_Id2_rw {| reduce; arith_unfold |} :
   ( 'a in rationals ) -->
   add_rat{rat{0; 1}; 'a} <--> 'a

let add_rat_Id2C = add_rat_Id2_rw

let resource reduce += [
	<<sub_rat{'a; rat{0; 1}}>>, wrap_reduce (unfold_sub_rat thenC (addrC [Subterm 2] reduce_sub_rat));
]

interactive_rw add_rat_Id3_rw ('a :> Term) :
   ( 'a in rationals ) -->
   'a <--> add_rat{rat{0; 1}; 'a}

(* unused
let add_rat_Id3C = termC add_rat_Id3_rw
 *)

interactive_rw add_rat_Id4_rw ('a :> Term) :
   ( 'a in rationals ) -->
   'a <--> add_rat{'a; rat{0; 1}}

(* unused
let add_rat_Id4C = termC add_rat_Id4_rw
 *)

interactive mul_rat_Commut :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   sequent { <H> >- mul_rat{'a; 'b} ~ mul_rat{'b; 'a} }

interactive_rw mul_rat_Commut_rw :
   ('a in rationals) -->
   ('b in rationals) -->
   mul_rat{'a; 'b} <--> mul_rat{'b; 'a}

let mul_rat_CommutC = mul_rat_Commut_rw

interactive mul_rat_Assoc :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [wf] sequent { <H> >- 'c in rationals } -->
   sequent { <H> >- mul_rat{'a; mul_rat{'b; 'c}} ~ mul_rat{mul_rat{'a; 'b}; 'c} }

interactive_rw mul_rat_Assoc_rw :
   ('a in rationals) -->
   ('b in rationals) -->
   ('c in rationals) -->
   mul_rat{'a; mul_rat{'b; 'c}} <--> mul_rat{mul_rat{'a; 'b}; 'c}

let mul_rat_AssocC = mul_rat_Assoc_rw

interactive_rw mul_rat_Assoc2_rw {| reduce |} :
   ('a in rationals) -->
   ('b in rationals) -->
   ('c in rationals) -->
   mul_rat{mul_rat{'a; 'b}; 'c} <--> mul_rat{'a; mul_rat{'b; 'c}}

let mul_rat_Assoc2C = mul_rat_Assoc2_rw

interactive mul_rat_add_Distrib :
   [wf] sequent { <H> >- 'a in rationals } -->
   [wf] sequent { <H> >- 'b in rationals } -->
   [wf] sequent { <H> >- 'c in rationals } -->
   sequent { <H> >- mul_rat{'a; add_rat{'b; 'c}} ~ add_rat{mul_rat{'a; 'b}; mul_rat{'a; 'c}} }

interactive_rw mul_rat_add_Distrib_rw {| arith_unfold |} :
   ('a in rationals) -->
   ('b in rationals) -->
   ('c in rationals) -->
   mul_rat{'a; add_rat{'b; 'c}} <--> add_rat{mul_rat{'a; 'b}; mul_rat{'a; 'c}}

let mul_rat_add_DistribC = mul_rat_add_Distrib_rw

interactive_rw mul_rat_add_Distrib2C :
   ('a in rationals) -->
   ('b in rationals) -->
   ('c in rationals) -->
   add_rat{mul_rat{'a; 'b}; mul_rat{'a; 'c}} <--> mul_rat{'a; add_rat{'b; 'c}}

interactive_rw mul_rat_add_Distrib3C {| arith_unfold |} :
   ('a in rationals) -->
   ('b in rationals) -->
   ('c in rationals) -->
   mul_rat{add_rat{'a; 'b}; 'c} <--> add_rat{mul_rat{'a; 'c}; mul_rat{'b; 'c}}

interactive mul_rat_Id {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in rationals } -->
   sequent { <H> >- mul_rat{rat{1; 1}; 'a} ~ 'a }

interactive_rw mul_rat_Id_rw {| reduce |} :
   ('a in rationals) -->
   mul_rat{rat{1; 1}; 'a} <--> 'a

let mul_rat_IdC = mul_rat_Id_rw

interactive mul_rat_Id2 {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in rationals } -->
   sequent { <H> >- mul_rat{'a; rat{1; 1}} ~ 'a }

interactive_rw mul_rat_Id2_rw {| reduce |} :
   ('a in rationals) -->
   mul_rat{'a; rat{1; 1}} <--> 'a

let mul_rat_Id2C = mul_rat_Id2_rw

interactive mul_rat_Id3 {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in rationals } -->
   sequent { <H> >- 'a ~ mul_rat{rat{1; 1}; 'a} }

interactive_rw mul_rat_Id3_rw ('a :> Term) :
   ('a in rationals) -->
   'a <--> mul_rat{rat{1; 1}; 'a}

(* unused
let mul_rat_Id3C = termC mul_rat_Id3_rw
 *)

interactive mul_rat_Zero {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in rationals } -->
   sequent { <H> >- mul_rat{rat{0; 'd}; 'a} ~ rat{0; 1} }

interactive_rw mul_rat_Zero_rw {| reduce |} :
   ('a in rationals) -->
   mul_rat{rat{0; 'd}; 'a} <--> rat{0; 1}

(* unused
let mul_rat_ZeroC = mul_rat_Zero_rw
 *)

interactive mul_rat_Zero2 {| nth_hyp |} :
   [wf] sequent { <H> >- 'a in rationals } -->
   sequent { <H> >- mul_rat{'a; rat{0; 'd}} ~ rat{0; 1} }

interactive_rw mul_rat_Zero2_rw {| reduce |} :
   ('a in rationals) -->
   mul_rat{'a; rat{0; 'd}} <--> rat{0; 1}

(* unused
let mul_rat_Zero2C = mul_rat_Zero2_rw
 *)

interactive_rw mul_rat_Zero3C 'a :
   ('a in rationals) -->
   rat{0; 'd} <--> mul_rat{rat{0; 1}; 'a}

interactive_rw negative1_2uni_ratC :
	('a in rationals) -->
	mul_rat{ratn{-1; 1}; 'a} <--> neg_rat{'a}

interactive_rw uni2negative1_ratC {| arith_unfold |} :
	('a in rationals) -->
	neg_rat{'a} <--> mul_rat{rat{-1; 1}; 'a}

doc docoff

let debug_int2rat =
   create_debug (**)
      { debug_name = "int2rat";
        debug_description = "display int-to-rat conversion";
        debug_value = false
      }

let extract_data tbl =
   let rw t =
      (* Find and apply the right tactic *)
      if !debug_int2rat then
         eprintf "int2rat: lookup %a%t" debug_print t eflush;
      match Term_match_table.lookup tbl select_all t with
         Some conv ->
            if !debug_int2rat then
               eprintf "int2rat: applying %a%t" debug_print t eflush;
            conv
       | None ->
            raise (RefineError ("int2rat.extract_data", StringTermError ("no reduction for", t)))
   in
      termC rw

let process_int2rat_resource_rw_annotation = redex_and_conv_of_rw_annotation "int2rat"

(*
 * Resource.
 *)
let resource (term * conv, conv) int2rat =
   table_resource_info extract_data

let int2ratTopC_env e =
   get_resource_arg (env_arg e) get_int2rat_resource

let int2ratTopC = funC int2ratTopC_env

let int2ratC =
   repeatC (higherC int2ratTopC)

let int2ratT =
   rwAll int2ratC

doc docon

interactive_rw rat_of_int_ratn :
	('a in int) -->
	rat_of_int{'a} <--> ratn{'a; 1}

let rat_of_int_ratnC = rat_of_int_ratn

interactive ratn_number_wf {| intro [] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- ratn{'a; 1} in rationals }

let resource int2rat += [
	<<'a -@ 'b>>, sub_elim_rw;
	<<- 'a>>, (uni2negative1C thenC (addrC [Subterm 1] reduce_minus));
]

interactive_rw rat_of_int_add {| int2rat |} :
	('a in int) -->
	('b in int) -->
	rat_of_int{'a +@ 'b} <--> add_rat{rat_of_int{'a}; rat_of_int{'b}}

interactive_rw rat_of_int_mul {| int2rat |} :
	('a in int) -->
	('b in int) -->
	rat_of_int{'a *@ 'b} <--> mul_rat{rat_of_int{'a}; rat_of_int{'b}}

interactive_rw rat_of_int_lt_bool {| int2rat |} :
	('a in int) -->
	('b in int) -->
	('a <@ 'b) <--> lt_bool_rat{rat_of_int{'a}; rat_of_int{'b}}

interactive_rw rat_of_int_gt_bool {| int2rat |} :
	('a in int) -->
	('b in int) -->
	('a >@ 'b) <--> gt_bool_rat{rat_of_int{'a}; rat_of_int{'b}}

interactive_rw rat_of_int_le_bool {| int2rat |} :
	('a in int) -->
	('b in int) -->
	('a <=@ 'b) <--> le_bool_rat{rat_of_int{'a}; rat_of_int{'b}}

interactive_rw rat_of_int_ge_bool {| int2rat |} :
	('a in int) -->
	('b in int) -->
	('a >=@ 'b) <--> ge_bool_rat{rat_of_int{'a}; rat_of_int{'b}}

interactive_rw rat_of_int_bneq {| int2rat |} :
	('a in int) -->
	('b in int) -->
	('a <>@ 'b) <--> bneq_rat{rat_of_int{'a}; rat_of_int{'b}}

interactive_rw rat_of_int_lt {| int2rat |} :
	('a in int) -->
	('b in int) -->
	('a < 'b) <--> lt_rat{rat_of_int{'a}; rat_of_int{'b}}

interactive_rw rat_of_int_gt {| int2rat |} :
	('a in int) -->
	('b in int) -->
	('a > 'b) <--> gt_rat{rat_of_int{'a}; rat_of_int{'b}}

interactive_rw rat_of_int_le {| int2rat |} :
	('a in int) -->
	('b in int) -->
	('a <= 'b) <--> le_rat{rat_of_int{'a}; rat_of_int{'b}}

interactive_rw rat_of_int_ge {| int2rat |} :
	('a in int) -->
	('b in int) -->
	('a >= 'b) <--> ge_rat{rat_of_int{'a}; rat_of_int{'b}}

interactive_rw rat_of_int_neq {| int2rat |} :
	('a in int) -->
	('b in int) -->
	('a <> 'b) <--> neq_rat{rat_of_int{'a}; rat_of_int{'b}}

interactive lt_bool_rat_wf1 {| intro [] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H> >- 'd in int } -->
	sequent { <H> >- lt_bool_rat{rat{'a;'b}; rat{'c;'d}} in bool }

interactive lt_bool_rat_wf2 {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H> >- lt_bool_rat{'a; rat{'b;'c}} in bool }

interactive lt_bool_rat_wf3 {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- lt_bool_rat{rat{'a;'b}; 'c} in bool }

interactive lt_bool_rat_wf {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- lt_bool_rat{'a; 'b} in bool }

interactive le_bool_rat_wf1 {| intro [] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H> >- 'd in int } -->
	sequent { <H> >- le_bool_rat{rat{'a;'b}; rat{'c;'d}} in bool }

interactive le_bool_rat_wf2 {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H> >- le_bool_rat{'a; rat{'b;'c}} in bool }

interactive le_bool_rat_wf3 {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- le_bool_rat{rat{'a;'b}; 'c} in bool }

interactive le_bool_rat_wf {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- le_bool_rat{'a; 'b} in bool }

interactive beq_rat_wf1 {| intro [] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H> >- 'd in int } -->
	sequent { <H> >- beq_rat{rat{'a;'b}; rat{'c;'d}} in bool }

interactive beq_rat_wf2 {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H> >- beq_rat{'a; rat{'b;'c}} in bool }

interactive beq_rat_wf3 {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- beq_rat{rat{'a;'b}; 'c} in bool }

interactive beq_rat_wf {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- beq_rat{'a; 'b} in bool }

interactive min_rat_wf {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- min_rat{'a;'b} in rationals }

interactive max_rat_wf {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- max_rat{'a;'b} in rationals }

interactive max_self1 {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- ge_rat{max_rat{'a;'b};'a} }

interactive max_self2 {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- ge_rat{max_rat{'a;'b};'b} }

interactive min_self1 {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- ge_rat{'a;min_rat{'a;'b}} }

interactive min_self2 {| intro [] |} :
	sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- ge_rat{'b;min_rat{'a;'b}} }

interactive rat_of_intEquality {| intro [] |} :
	sequent { <H> >- 'a = 'b in int } -->
	sequent { <H> >- rat_of_int{'a}=rat_of_int{'b} in rationals }

interactive rat_of_intEquality2 :
	sequent { <H> >- rat_of_int{'a}=rat_of_int{'b} in rationals } -->
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'a = 'b in int }

interactive rat_of_intLess {| intro [] |} :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'a < 'b } -->
	sequent { <H> >- "assert"{lt_bool_rat{rat_of_int{'a}; rat_of_int{'b}}} }

interactive rat_of_intLess2 :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H> >- "assert"{lt_bool_rat{rat_of_int{'a}; rat_of_int{'b}}} } -->
	sequent { <H> >- 'a < 'b }

interactive rat_of_intLE {| intro [] |} :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'a <= 'b } -->
	sequent { <H> >- "assert"{le_bool_rat{rat_of_int{'a}; rat_of_int{'b}}} }

interactive rat_of_intLE2 :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	sequent { <H> >- "assert"{le_bool_rat{rat_of_int{'a}; rat_of_int{'b}}} } -->
	sequent { <H> >- 'a <= 'b }

interactive lt_le_rat :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- strict2unstrict{lt_bool_rat{'a;'b}} = le_bool_rat{'a;'b} in bool }

interactive q_is_field {| intro [] |} :
	sequent { <H> >- fieldQ in field[i:l] }

interactive lt_bool_ratStrictTotalOrder :
	sequent { <H> >- isStrictTotalOrder{rationals; lambda{x.lambda{y.lt_bool_rat{'x;'y}}}} }

interactive le_bool_ratUnstrictTotalOrder :
	sequent { <H> >- isUnstrictTotalOrder{rationals; lambda{x.lambda{y.le_bool_rat{'x;'y}}}} }

interactive ge_bool_ratUnstrictTotalOrder :
	sequent { <H> >- isUnstrictTotalOrder{rationals; lambda{x.lambda{y.ge_bool_rat{'x;'y}}}} }

interactive geReflexive {| intro [] |} :
	[wf] sequent { <H> >- 'a in rationals } -->
	sequent { <H> >- ge_rat{'a; 'a} }

interactive geTransitive 'b :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- ge_rat{'b; 'c} } -->
	sequent { <H> >- ge_rat{'a; 'b} } -->
	sequent { <H> >- ge_rat{'a; 'c} }

interactive ge_minLeftIntro :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- ge_rat{'a; 'c} } -->
	sequent { <H> >- ge_rat{'b; 'c} } -->
	sequent { <H> >- ge_rat{min_rat{'a;'b}; 'c} }

interactive ge_maxRightIntro :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- ge_rat{'a; 'b} } -->
	sequent { <H> >- ge_rat{'a; 'c} } -->
	sequent { <H> >- ge_rat{'a;max_rat{'b;'c}} }

interactive ge_minLeftElim {| elim [] |} 'H :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H>; ge_rat{'a; 'c}; ge_rat{'b; 'c}; <J> >- 'C } -->
	sequent { <H>; ge_rat{min_rat{'a;'b}; 'c}; <J> >- 'C }

interactive ge_maxRightElim {| elim [] |} 'H :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H>; ge_rat{'a;'b}; ge_rat{'a;'c}; <J> >- 'C } -->
	sequent { <H>; ge_rat{'a;max_rat{'b;'c}}; <J> >- 'C }

interactive max_ge_maxIntro :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	[wf] sequent { <H> >- 'd in rationals } -->
	sequent { <H> >- ge_rat{'a;'b} } -->
	sequent { <H> >- ge_rat{'c;'d} } -->
	sequent { <H> >- ge_rat{max_rat{'a;'c};max_rat{'b;'d}} }

interactive min_ge_minIntro :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	[wf] sequent { <H> >- 'd in rationals } -->
	sequent { <H> >- ge_rat{'a;'b} } -->
	sequent { <H> >- ge_rat{'c;'d} } -->
	sequent { <H> >- ge_rat{min_rat{'a;'c};min_rat{'b;'d}} }

interactive max_ge_minIntro {| intro [] |} :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	sequent { <H> >- ge_rat{max_rat{'a;'b};min_rat{'a;'b}} }

interactive ge_addMono 'c :
	[wf] sequent { <H> >- 'a in rationals } -->
	[wf] sequent { <H> >- 'b in rationals } -->
	[wf] sequent { <H> >- 'c in rationals } -->
	sequent { <H> >- ge_rat{add_rat{'a;'c};add_rat{'b;'c}} } -->
	sequent { <H> >- ge_rat{'a;'b} }

interactive ge_addMonoElim 'H 'c :
	[wf] sequent { <H>; w: ge_rat{'a;'b}; <J['w]> >- 'a in rationals } -->
	[wf] sequent { <H>; w: ge_rat{'a;'b}; <J['w]> >- 'b in rationals } -->
	[wf] sequent { <H>; w: ge_rat{'a;'b}; <J['w]> >- 'c in rationals } -->
	sequent { <H>; w: ge_rat{'a;'b}; <J['w]>; ge_rat{add_rat{'a;'c};add_rat{'b;'c}} >- 'C['w] } -->
	sequent { <H>; w: ge_rat{'a;'b}; <J['w]> >- 'C['w] }
doc docoff
