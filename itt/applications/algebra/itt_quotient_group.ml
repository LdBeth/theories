doc <:doc<
   @module[Itt_quotient_group]

   This theory defines quotient groups.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2003-2006 MetaPRL Group, California Institute of Technology

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

   Author: Xin Yu @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @parents >>
extends Itt_group
extends Itt_quotient
extends Itt_subset
extends Itt_subset2
extends Itt_labels
doc docoff

open Basic_tactics

(************************************************************************
 * QUOTIENT GROUP                                                       *
 ************************************************************************)

doc <:doc<
   @modsection{Rewrites}

   The quotient group of $A$ in $B$, or the Factor Group of $B$ relative to $A$.
>>
define unfold_quotGroup : quotGroup{'A; 'B} <-->
   {car=quot x, y: 'B^car // ('x *['B] ('B^inv 'y) in 'A^car subset 'B^car); "*"='B^"*"; "1"='B^"1"; inv='B^inv}

doc docoff

let resource typeinf += (<<quotGroup{'A; 'B}>>, Typeinf.infer_map (fun t -> fst(two_subterms t)))

let fold_quotGroup = makeFoldC << quotGroup{'A; 'B} >> unfold_quotGroup

(************************************************************************
 * REDUCTIONS                                                           *
 ************************************************************************)

interactive_rw reduce_quotGroup_car {| reduce |} :
   (quotGroup{'A; 'B}^car) <--> (quot x, y: 'B^car // ('x *['B] ('B^inv 'y) in 'A^car subset 'B^car))

interactive_rw reduce_quotGroup_op {| reduce |} :
   (quotGroup{'A; 'B}^"*") <--> ('B^"*")

interactive_rw reduce_quotGroup_inv {| reduce |} :
   (quotGroup{'A; 'B}^inv) <--> ('B^inv)

interactive_rw reduce_quotGroup_id {| reduce |} :
   (quotGroup{'A; 'B}^"1") <--> ('B^"1")

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

interactive quotG_equiv_type {| intro [intro_typeinf <<'B>>] |} group[i:l] :
   sequent { <H> >- subgroup[i:l]{'A; 'B} } -->
   sequent { <H> >- "type"{quot x, y: 'B^car // ('x *['B] ('B^inv 'y) in 'A^car subset 'B^car)} }

interactive quotG_equiv_type2 {| intro [intro_typeinf <<'B>>] |} group[i:l] :
   sequent { <H> >- subgroup[i:l]{'A; 'B} } -->
   sequent { <H> >- "type"{(quotGroup{'A; 'B}^car)} }

doc <:doc<
   @modsection{Rules}

   Introduction
>>
interactive quotGroup_intro {| intro []; nth_hyp |} :
   sequent { <H> >- normalSubg[i:l]{'A; 'B} } -->
   sequent { <H> >- quotGroup{'A; 'B} in group[i:l] }

doc <:doc<

   If <<normalSubg[i:l]{'A; 'B}>> and $B$ is abelian, then <<quotGroup{'A; 'B}>> is abelian.
>>
interactive quotGroup_abel {| intro [AutoMustComplete] |} :
   sequent { <H> >- normalSubg[i:l]{'A; 'B} } -->
   sequent { <H> >- isCommutative{'B} } -->
   sequent { <H> >- quotGroup{'A; 'B} in abelg[i:l] }

doc <:doc<

   If <<normalSubg[i:l]{'A; 'B}>>, then $f: ('B -> <<quotGroup{'A; 'B}>>)$ defined by $f a = a$ is an epimorphism of $B$ to <<quotGroup{'A; 'B}>> with kernel $A$.
>>
interactive quotGroup_hom {| intro [intro_typeinf <<'B>>] |} group[i:l] :
   sequent { <H> >- normalSubg[i:l]{'A; 'B} } -->
   sequent { <H> >- lambda{a. 'a} in groupHom{'B; quotGroup{'A; 'B}} }

interactive quotGroup_epi {| intro [intro_typeinf <<'B>>] |} group[i:l] :
   sequent { <H> >- normalSubg[i:l]{'A; 'B} } -->
   sequent { <H> >- lambda{a. 'a} in groupEpi{'B; quotGroup{'A; 'B}} }

interactive quotGroup_ker_ext {| intro [intro_typeinf <<'B>>] |} group[i:l] :
   sequent { <H> >- normalSubg[i:l]{'A; 'B} } -->
   sequent { <H> >- groupExtEqual{groupKer{lambda{a. 'a}; 'B; quotGroup{'A; 'B}}; {car='A^car; "*"='A^"*"; "1"='A^"1"; inv='A^inv}} }

doc <:doc<

   First Isomorphism Theorem for Groups. Let $f$ be a group epimorphism
   from $B$ to $A$ and let $K$ be the kernel of $f$. Then $A$ is isomorphism
   to the quotient group <<quotGroup{'K; 'B}>>.
>>
interactive quotGroup_iso {| intro [AutoMustComplete; intro_typeinf <<'B>>] |} group[i:l] :
   [wf] sequent { <H> >- 'A in group[i:l] } -->
   [wf] sequent { <H> >- 'B in group[i:l] } -->
   [wf] sequent { <H> >- 'f in groupEpi{'A; 'B} } -->
   sequent { <H> >- lambda{a. ('f 'a)} in groupIso{quotGroup{groupKer{'f; 'A; 'B}; 'A}; 'B} }

doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform quotGroup_df1 : except_mode[src] :: parens :: quotGroup{'A; 'B} =
   slot{'B} `" // " slot{'A}

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
