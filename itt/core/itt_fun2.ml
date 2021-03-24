doc <:doc<
   @module[Itt_dfun]

   The @tt[Itt_dfun] module defines the type <<x:'A -> 'B['x]>> of
   dependent functions.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1997-2006 MetaPRL Group, Cornell University and Caltech

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
   @end[license]
>>
doc <:doc<
   @parents
>>
extends Itt_dfun
extends Itt_nat
doc docoff

open Basic_tactics

doc <:doc<
   @modsection{Compose}
>>
define unfold_compose : compose{'f;'g} <--> lambda{x.'f ('g 'x)}

dform funexp_df : except_mode[src] :: compose{'f;'g} =
   slot{'f} space circ space slot{'g}

interactive_rw reduce_compose {| reduce |}:  (compose{'f;'g} 'x) <--> ('f ('g 'x))

interactive compose_wf3  {| intro [] |}:
   sequent { <H> >- compose{'f;'g} in void -> 'C }

interactive compose_wf  {| intro [intro_typeinf <<'g>>] |} (x:'A -> 'B['x]) :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- 'g in (x:'A -> 'B['x]) } -->
   sequent { <H>; x:'A >- 'f in 'B['x] -> 'C['x] } -->
   sequent { <H> >- compose{'f;'g} in x:'A -> 'C['x] }

interactive compose_wf2 {| intro [intro_typeinf <<'g>>] |} ('A -> 'B):
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- 'g in 'A -> 'B } -->
   sequent { <H>; x:'A >- 'f in 'B -> 'C } -->
   sequent { <H> >- compose{'f;'g} in 'A -> 'C }

interactive comp_assoc {|  intro [intro_typeinf <<'g>>] |} ('"B"->'"C")  :
   [wf] sequent { <H> >- "type"{'"A"} }  -->
   [wf] sequent { <H> >- "type"{'"B"} }  -->
   [wf] sequent { <H> >- "type"{'"C"} }  -->
   [wf] sequent { <H> >- "type"{'"D"} }  -->
   [wf] sequent { <H> >- '"f" in ('A -> 'B) }  -->
   [wf] sequent { <H> >- '"g" in ('B -> 'C) }  -->
   [wf] sequent { <H> >- '"h" in ('C -> 'D) }  -->
   sequent { <H> >- "equal"{('A -> 'D);"compose"{'"h";"compose"{'"g";'"f"}};"compose"{"compose"{'"h";'"g"};'"f"}} }

doc <:doc<
   @modsection{Identity}
>>
define unfold_id: id <--> lambda{x.'x}

interactive_rw id_reduce {| reduce |}: id 'x <--> 'x

interactive id_wf  {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- id in 'A -> 'A }

interactive comp_id_l {| intro [] |}:
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- 'f in 'A -> 'B } -->
   sequent { <H> >- compose{id;'f} in 'A -> 'B }

interactive comp_id_r {| intro [] |}:
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- 'f in 'A -> 'B } -->
   sequent { <H> >- compose{'f;id} in 'A -> 'B }

doc <:doc<
   @modsection{Function exponential}
>>

define unfold_funexp :  fun_exp{'f;'n} <--> ind{'n;id; "_" ,F.compose{'F;'f}}

dform funexp_df : except_mode[src] :: fun_exp{'f;'n} = slot{'f} sup{'n}

interactive_rw funexp_reduce_base {| reduce |} :
   fun_exp{'f;0} <--> id

interactive_rw funexp_reduce_step {| reduce |} :
   ('n in nat) -->
   fun_exp{'f;'n +@ 1} <--> compose{fun_exp{'f;'n};'f}

interactive funexp_wf {| intro[] |}:
   sequent{ <H> >- 'T Type } -->
   sequent{ <H> >- 'f in 'T -> 'T } -->
   sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- fun_exp{'f;'n} in 'T -> 'T }
