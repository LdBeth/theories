doc <:doc<
   @module[Itt_per]

   Define types based on PER semantics.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2002-2004 MetaPRL Group

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

   Author: LdBeth @email{ldbeth@sdf.org}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_logic
extends Itt_bisect
extends Itt_quotient
extends Itt_ext_equal

declare per{x, y. 'R['x;'y]}

prim perEquality 'x 'y 'z :
   [wf] sequent{ <H> >- 'R1['x;'y] Type } -->
   [wf] sequent{ <H> >- 'R2['x;'y] Type } -->
   sequent{ <H>; 'R1['x;'y] >- 'R2['x;'y] } -->
   sequent{ <H>; 'R2['x;'y] >- 'R1['x;'y] } -->
   sequent{ <H>; 'R1['x;'y]; 'R1['y;'z] >- 'R1['x;'z] } -->
   sequent{ <H> >- per{x, y. 'R1['x;'y]} = per{x, y. 'R2['x;'y]} in univ[i:l] }
   = it

prim perMemberEquality :
   [wf] sequent{ <H> >- per{x, y. 'R['x;'y]} Type } -->
   sequent{ <H> >- 'R['t1;'t2] } -->
   sequent{ <H> >- 't1 = 't2 in per{x, y. 'R['x;'y]} }
   = it

prim perUnsquash 'H :
   [wf] sequent{ <H>; 't1 = 't2 in per{x, y. 'R['x;'y]}; <J> >- 'R['t1;'t2] Type } -->
   sequent{ <H>; 't1 = 't2 in per{x, y. 'R['x;'y]}; <J> >- squash{'R['t1;'t2]} } = it

interactive perElimination 'H :
   [wf] sequent{ <H>; 't1 = 't2 in per{x, y. 'R['x;'y]}; <J> >- 'R['t1;'t2] Type } -->
   sequent{ <H>; 't1 = 't2 in per{x, y. 'R['x;'y]}; squash{'R['t1;'t2]}; <J> >- 'C } -->
   sequent{ <H>; 't1 = 't2 in per{x, y. 'R['x;'y]}; <J> >- 'C }

doc docoff
