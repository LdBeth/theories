doc <:doc<
   @module[Itt_base]

   The @tt{Itt_base} module defines the type of all closed terms,
   with squiggle equality <<'t ~ 's>> as its equality.

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2020 LdBeth

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
extends Itt_equal
extends Itt_squiggle
doc docoff
(*
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
*)

open Dtactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< @terms >>
declare const base
doc docoff

(*
let base_term = << base >>
let base_opname = opname_of_term base_term
let is_base_term = is_no_subterms_term base_opname *)

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform base_df1 : except_mode[src] :: base = `"Base"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules

   @modsubsection{Equality and typehood}

   The <<base>> type is a member of every universe, and it
   is a type.

>>
prim baseEquality {| intro [] |} :
   sequent { <H> >- base in univ[i:l] } =
   it

(*
 * Typehood.
 *)
interactive baseType {| intro [] |} :
   sequent { <H> >- "type"{base} }

doc docoff

(*
 * H >- Ui ext Base
 * by baseFormation
 *)
interactive baseFormation :
   sequent { <H> >- univ[i:l] }

prim sqequalBase :
   sequent { <H> >- 'a = 'b in base } -->
   sequent { <H> >- 'a ~ 'b } =
   it

prim closedBase :
   sequent { <H> >- 'a<||> in base } =
   it

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
