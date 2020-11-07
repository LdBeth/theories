(*
 * Valid signatures.
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
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
extends Base_theory

(* open Basic_tactics *)

declare mem{'a; 'b}
declare "type"

declare default_extract

dform type_df : "type" = bf["Type"]
dform mem_df : mem{'a; 'b} = slot{'a} `": " slot{'b}

dform default_extrat_df : default_extract = cdot

(*
 * Valid signatures.
 *)
prim s_type_kind :
   sequent { >- "type" }

prim s_k_var :
   sequent { <H> >- 'K } -->
   sequent { <H>; x: 'K >- "type" }

prim s_t_var :
   sequent { <H> >- mem{'A; "type"} } -->
   sequent { <H>; x: 'A >- "type" }

declare dfun{'A; x. 'K['x]}
declare lambda{'A; x. 'B['x]}

dform pi_df : dfun{'A; x. 'K} =
   Pi bvar{'x} ":" slot{'A} "." slot{'K}
dform lambda_df : lambda{'a; x. 'b} = Mpsymbols!lambda slot{'x} `":" slot {'a} `"." slot{'b}

prim s_pi_kind :
   sequent { <H> >- mem{'A; "type"} } -->
   sequent { <H>; x: 'A >- 'K['x] } -->
   sequent { <H> >- dfun{'A; x. 'K['x]} }

prim s_var_fam :
   sequent { <H>; x: 'K >- "type" } -->
   sequent { <H>; x: 'K >- mem{'x; 'K} }

prim s_pi_fam :
   sequent { <H> >- mem{'A; "type"} } -->
   sequent { <H>; x: 'A >- mem{'B['x]; "type"} }-->
   sequent { <H> >- mem{dfun{'A; x. 'B['x]}; "type"} }

prim s_abs_fam :
   sequent { <H> >- mem{'A; "type"} } -->
   sequent { <H>; x: 'A >- mem{'B['x]; 'K['x]} }-->
   sequent { <H> >- mem{lambda{'A; x. 'B['x]}; dfun{'A; x. 'K['x]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
