(*
 * Interpretation of universe is a decidable type in U1.
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

extends Itt_theory
extends Fol_type_itt
extends Fol_univ

declare ufalse{'t}
declare utrue{'t}

rewrite unfold_univ : univ <--> (T: Itt_equal!univ[1:l] * "type"{'T})
rewrite unfold_prop : prop{'t} <--> fst{'t}

rewrite unfold_ufalse : ufalse{'t} <--> pair{'t; inl{it}}
rewrite unfold_utrue : utrue{'t} <--> pair{'t; inr{it}}

rewrite reduce_prop_ufalse : prop{ufalse{'t}} <--> 't
rewrite reduce_prop_utrue : prop{utrue{'t}} <--> 't

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
