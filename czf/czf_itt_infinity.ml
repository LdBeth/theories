(*
 * Infinite set.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
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

include Czf_itt_singleton
include Czf_itt_dall
include Czf_itt_dexists
include Czf_itt_sall
include Czf_itt_sexists
include Czf_itt_empty

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "inf"

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_inf : inf <--> collect{list{unit}; l. list_ind{'l; empty; h, t, g. sing{'g}}}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform inf_df : inf =
   `"inf"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Empty is a set.
 *)
interactive inf_isset {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- isset{inf} }

(*
 * Nothing is in the empty set.
 *)
interactive inf_axiom 'H 'J :
   sequent ['ext] { 'H; x: sexists{s. member{'s; inf}}; y: dall{inf; x. dexists{inf; y. member{'x; 'y}}} >- 'C } -->
   sequent ['ext] { 'H >- 'C }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
