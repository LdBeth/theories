(*
 * Add terms and ML rules for higher-order rules.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005 Mojave Group, Caltech
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
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends Base_theory
extends Meta_struct

open Basic_tactics

(*
 * The meta-implication and proof terms.
 *)
declare mimplies{'premise : Judgment; 'rest : Judgment} : Judgment
declare mlambda{x. 'e['x]}
declare mapply{'e1; 'e2}

(*
 * ML terms.
 *)
val mk_mimplies_term : term -> term -> term
val dest_mimplies_term : term -> term * term

val mk_mlambda_term : var -> term -> term
val dest_mlambda_term : term -> var * term

val mk_mapply_term : term -> term -> term
val dest_mapply_term : term -> term * term

(*
 * Tactics.
 *)
topval moveToGoalT : int -> tactic

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
