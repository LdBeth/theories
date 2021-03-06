(*
 * Additional well-formedness rule for bterms.
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
extends Itt_hoas_lof
extends Itt_hoas_lof_vec

open Basic_tactics

(*
 * Normalization resource.
 *)
resource (term * conv, conv) pre_normalize_simple
resource (term * conv, conv) normalize_simple

val process_pre_normalize_simple_resource_rw_annotation : (term * conv) rw_annotation_processor
val process_normalize_simple_resource_rw_annotation : (term * conv) rw_annotation_processor

(*
 * Normalize the term.
 *)
topval normalizeBTermC : conv
topval normalizeBTermForceC : conv

(*
 * Debugging.
 *)
topval normalizeBTermSimpleC : conv
topval normalizeBTermAuxC : conv

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
