(*
 * Isomorphism.
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
 * Copyright (C) 2002 Xin Yu, Caltech
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
 * Author: Xin Yu
 * Email : xiny@cs.caltech.edu
 *)

extends Czf_itt_hom

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare iso{'g1; 'g2; x. 'f['x]}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

rewrite unfold_iso : iso{'g1; 'g2; x. 'f['x]} <-->
   (hom{'g1; 'g2; x. 'f['x]} & (all c: set. all d: set. (mem{'c; car{'g1}} => mem{'d; car{'g1}} => eq{'f['c]; 'f['d]} => eq{'c; 'd})) & (all e: set. (mem{'e; car{'g2}} => (exst p: set. (mem{'p; car{'g1}} & eq{'e; 'f['p]})))))

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
