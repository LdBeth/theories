(*!
 * @begin[doc]
 * @module[Mfir_comment]
 *
 * The @tt{Mfir_comment} module declares terms and display forms
 * for formatting comments in the FIR theory.
 * @end[doc]
 *
 * ------------------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.  Additional
 * information about the system is available at
 * http://www.metaprl.org/
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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
 * Author: Brian Emre Aydemir
 * @email{emre@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @docoff
 *)

extends Base_theory

(**************************************************************************
 * Declarations.
 **************************************************************************)

(* Boldface text. *)
declare mfir_bf[text:s]

(**************************************************************************
 * Display forms.
 **************************************************************************)

dform mfir_bf_df : except_mode[src] ::
   mfir_bf[text:s] =
   slot[text:s]

dform mfir_bf_df : mode[tex] ::
   mfir_bf[text:s] =
   izone `"{\\bf " ezone
   slot[text:s]
   izone `"}" ezone
