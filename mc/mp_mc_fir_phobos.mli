(*
 * Convert preFIR terms to FIR terms.
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
 * Copyright (C) 2002 Adam Granicz, Caltech
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
 * Author: Adam Granicz
 * Email:  granicz@cs.caltech.edu
 *)

include Base_theory
include Itt_theory
include Mp_mc_fir_phobos_exp
include Mp_mc_fir_exp

open Opname
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.RefineError
open Tactic_type.Conversionals
open Phobos_type

val applyAllIFormC : (mp_pre_term * mp_pre_term) list -> conv
