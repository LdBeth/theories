(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Term construction / deconstruction convinience functions
 * for MC theory terms.
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
 * Email:  emre@its.caltech.edu
 *)

include Base_theory

open Opname
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.RefineError

(*************************************************************************
 * General utility.
 *************************************************************************)

(*
 * Turn a binding variable into a string.
 *)

let string_of_binding_var t =
   match dest_term t with
      { term_op = _; term_terms = [bt1] } ->
         (
            match dest_bterm bt1 with
               { bvars = [s1]; bterm = t1 } ->
                  s1
             | _ ->
               raise (RefineError ("string_of_binding_var", StringTermError
                     ("not exactly one bvar?", t)))
         )
    | _ ->
         raise (RefineError ("string_of_binding_var", StringTermError
               ("not a term with one subterm with one bvar?", t)))

(*
 * Deconstruct a term into some convinient entities.
 *)

let pre_dest_term t =
   ( opname_of_term t, subterm_arities t, subterms_of_term t )

(*
 * Convinience to check arity and opname at the same time.
 *)

let opname_arity_check opname_requested arities_requested opname arities =
   Opname.eq opname_requested opname && arities_requested = arities

(*************************************************************************
 * 4 subterms.
 *************************************************************************)

let is_4_dep0_term opname t =
   let (opname', arities, subterms) = pre_dest_term t in
      opname_arity_check opname' [0;0;0;0] opname arities

let mk_4_dep0_term opname t1 t2 t3 t4 =
   mk_term  (make_op { op_name = opname; op_params = [] })
            [ mk_simple_bterm t1; mk_simple_bterm t2;
              mk_simple_bterm t3; mk_simple_bterm t4
            ]

let dest_4_dep0_term opname t =
   let (opname', arities, subterms) = pre_dest_term t in
      if opname_arity_check opname' [0;0;0;0] opname arities then
         match subterms with
            [t1; t2; t3; t4] ->
               t1, t2, t3, t4
          | _ ->
               raise (RefineError ("dest_4_dep0_term", StringTermError
                     ("internal error", t)))
      else
         raise (RefineError ("dest_4_dep0_term", StringTermError
               ("invalid term structure", t)))

let is_3_dep0_1_dep1_term opname t =
   let (opname', arities, subterms) = pre_dest_term t in
      opname_arity_check opname [0;0;0;1] opname' arities

let mk_3_dep0_1_dep1_term opname t1 t2 t3 b4 t4 =
   mk_term  (make_op { op_name = opname; op_params = [] })
            [ mk_simple_bterm t1; mk_simple_bterm t2; mk_simple_bterm t3;
              mk_bterm [b4] t4
            ]

let dest_3_dep0_1_dep1_term opname t =
   let (opname', arities, subterms) = pre_dest_term t in
      if opname_arity_check opname [0;0;0;1] opname' arities then
         match subterms with
            [t1; t2; t3; t4] ->
               t1, t2, t3, string_of_binding_var t4, t4
          | _ ->
               raise (RefineError ("dest_3_dep0_1_dep1_term", StringTermError
                     ("internal error", t)))
      else
         raise (RefineError ("dest_3_dep0_1_dep1_term", StringTermError
               ("invalid term structure", t)))

(*************************************************************************
 * 5 subterms.
 *************************************************************************)

let is_4_dep0_1_dep1_term opname t =
   let (opname', arities, subterms) = pre_dest_term t in
      opname_arity_check opname [0;0;0;0;1] opname' arities

let mk_4_dep0_1_dep1_term opname t1 t2 t3 t4 b5 t5 =
   mk_term  (make_op { op_name = opname; op_params = [] })
            [ mk_simple_bterm t1; mk_simple_bterm t2; mk_simple_bterm t3;
              mk_simple_bterm t4; mk_bterm [b5] t5
            ]

let dest_4_dep0_1_dep1_term opname t =
   let (opname', arities, subterms) = pre_dest_term t in
      if opname_arity_check opname [0;0;0;0;1] opname' arities then
         match subterms with
            [t1; t2; t3; t4; t5] ->
               t1, t2, t3, t4, string_of_binding_var t5, t5
          | _ ->
               raise (RefineError ("dest_4_dep0_1_dep1_term", StringTermError
                     ("internal error", t)))
      else
         raise (RefineError ("dest_4_dep0_1_dep1_term", StringTermError
               ("invalid term structure", t)))

(*************************************************************************
 * 6 subterms.
 *************************************************************************)

let is_5_dep0_1_dep1_term opname t =
   let (opname', arities, subterms) = pre_dest_term t in
      opname_arity_check opname [0;0;0;0;0;1] opname' arities

let mk_5_dep0_1_dep1_term opname t1 t2 t3 t4 t5 b6 t6 =
   mk_term  (make_op { op_name = opname; op_params = [] })
            [ mk_simple_bterm t1; mk_simple_bterm t2; mk_simple_bterm t3;
              mk_simple_bterm t4; mk_simple_bterm t5; mk_bterm [b6] t6
            ]

let dest_5_dep0_1_dep1_term opname t =
   let (opname', arities, subterms) = pre_dest_term t in
      if opname_arity_check opname [0;0;0;0;0;1] opname' arities then
         match subterms with
            [t1; t2; t3; t4; t5; t6] ->
               t1, t2, t3, t4, t5, string_of_binding_var t6, t6
          | _ ->
               raise (RefineError ("dest_5_dep0_1_dep1_term", StringTermError
                     ("internal error", t)))
      else
         raise (RefineError ("dest_5_dep0_1_dep1_term", StringTermError
               ("invalid term structure", t)))

(*************************************************************************
 * 7 subterms.
 *************************************************************************)

let is_7_dep0_term opname t =
   let (opname', arities, subterms) = pre_dest_term t in
      opname_arity_check opname [0;0;0;0;0;0;0] opname' arities

let mk_7_dep0_term opname t1 t2 t3 t4 t5 t6 t7 =
   mk_term  (make_op { op_name = opname; op_params = [] })
            [ mk_simple_bterm t1; mk_simple_bterm t2; mk_simple_bterm t3;
              mk_simple_bterm t4; mk_simple_bterm t5; mk_simple_bterm t6;
              mk_simple_bterm t7
            ]

let dest_7_dep0_term opname t =
   let (opname', arities, subterms) = pre_dest_term t in
      if opname_arity_check opname [0;0;0;0;0;0;0] opname' arities then
         match subterms with
            [t1; t2; t3; t4; t5; t6; t7] ->
               t1, t2, t3, t4, t5, t6, t7
          | _ ->
               raise (RefineError ("dest_7_dep0_term", StringTermError
                     ("internal error", t)))
      else
         raise (RefineError ("dest_7_dep0_term", StringTermError
               ("invalid term structure", t)))