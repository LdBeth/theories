(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Provides the primary interface to the MCC compiler.
 *
 * ----------------------------------------------------------------
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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
include Mp_mc_theory (* Needed to establish proper dependencies. *)

open Symbol
open Fir

open Simple_print.SimplePrint
open Top_conversionals

open Mp_mc_fir_phobos
open Mp_mc_fir_eval
open Mp_mc_deadcode
open Mp_mc_connect_prog
open Mp_mc_inline

(* Set this to true to enable debugging code / output. *)

let debug = ref false

(* Simple functions for debug printing of strings and terms. *)

let debug_string str =
   if !debug then print_string ("\n" ^ str ^ "\n")

let debug_term term =
   if !debug then begin
      print_string "\n";
      print_simple_term term;
      print_string "\n"
   end

(*
 * These are the rewriters we want to use to rewrite terms.
 *)

let apply_rewrite_top =
   apply_rewrite (Mp_resource.theory_bookmark "Mp_mc_theory")

let apply_rewrite_post =
   apply_rewrite (Mp_resource.theory_bookmark "Mp_mc_fir_phobos")

(*************************************************************************
 * Taking input from Phobos.
 *************************************************************************)

(*
 * Take some global data, a program term, and inline the given target.
 *)

let inline_target global_data program target =

   (* Setup the inline wrapper. *)
   let inline_prep = mk_add_inline_wrapper_term target global_data program in
   let inline_ready = apply_rewrite_top firInlineAddWrapperC inline_prep in

   (* Inlining (and normalization) time! *)
   let new_prog = apply_rewrite_top firInlineC inline_ready in
   let new_prog = apply_rewrite_top reduceC new_prog in
      apply_rewrite_top firExpEvalC new_prog

(*
 * Loop over the inline targets until a fix point.
 *)

let rec inline_target_loop global_data program inline_forms =
   let new_program =
      List.fold_left (inline_target global_data) program inline_forms
   in
      if program = new_program then
         program
      else
         inline_target_loop global_data new_program inline_forms

(*
 * Inline an firProg term using the given inline_forms as targets.
 *)

let inline_firProg program inline_forms =

   (* Extract the "global" information first. *)
   let pre_global_data = mk_extract_sym_func_pairs_term program in
   let global_data = apply_rewrite_top firInlineGetGlobalInfoC pre_global_data
   in
   debug_string "\n\nGlobal data extracted:\n\n";
   debug_term global_data;

   (* Okay, inline the targets.  Yes, this approach needs work still. *)
   inline_target_loop global_data program inline_forms

(*
   List.fold_left (inline_target global_data) program inline_forms
*)

(*
 * Takes a FIR term generated by Phobos and for now, applies some rewrites
 * to it, and then just quits.  Eventually, the processed term will
 * be given back to MCC as an Fir.prog struct for further compilation.
 *)

(*
 * NOTE: post_rewrites is (mp_term * mp_term) list list, where
 *       type mp_term = term * pos
 *)
let compile_phobos_fir term post_rewrites_list inline_forms =

   (* Just need the term portion of inline_forms. *)
   let inline_forms = List.map (fun (x,y) -> x) inline_forms in

   (* Dump out initial input. *)
   debug_string "\n\nBefore PhoFIR -> FIR:\n\n";
   debug_string "\n\nProgram:\n\n";
   debug_term term;
   debug_string "\n\nInline_forms:\n\n";
   ignore (List.map debug_term inline_forms);

   (* General reductions *)
   let term = apply_rewrite_top reduceC term in
   debug_string "\n\nAfter general reductions:\n\n";
   debug_term term;

   (* We apply each set of post-parsing rewrites one after another. *)
   let term = List.fold_left
      (fun term post_rewrites ->
         apply_rewrite_post (applyAllIFormC post_rewrites) term)
      term
      post_rewrites_list
   in
   debug_string "\n\nAfter PhoFIR -> FIR\n\n";
   debug_term term;

   (* Inlining. *)
   let term = inline_firProg term inline_forms in
   debug_string "\n\nAfter inlining\n\n";
   debug_term term;

   (* Apply optimizations. *)
   let term = apply_rewrite_top firDeadcodeC term in
   let term = apply_rewrite_top firExpEvalC term in
   print_string "\n\nFinal term =\n\n";
   print_simple_term term;
   print_string "\n\nfirProg -> Fir.prog not implemented yet\n"

(*************************************************************************
 * Taking input from an MCC Fir.prog.
 *************************************************************************)

(*
 * Takes a MCC Fir.prog structure and applies some rewrites to it,
 * and then returns a new Fir.prog struct to MCC for further compilation.
 *)

let compile_mc_fir prog =
   debug_string "Entering Mp_mc_compile.compile_mc_fir.";

   let table = SymbolTable.map term_of_fundef prog.prog_funs in

   debug_string "Printing initial term structure.";
   let _ = SymbolTable.map debug_term table in

   let table = SymbolTable.map (apply_rewrite_top firDeadcodeC) table in
   let table = SymbolTable.map (apply_rewrite_top firExpEvalC) table in

   debug_string "Printing optimized term structure.";
   let _ = SymbolTable.map debug_term table in

   debug_string "Performing term -> Fir.prog conversion and returning.";
   let new_prog_funs = SymbolTable.map fundef_of_term table in
      { prog with prog_funs = new_prog_funs }
