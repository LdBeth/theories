(*
 * The D tactic performs a case selection on the conclusion opname.
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

include Base_auto_tactic

open Printf
open Mp_debug

open Opname
open Refiner.Refiner
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermMeta
open Refiner.Refiner.RefineError
open Mp_resource
open Simple_print
open Term_match_table

open Tactic_type
open Tactic_type.Tacticals

open Base_auto_tactic
open Mptop

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Base_dtactic%t" eflush

let debug_dtactic =
   create_debug (**)
      { debug_name = "dtactic";
        debug_description = "display dT tactic operations";
        debug_value = false
      }

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * The d_tactic uses a term_table to match against terms.
 *)
type elim_data = (int -> tactic, int -> tactic) term_table
type intro_data = (string * int option * tactic, tactic) term_table

type intro_option =
   SelectOption of int        (* Select among multiple introduction rules *)

type elim_option =
   ThinOption                 (* Normally thin the eliminated hyp, unless overridden *)

resource (term * (int -> tactic), int -> tactic, elim_data, Tactic.pre_tactic * elim_option list) elim_resource
resource (term * tactic, tactic, intro_data, Tactic.pre_tactic * intro_option list) intro_resource

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Merge the entries for the tactics.
 * First, separate them into alpha equal terms.
 *)
let intro_compact entries =
   (* Collect all the entries with the same term value *)
   let rec separate t = function
      { info_term = t' } as hd :: tl ->
         let entries, tl = separate t tl in
            if alpha_equal t t' then
               hd :: entries, tl
            else
               entries, hd :: tl
    | [] ->
         [], []
   in

   (* Divide the entries into sets that have the same term values *)
   let rec divide = function
      info :: tl ->
         let entries, tl = separate info.info_term tl in
            (info, (info :: entries)) :: divide tl
    | [] ->
         []
   in

   (* Split into normal/select versions *)
   let rec split normal select = function
      { info_value = (name, Some sel, tac) } as hd :: tl ->
         split normal ((name, sel, tac) :: select) tl
    | { info_value = (_, None, tac) } as hd :: tl ->
         split (tac :: normal) select tl
    | [] ->
         List.rev normal, List.rev select
   in

   (* Find a selected tactic in the list *)
   let rec assoc name sel = function
      (sel', tac) :: tl ->
         if sel' = sel then
            tac
         else
            assoc name sel tl
    | [] ->
         raise (RefineError (name, StringIntError ("selT argument is out of range", sel)))
   in

   (* Compile the select version of the tactic *)
   let compile_select name entries = fun
      p ->
         let sel =
            try get_sel_arg p with
               RefineError _ ->
                  raise (RefineError (name, StringError "selT argument required"))
         in
            assoc name sel entries p
   in

   (* Compile the non-selected version of the tactic *)
   let compile_normal entries =
      firstT entries
   in

   (* Compile the most general form *)
   let compile_general name normal select = fun
      p ->
         match
            try Some (get_sel_arg p) with
               RefineError _ ->
                  None
         with
            Some sel ->
               assoc name sel select p
          | None ->
               firstT normal p
   in

   (* Merge the entries *)
   let compile ({ info_term = t; info_redex = rw; info_value = (name, _, _) }, entries) =
      let tac =
         let normal, select = split [] [] entries in
         let selname = String_util.concat ":" (List.map (fun (name, _, _) -> name) select) in
         let select = List.map (fun (_, sel, tac) -> sel, tac) select in
            match normal, select with
               [], [] ->
                  raise (Invalid_argument "Base_dtactic: intro_merge")
             | [], select ->
                  compile_select selname select
             | normal, [] ->
                  compile_normal normal
             | normal, select ->
                  compile_general selname normal select
      in
         { info_term = t;
           info_redex = rw;
           info_value = tac
         }
   in
      List.map compile (divide entries)


(*
 * Extract a D tactic from the data.
 * The tactic checks for an optable.
 *)
let identity x = x

let extract_elim_data tbl = fun
   i p ->
      let t = snd (Sequent.nth_hyp p i) in
      let tac =
         try
            (* Find and apply the right tactic *)
            if !debug_dtactic then
               eprintf "Base_dtactic: lookup %s%t" (SimplePrint.string_of_opname (opname_of_term t)) eflush;
            let _, _, tac = Term_match_table.lookup "Base_dtactic.extract_elim_data" tbl identity t in
               tac
         with
            Not_found ->
               raise (RefineError ("extract_elim_data", StringTermError ("D tactic doesn't know about", t)))
      in
         if !debug_dtactic then
            eprintf "Base_dtactic: applying elim %s%t" (SimplePrint.string_of_opname (opname_of_term t)) eflush;

         tac i p

let extract_intro_data tbl = fun
   p ->
      let t = Sequent.concl p in
      let tac =
         try
            (* Find and apply the right tactic *)
            if !debug_dtactic then
               eprintf "Base_dtactic: lookup %s%t" (SimplePrint.string_of_opname (opname_of_term t)) eflush;
            let _, _, tac = Term_match_table.lookup "Base_dtactic.extract_intro_data" tbl intro_compact t in
               tac
         with
            Not_found ->
               raise (RefineError ("extract_intro_data", StringTermError ("D tactic doesn't know about", t)))
      in
         if !debug_dtactic then
            eprintf "Base_dtactic: applying intro %s%t" (SimplePrint.string_of_opname (opname_of_term t)) eflush;

         tac p

(*
 * Add a new tactic.
 *)
let improve_data (t, tac) tbl =
   Refine_exn.print Dform.null_base (insert tbl t) tac

(*
 * Improve the introduction resource from the rule argument.
 *)
let improve_intro_arg rsrc name context_args var_args term_args _ statement (pre_tactic, options) =
   let _, goal = unzip_mfunction statement in
   let t =
      try TermMan.nth_concl goal 1 with
         RefineError _ ->
            raise (Invalid_argument (sprintf "Base_dtactic.improve_intro: %s: must be an introduction rule" name))
   in
   let term_args =
      match term_args with
         [] ->
            (fun _ -> [])
       | _ ->
            let length = List.length term_args in
               (fun p ->
                     let args =
                        try get_with_args p with
                           RefineError _ ->
                              raise (RefineError (name, StringIntError ("arguments required", length)))
                     in
                     let length' = List.length args in
                        if length' != length then
                           raise (RefineError (name, StringIntError ("wrong number of arguments", length')));
                        args)
   in
   let tac =
      match context_args with
         [|_|] ->
            (fun p ->
               let vars = Var.maybe_new_vars_array p var_args in
               let addr = Sequent.hyp_count_addr p in
                  Tactic_type.Tactic.tactic_of_rule pre_tactic ([| addr |], vars) (term_args p) p)
       | _ ->
            raise (Invalid_argument (sprintf "Base_dtactic.intro: %s: not an introduction rule" name))
   in
   let rec get_sel_arg = function
      SelectOption i :: _ ->
         Some i
    | [] ->
         None
   in
      improve_data (t, (name, get_sel_arg options, tac)) rsrc

(*
 * Compile an elimination tactic.
 *)
let improve_elim_arg rsrc name context_args var_args term_args _ statement (pre_tactic, options) =
   let _, goal = unzip_mfunction statement in
   let { sequent_hyps = hyps } =
      try TermMan.explode_sequent goal with
         RefineError _ ->
            raise (Invalid_argument (sprintf "Base_dtactic.improve_elim: %s: must be a sequent" name))
   in
   let v, t =
      let rec search i len =
         if i = len then
            raise (Invalid_argument (sprintf "Base_dtactic.improve_elim: %s: must be an elimination rule" name))
         else
            match SeqHyp.get hyps i with
               Hypothesis (v, t) ->
                  v, t
             | Context _ ->
                  search (succ i) len
      in
         search 0 (SeqHyp.length hyps)
   in
   let term_args =
      match term_args with
         [] ->
            (fun _ -> [])
       | _ ->
            let length = List.length term_args in
               (fun p ->
                     let args =
                        try get_with_args p with
                           RefineError _ ->
                              raise (RefineError (name, StringIntError ("arguments required", length)))
                     in
                     let length' = List.length args in
                        if length' != length then
                           raise (RefineError (name, StringIntError ("wrong number of arguments", length')));
                        args)
   in
   let new_vars =
      if Array_util.mem v var_args then
         let index = Array_util.index v var_args in
            (fun i p ->
                  let v, _ = Sequent.nth_hyp p i in
                  let vars = Array.copy var_args in
                     vars.(index) <- v;
                     Var.maybe_new_vars_array p vars)
      else
         (fun i p -> Var.maybe_new_vars_array p var_args)
   in
   let tac =
      match context_args with
         [| _; _ |] ->
            (fun i p ->
                  let vars = new_vars i p in
                  let j, k = Sequent.hyp_indices p i in
                     Tactic_type.Tactic.tactic_of_rule pre_tactic ([| j; k |], new_vars i p) (term_args p) p)
       | _ ->
            raise (Invalid_argument (sprintf "Base_dtactic: %s: not an elimination rule" name))
   in
      improve_data (t, tac) rsrc

(*
 * Wrap up the joiner.
 *)
let join_resource = join_tables

let improve_intro_resource data (t, tac) =
   if !debug_dtactic then
      begin
         let opname = opname_of_term t in
            eprintf "Base_dtactic.improve_intro_resource: %s%t" (string_of_opname opname) eflush
      end;
   improve_data (t, ("Base_dtactic.improve_intro_resource", None, tac)) data

let improve_elim_resource data t =
   if !debug_dtactic then
      begin
         let opname = opname_of_term (fst t) in
            eprintf "Base_dtactic.improve_elim_resource: %s%t" (string_of_opname opname) eflush
      end;
   improve_data t data

let close_resource rsrc modname =
   rsrc

(*
 * Resource.
 *)
let elim_resource =
   Mp_resource.create (**)
      { resource_join = join_resource;
        resource_extract = extract_elim_data;
        resource_improve = improve_elim_resource;
        resource_improve_arg = improve_elim_arg;
        resource_close = close_resource
      }
      (new_table ())

let intro_resource =
   Mp_resource.create (**)
      { resource_join = join_resource;
        resource_extract = extract_intro_data;
        resource_improve = improve_intro_resource;
        resource_improve_arg = improve_intro_arg;
        resource_close = close_resource
      }
      (new_table ())

let dT i p =
   if i = 0 then
      Sequent.get_tactic_arg p "intro" p
   else
      Sequent.get_int_tactic_arg p "elim" i p

let rec dForT i =
   if i <= 0 then
      idT
   else
      dT 0 thenMT dForT (pred i)

(*
 * Combined adding.
 *)
let rec add_intro_info rsrc = function
   h :: t ->
      add_intro_info (improve rsrc h) t
 | [] ->
      rsrc

(*
 * By default, dT 0 should always make progress.
 *)
let d_prec = create_auto_prec [trivial_prec] []

let auto_resource =
   Mp_resource.improve auto_resource (**)
      { auto_name = "dT";
        auto_prec = d_prec;
        auto_tac = auto_wrap (dT 0)
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
