(*!
 * @begin[spelling]
 * ElimArgsOption IntroArgsOption SelectOption ThinOption
 * selT dT ext intro
 * @end[spelling]
 *
 * @begin[doc]
 * @module[Base_dtactic]
 *
 * The @tactic[dT] tactic is the cornerstone of reasoning in
 * most logics; it provides generic application of introduction
 * elimination reasoning.  The @hrefmodule[Base_dtactic] defines a @emph{generic}
 * resource that can be used to add introduction and elimination reasoning.
 * In addition, it add resource @emph{annotations} that can be used in rule
 * definitions to add them automatically to the @tt[dT] resources.
 *
 * The @tt[dT] tactic uses two resources.  The @resource[intro_resource]
 * is used to collect introduction rules; and the @resource[elim_resource]
 * is used to collect elimination rules.  The components of both resources
 * take a term that describes the shape of the goals to which they apply,
 * and a tactic to use when goals of that form are recognized.  The
 * @hrefresource[elim_resource] takes a tactic of type @code{int -> tactic} (the
 * tactic takes the number of the hypothesis to which it applies), and the
 * @hrefresource[intro_resource] takes a tactic of type @code{tactic}.
 *
 * The (@hreftactic[dT] $i$) tactic is a generic tactic that takes the clause number
 * of the clause (either hypothesis or conclusion) to ``decompose,'' and it
 * applies the most appropriate entry from the resources.
 *
 * The resources also allow resource annotations in rule definitions.
 * Typically, the annotation is added to explicit introduction or
 * elimination rules, like the following:
 *
 * $$
 * @defrule{@tt{and@_intro};
 *     @{| @tt{intro@_resource} [ ] |@} H;
 *     @sequent{ext; H; A}@cr
 *        @sequent{ext; H; B};
 *     @sequent{ext; H; A @wedge B}}
 * $$
 *
 * Once this rule is defined, an application of the tactic (@hreftactic[dT] 0)
 * to a conjunction will result in an application of the @hrefrule[and_intro]
 * rule.
 *
 * The resource annotations take a list of optional arguments.  The
 * @hrefresource[intro_resource] takes arguments of the following type:
 *
 * @begin[center]
 * @begin[verbatim]
 * type intro_option =
 *    SelectOption of int
 *  | IntroArgsOption of (tactic_arg -> term -> term list) * term option
 *  | AutoMustComplete
 * @end[verbatim]
 * @end[center]
 *
 * The @tt[SelectOption] is used for rules that require a selection argument.
 * For instance, the disjunction introduction rule has two forms for the left
 * and right-hand forms.
 *
 * $$
 * @defrule{or@_intro@_left;
 *    @{| @tt{intro@_resource} [SelectOption 1] |@} H;
 *    @sequent{ext; H; B @Type}
 *        @cr @sequent{ext; H; A};
 *    @sequent{ext; H; A @wedge B}}
 * $$
 *
 * $$
 * @defrule{or@_intro@_right;
 *   @{| @tt{intro@_resource} [SelectOption 2] |@} H;
 *   @sequent{ext; H; A @Type}@cr
 *      @sequent{ext; H; B};
 *   @sequent{ext; H; A @wedge B}}
 * $$
 *
 * These options require @hreftactic[selT] arguments: the left rule is applied with
 * @tt{selT 1 (dT 0)} and the right rule is applied with @tt{selT 2 (dT 0)}.
 *
 * The @tt[IntroArgsOption] is used to @emph{infer} arguments to the rule.
 * The function argument takes the current goal and a subterm, and it provides
 * an argument list that can be used in the rule application.  The @code{term option}
 * entry describes the subterm to be used for the second function argument.
 *
 * The @tt[AutoMustComplete] option can be used to indicate that the
 * @hreftactic[autoT] tactic should not use this rule unless it is capable
 * of finishing the proof on its own. This option can be used to mark irreversible
 * rules that may take a provable goal and produce potentially unprovable
 * subgoals.
 *
 * The @hrefresource[elim_resource] options are defined with the following type:
 *
 * @begin[center]
 * @begin[verbatim]
 * type elim_option =
 *    ThinOption of (int -> tactic)
 *  | ElimArgsOption of (tactic_arg -> term -> term list) * term option
 * @end[verbatim]
 * @end[center]
 *
 * The @tt[ElimArgsOption] provides arguments in the same way as the
 * @tt[IntroArgsOption].  The @tt[ThinOption] is an argument that provides an
 * optional tactic to ``thin'' the hypothesis after application of the
 * elimination rule.
 *
 * The @hreftactic[dT] resources are implemented as tables that store
 * the term descriptions and tactics for ``decomposition''
 * reasoning.  The @hreftactic[dT] tactic select the most appropriate
 * rule for a given goal and applies it.  The @tt{(dT 0)} tactic
 * is added to the @hrefresource[auto_resource] by default.
 * @end[doc]
 *
 * ---------------------------------------------------------------
 *
 * @begin[license]
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
 * Author: Jason Hickey @email{jyh@cs.caltech.edu}
 * Modified by: Aleksey Nogin @email{nogin@cs.cornell.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends Base_auto_tactic
(*! @docoff *)

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
open Typeinf
open Mptop

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Base_dtactic%t"

let debug_dtactic =
   create_debug (**)
      { debug_name = "dtactic";
        debug_description = "display dT tactic operations";
        debug_value = false
      }

let debug_term_table = load_debug "term_table"

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * The d_tactic uses a term_table to match against terms.
 *)
type intro_option =
   SelectOption of int
 | IntroArgsOption of (tactic_arg -> term -> term list) * term option
 | AutoMustComplete

type elim_option =
   ThinOption of (int -> tactic)
 | ElimArgsOption of (tactic_arg -> term -> term list) * term option

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
      hd :: tl ->
         let t' = hd.info_term in
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
         let tac =
            try assoc name (get_sel_arg p) select with
               RefineError _ ->
                  firstT normal
         in
            tac p
   in

   (* Merge the entries *)
   let compile ({ info_term = t; info_redex = rw; info_value = (name, _, _) }, entries) =
      let tac =
         let normal, select = split [] [] entries in
         let selname = String.concat ":" (List.map (fun (name, _, _) -> name) select) in
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
      if entries != [] then List.map compile (divide entries) else []

(*
 * Extract a D tactic from the data.
 * The tactic checks for an optable.
 *)
let identity x = x

let extract_elim_data data =
   let tbl = create_table data identity in
   fun i p ->
      let t = snd (Sequent.nth_hyp p i) in
      let tac =
         try
            (* Find and apply the right tactic *)
            if !debug_dtactic then
               eprintf "Base_dtactic: lookup %s%t" (SimplePrint.string_of_opname (opname_of_term t)) eflush;
            snd (Term_match_table.lookup tbl t)
         with
            Not_found ->
               raise (RefineError ("extract_elim_data", StringTermError ("D tactic doesn't know about", t)))
      in
         if !debug_dtactic then
            eprintf "Base_dtactic: applying elim %s%t" (SimplePrint.string_of_opname (opname_of_term t)) eflush;

         tac i p

let extract_intro_data data =
   let tbl = create_table data intro_compact in
   fun p ->
      let t = Sequent.concl p in
         try
            (* Find and apply the right tactic *)
            if !debug_dtactic then begin
               eprintf "Base_dtactic: intro: lookup %s%t" (SimplePrint.short_string_of_term t) eflush;
               let sv_deb_table = !debug_term_table in
               debug_term_table:=true;
               try
                  let tac = snd (Term_match_table.lookup tbl t) in
                  debug_term_table:=sv_deb_table;
                  eprintf "Base_dtactic: intro: applying %s%t" (SimplePrint.short_string_of_term t) eflush;
                  tac p
               with
                  Not_found ->
                     debug_term_table:=sv_deb_table;
                     eprintf "Base_dtactic: intro: not found%t" eflush;
                     raise Not_found
            end else
               snd (Term_match_table.lookup tbl t) p
         with
            Not_found ->
               raise (RefineError ("extract_intro_data", StringTermError ("D tactic doesn't know about", t)))


(*
 * Add a new tactic.
 *)
let add_data datas data = data::datas

(*
 * Options for intro rule.
 *)
let rec get_args_arg = function
   IntroArgsOption (f, arg) :: t ->
      Some (f, arg)
 | _ :: t ->
      get_args_arg t
 | [] ->
      None

let rec get_sel_arg = function
   SelectOption sel :: t ->
      Some sel
 | _ :: t ->
      get_sel_arg t
 | [] ->
      None

(*
 * This function needs to be moved into the term module.
 *)
let find_subterm t arg =
   let rec search addr t =
      if alpha_equal t arg then
         addr
      else
         let { term_terms = bterms } = dest_term t in
            search_bterms addr 0 bterms
   and search_bterms addr index = function
      [] ->
         raise Not_found
    | bterm :: bterms ->
         let { bterm = t } = dest_bterm bterm in
            try search (index :: addr) t with
               Not_found ->
                  search_bterms addr (succ index) bterms
   in
      try make_address (List.rev (search [] t)) with
         Not_found ->
            raise (RefineError ("Base_dtactic.improve_intro.find_subterm", StringTermError ("subterm can't be found", arg)))

(*
 * Improve the intro resource from a rule.
 *)
let process_intro_resource_annotation name context_args var_args term_args _ statement (pre_tactic, options) =
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
            match get_args_arg options with
               Some (f, arg) ->
                  let get_arg =
                     match arg with
                        None ->
                           Sequent.concl
                      | Some arg ->
                           let addr = find_subterm t arg in
                              (fun p -> term_subterm (Sequent.concl p) addr)
                  in
                     (fun p -> f p (get_arg p))
             | None ->
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
            let check_auto =
               if List.mem AutoMustComplete options then
                  let exn = RefineError("intro_annotation " ^ name, StringError("not appropriate in autoT")) in
                   (fun p ->
                        if
                           try Sequent.get_bool_arg p "d_auto"
                           with RefineError _ -> false
                        then
                           raise exn)
               else
                  (fun p -> ())
            in
               (fun p ->
                  check_auto p;
                  let vars = Var.maybe_new_vars_array p var_args in
                  let addr = Sequent.hyp_count_addr p in
                     Tactic_type.Tactic.tactic_of_rule pre_tactic ([| addr |], vars) (term_args p) p)
       | _ ->
            raise (Invalid_argument (sprintf "Base_dtactic.intro: %s: not an introduction rule" name))
   in
      t, (name, get_sel_arg options, tac)

(*
 * Compile an elimination tactic.
 *)
let rec get_elim_args_arg = function
   ElimArgsOption (f, arg) :: t ->
      Some (f, arg)
 | _ :: t ->
      get_elim_args_arg t
 | [] ->
      None

let tryThinT thinT v i p =
   if get_thinning_arg p then
      let i =
         try
            let v', _ = Sequent.nth_hyp p i in
            if (v=v') then i else Sequent.get_decl_number p v
         with RefineError _ -> Sequent.get_decl_number p v
      in
         tryT (thinT i) p
   else
      idT p

let process_elim_resource_annotation name context_args var_args term_args _ statement (pre_tactic, options) =
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
            (fun _ _ -> [])
       | _ ->
            match get_elim_args_arg options with
               Some (f, arg) ->
                  let get_arg =
                     match arg with
                        None ->
                           (fun p i -> snd (Sequent.nth_hyp p i))
                      | Some arg ->
                           let addr = find_subterm t arg in
                              (fun p i -> term_subterm (snd (Sequent.nth_hyp p i)) addr)
                  in
                     (fun i p -> f p (get_arg p i))
             | None ->
                  let length = List.length term_args in
                     (fun _ p ->
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
                  let vars = Var.maybe_new_vars_array p vars in
                     vars.(index) <- v;
                     vars)
      else
         (fun i p -> Var.maybe_new_vars_array p var_args)
   in
   let thinT =
      let rec collect = function
         ThinOption thinT :: _ ->
            Some thinT
       | _ :: t ->
            collect t
       | [] ->
            None
      in
         collect options
   in
   let tac =
      match context_args, thinT with
         [| _; _ |], None ->
            (fun i p ->
                  let vars = new_vars i p in
                  let j, k = Sequent.hyp_indices p i in
                     Tactic_type.Tactic.tactic_of_rule pre_tactic ([| j; k |], new_vars i p) (term_args i p) p)

       | [| _; _ |], Some thinT ->
            (fun i p ->
                  let v, _ = Sequent.nth_hyp p i in
                  let vars = new_vars i p in
                  let j, k = Sequent.hyp_indices p i in
                     (Tactic_type.Tactic.tactic_of_rule pre_tactic ([| j; k |], new_vars i p) (term_args i p)
                      thenT tryThinT thinT v i) p)
       | _ ->
            raise (Invalid_argument (sprintf "Base_dtactic: %s: not an elimination rule" name))
   in
      t, tac

let add_intro_data datas ((t, _) as data) =
   if !debug_dtactic then begin
      let opname = opname_of_term t in
         eprintf "Base_dtactic.improve_intro_resource: %s%t" (string_of_opname opname) eflush
   end;
   add_data datas data

let wrap_intro tac =
   ("wrap_intro", None, tac)

let add_elim_data datas ((t,_) as data) =
   if !debug_dtactic then begin
      let opname = opname_of_term t in
         eprintf "Base_dtactic.improve_elim_resource: %s%t" (string_of_opname opname) eflush
   end;
   add_data datas data

(*
 * Resource.
 *)
let resource elim = Functional {
   fp_empty = [];
   fp_add = add_elim_data;
   fp_retr = extract_elim_data;
}

let resource intro = Functional {
   fp_empty = [];
   fp_add = add_intro_data;
   fp_retr = extract_intro_data;
}

let dT i p =
   if i = 0 then
      Sequent.get_resource_arg p get_intro_resource p
   else
      Sequent.get_resource_arg p get_elim_resource i p

let rec dForT i =
   if i <= 0 then
      idT
   else
      dT 0 thenMT dForT (pred i)

(*
 * By default, dT 0 should always make progress.
 *)
let d_prec = create_auto_prec [trivial_prec] []
let d_elim_prec = create_auto_prec [trivial_prec; d_prec] []

let eq_exn = RefineError ("dT", StringError "elim rule not suitable for autoT")

let not_equal t i p =
   if alpha_equal t (snd (Sequent.nth_hyp p i)) then raise eq_exn else idT p

let auto_dT i p =
   (dT i thenT not_equal (snd (Sequent.nth_hyp p i)) i) p

let resource auto += [ {
   auto_name = "dT";
   auto_prec = d_prec;
   auto_tac = withBoolT "d_auto" true (dT 0);
   auto_type = AutoNormal;
}; {
   auto_name = "dT complete";
   auto_prec = d_prec;
   auto_tac = withBoolT "d_auto" false (dT 0);
   auto_type = AutoComplete;
}; {
   auto_name = "dT elim-complete";
   auto_prec = d_elim_prec;
   auto_tac = onSomeHypT auto_dT;
   auto_type = AutoComplete;
}]

let elim_typeinf t = ElimArgsOption (infer_type_args, Some t)
let intro_typeinf t = IntroArgsOption (infer_type_args, Some t)
let univ_arg_fun p _ = [get_univ_arg p]
let elim_univ_arg = ElimArgsOption (univ_arg_fun, None)
let intro_univ_arg = IntroArgsOption (univ_arg_fun, None)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
