(*
 * Equality type.
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
 *
 *)

include Base_theory
include Itt_squash

open Printf
open Mp_debug
open String_set
open Opname
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermMeta
open Refiner.Refiner.RefineError
open Rformat
open Simple_print
open Term_stable
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Mptop

open Base_meta
open Base_auto_tactic

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_equal%t"

let debug_eqcd =
   create_debug (**)
      { debug_name = "eqcd";
        debug_description = "display eqcd operations";
        debug_value = false
      }

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

let x = 1

declare "type"{'a}
declare univ[i:l]
declare equal{'T; 'a; 'b}
declare "true"
declare "false"
declare cumulativity[i:l, j:l]

let true_term = << "true" >>
let true_opname = opname_of_term true_term
let is_true_term = is_no_subterms_term true_opname

let false_term = << "false" >>
let false_opname = opname_of_term false_term
let is_false_term = is_no_subterms_term false_opname

let cumulativity_term = << cumulativity[i:l, j:l] >>

let equal_term = << 'a = 'b in 'c >>
let equal_opname = opname_of_term equal_term
let is_equal_term = is_dep0_dep0_dep0_term equal_opname
let dest_equal = dest_dep0_dep0_dep0_term equal_opname
let mk_equal_term = mk_dep0_dep0_dep0_term equal_opname

let is_member_term t =
   is_equal_term t &&
   match dest_equal t with
      _, t1, t2 -> alpha_equal t1 t2

let type_term = << "type"{'t} >>
let type_opname = opname_of_term type_term
let is_type_term = is_dep0_term type_opname
let mk_type_term = mk_dep0_term type_opname
let dest_type_term = dest_dep0_term type_opname

let univ_term = << univ[i:l] >>
let univ1_term = << univ[1:l] >>
let univ_opname = opname_of_term univ_term
let is_univ_term = TermOp.is_univ_term univ_opname
let dest_univ = TermOp.dest_univ_term univ_opname
let mk_univ_term = TermOp.mk_univ_term univ_opname

let unknown_level = dest_univ << univ[unknown:l] >>

let try_dest_univ t =
   if is_univ_term t then dest_univ t else unknown_level

let it_term = << it >>

let squash_term = << squash >>
let squash_opname = opname_of_term squash_term
let is_squash_term = is_no_subterms_term squash_opname

(************************************************************************
 * EQCD RESOURCE                                                        *
 ************************************************************************)

(*
 * EQCD resource.
 * Use simple table.
 *)
type eqcd_data = tactic term_stable

resource (term * tactic, tactic, eqcd_data, Tactic.pre_tactic) eqcd_resource

(*
 * Extract an EQCD tactic from the data.
 * The tactic checks for an optable.
 *)
let extract_data base =
   let tbl = sextract base in
   let eqcd p =
      let t = Sequent.concl p in
      let _, l, _ = dest_equal t in
         try
            (* Find and apply the right tactic *)
            if !debug_eqcd then
               eprintf "Itt_equal.eqcd: looking up %s%t" (SimplePrint.string_of_opname (opname_of_term l)) eflush;
            let tac = slookup tbl l in
               if !debug_eqcd then
                  eprintf "Itt_equal.eqcd: found a tactic for %s%t" (SimplePrint.string_of_opname (opname_of_term l)) eflush;
               tac p
         with
            Not_found ->
               raise (RefineError ("eqcd", StringTermError ("EQCD tactic doesn't know about ", l)))
   in
      eqcd

(*
 * Add info from a rule definition.
 *)
let improve_intro_arg data name context_args var_args term_args _ statement pre_tactic =
   let _, goal = unzip_mfunction statement in
   let t =
      try TermMan.nth_concl goal 1 with
         RefineError _ ->
            raise (Invalid_argument (sprintf "Itt_equal.improve_intro: %s: must be an introduction rule" name))
   in
   let _, t, _ =
      try dest_equal t with
         RefineError _ ->
            raise (Invalid_argument (sprintf "Itt_equal.improve_intro: %s must be an equality judgement" name))
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
            raise (Invalid_argument (sprintf "Itt_equal.intro: %s: not an introduction rule" name))
   in
      sinsert data t tac

(*
 * Wrap up the joiner.
 *)
let join_resource = join_stables

let extract_resource = extract_data

let improve_resource data (t, tac) =
   sinsert data t tac

let close_resource rsrc _ =
   rsrc

(*
 * Resource.
 *)
let eqcd_resource =
   ((Mp_resource.create (**)
      { resource_join = join_resource;
        resource_extract = extract_resource;
        resource_improve = improve_resource;
        resource_improve_arg = improve_intro_arg;
        resource_close = close_resource
      }
      (new_stable ())) : (term * tactic, tactic, eqcd_data, Tactic.pre_tactic) Mp_resource.t)

let get_resource modname =
   Mp_resource.find eqcd_resource modname

(*
 * Resource argument.
 *)
let eqcdT p =
   Tactic_type.Sequent.get_tactic_arg p "eqcd" p

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

prim_rw reduce_cumulativity' : cumulativity[i:l, j:l] <-->
   meta_lt{univ[i:l]; univ[j:l]; ."true"; ."false"}

let reduce_cumulativity =
   reduce_cumulativity' andthenC reduce_meta_lt

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_type
prec prec_equal

dform equal_df : except_mode[src] :: parens :: "prec"[prec_equal] :: equal{'T; 'a; 'b} =
   szone pushm slot{'a} space `"= " slot{'b} space Nuprl_font!member `" " slot{'T} popm ezone

dform equal_df2 : mode[src] :: parens :: "prec"[prec_equal] :: equal{'T; 'a; 'b} =
   szone pushm slot{'a} space `"= " slot{'b} space `"in " slot{'T} popm ezone

(* HACK! - this should be replaced with a proper I/O abstruction *)
dform member_df : except_mode[src] :: parens :: "prec"[prec_equal] :: ('x IN 'T) =
   szone pushm slot{'x} space Nuprl_font!member hspace slot{'T} popm ezone

dform member_df2 : mode[src] :: parens :: "prec"[prec_equal] :: ('x IN 'T) =
   szone pushm slot{'x} space `"IN" hspace slot{'T} popm ezone

dform it_df1 : it = cdot

dform type_df1 : except_mode[src] :: parens :: "prec"[prec_type] :: "type"{'a} =
   slot{'a} " " `"Type"

dform type_df2 : mode[src] :: "type"{'a} =
   `"\"type\"{" slot{'a} `"}"

dform univ_df1 : except_mode[src] :: univ[i:l] =
   mathbbU `"[" slot[i:l] `"]"

dform squash_df : except_mode[src] :: squash = cdot

dform squash_df2 : mode[src] :: squash = `"squash"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * True always holds.
 *)
prim trueIntro {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "true" } =
   it

(*
 * Typehood is equality.
 *)
prim equalityAxiom 'H 'J :
   sequent ['ext] { 'H; x: 'T; 'J['x] >- 'x IN 'T } =
   it

(*
 * Reflexivity.
 *)
prim equalityRef 'H 'y :
   sequent ['ext] { 'H >- 'x = 'y in 'T } -->
   sequent ['ext] { 'H >- 'x IN 'T } =
   it

(*
 * Symettry.
 *)
prim equalitySym 'H :
   sequent ['ext] { 'H >- 'y = 'x in 'T } -->
   sequent ['ext] { 'H >- 'x = 'y in 'T } =
   it

(*
 * Transitivity.
 *)
prim equalityTrans 'H 'z :
   sequent ['ext] { 'H >- 'x = 'z in 'T } -->
   sequent ['ext] { 'H >- 'z = 'y in 'T } -->
   sequent ['ext] { 'H >- 'x = 'y in 'T } =
   it

(*
 * H >- Ui ext a = b in T
 * by equalityFormation T
 *
 * H >- T ext a
 * H >- T ext b
 *)
prim equalityFormation 'H 'T :
   [main] ('a : sequent ['ext] { 'H >- 'T }) -->
   [main] ('b : sequent ['ext] { 'H >- 'T }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   'a = 'b in 'T

(*
 * H >- (a1 = b1 in T1) = (a2 = b2 in T2)
 * by equalityEquality
 *
 * H >- T1 = T2 in Ui
 * H >- a1 = a2 in T1
 * H >- b1 = b2 in T1
 *)
prim equalityEquality {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- 'T1 = 'T2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'T1 } -->
   [wf] sequent [squash] { 'H >- 'b1 = 'b2 in 'T2 } -->
   sequent ['ext] { 'H >- ('a1 = 'b1 in 'T1) = ('a2 = 'b2 in 'T2) in univ[i:l] } =
   it

(*
 * Typehood.
 *)
prim equalityType {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a IN 'T } -->
   [wf] sequent [squash] { 'H >- 'b IN 'T } -->
   sequent ['ext] { 'H >- "type"{. 'a = 'b in 'T } } =
   it

interactive equalityType2 {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a IN 'T } -->
   sequent ['ext] { 'H >- "type"{. 'a IN 'T } }

prim equalityTypeIsType 'H 'a 'b :
   [wf] sequent [squash] { 'H >- 'a = 'b in 'T } -->
   sequent ['ext] { 'H >- "type"{'T} } =
   it

(*
 * H >- it in (a = b in T)
 * by axiomMember
 *
 * H >- a = b in T
 *)
prim axiomMember {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a = 'b in 'T } -->
   sequent ['ext] { 'H >- it IN ('a = 'b in 'T) } =
   it

(*
 * H, x: a = b in T, J[x] >- C[x]
 * by equalityElimination i
 *
 * H, x: a = b in T; J[it] >- C[it]
 *)
prim equalityElimination {| elim_resource [] |} 'H 'J :
   ('t : sequent ['ext] { 'H; x: 'a = 'b in 'T; 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; x: 'a = 'b in 'T; 'J['x] >- 'C['x] } =
   't

(*
 * H >- T = T in type
 * by typeEquality
 *
 * H >- T
 *)
prim typeEquality 'H :
   [main] sequent [squash] { 'H >- 'T } -->
   sequent ['ext] { 'H >- "type"{'T} } =
   it

(*
 * Squash elim.
 *)
prim equality_squashElimination 'H :
   sequent [squash] { 'H >- 'a = 'b in 'T } -->
   sequent ['ext] { 'H >- 'a = 'b in 'T } =
   it

prim type_squashElimination 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent ['ext] { 'H >- "type"{'T} } =
   it

prim rewrite_squashElimination 'H :
   sequent [squash] { 'H >- Perv!"rewrite"{'a; 'b} } -->
   sequent ['ext] { 'H >- Perv!"rewrite"{'a; 'b} } =
   it

(*
 * H >- Uj in Ui
 * by universeMember (side (j < i))
 *
 * Add a tactic later that will automatically
 * unfold the cumulativity.
 *)
prim universeMember 'H :
   sequent ['ext] { 'H >- cumulativity[j:l, i:l] } -->
   sequent ['ext] { 'H >- univ[j:l] IN univ[i:l] } =
  it

(*
 * H >- x = x in Ui
 * by universeCumulativity
 *
 * H >- x = x in Uj
 * H >- cumulativity(j, i)
 *)
prim universeCumulativity 'H univ[j:l] :
   sequent [squash] { 'H >- cumulativity[j:l, i:l] } -->
   sequent [squash] { 'H >- 'x = 'y in univ[j:l] } -->
   sequent ['ext] { 'H >- 'x = 'y in univ[i:l] } =
   it

let univ_member_term = << univ[i:l] IN univ[j:l] >>

let eqcd_univT p =
   let i = Sequent.hyp_count_addr p in
      (universeMember i
       thenT tryT (rw reduce_cumulativity 0 thenT trueIntro i)) p

let eqcd_resource = Mp_resource.improve eqcd_resource (univ_term, eqcd_univT)
let intro_resource = Mp_resource.improve intro_resource (univ_member_term, eqcd_univT)

(*
 * Universe is a type.
 *)
prim universeType {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "type"{univ[l:l]} } =
   it

(*
 * Anything in a universe is a type.
 *)
prim universeMemberType 'H univ[i:l] :
   [wf] sequent [squash] { 'H >- 'x IN univ[i:l] } -->
   sequent ['ext] { 'H >- "type"{'x} } =
   it

let univTypeT t p =
   universeMemberType (Sequent.hyp_count_addr p) t p

(*
 * Derived form for known membership.
 * hypothesis rule is not know yet.
 *)
prim universeAssumType 'H 'J :
   sequent ['ext] { 'H; x: univ[l:l]; 'J['x] >- "type"{'x} } =
   it

(*
 * H >- Ui ext Uj
 * by universeFormation
 *)
prim universeFormation 'H univ[j:l] :
   sequent ['ext] { 'H >- cumulativity[j:l, i:l] } -->
   sequent ['ext] {'H >- univ[i:l] } =
   univ[j:l]

(*
 * Squash from any.
 *)
prim squashFromAny 'H 'ext :
   sequent ['ext] { 'H >- 'T } -->
   sequent [squash] { 'H >- 'T } =
   it

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Infer types from membership and equality.
 *)
let infer_equal subst (so, t) =
   let t, x1, x2 = dest_equal t in
   let subst =
      if is_var_term x1 then
         (dest_var x1, t) :: subst
      else
         subst
   in
      if is_var_term x2 then
         (dest_var x2, t) :: subst
      else
         subst

let typeinf_subst_resource =
   Mp_resource.improve (**)
      typeinf_subst_resource
      (equal_term, infer_equal)

(*
 * Type of a universe is incremented by one.
 *)
let inf_univ _ _ _ eqs opt_eqs defs t =
   let le = dest_univ t in
      eqs, opt_eqs, defs, mk_univ_term (incr_level_exp le)

let typeinf_resource = Mp_resource.improve typeinf_resource (univ_term, inf_univ)

(*
 * Type of an equality is the type of the equality type.
 *)
let equal_type t =
   let ty, _, _ = dest_equal t in ty

let typeinf_resource =
   Mp_resource.improve typeinf_resource (equal_term, Typeinf.infer_map equal_type)

(*
 * Helper functions for universe type inference
 *)

let infer_univ_dep0_dep0 destruct inf consts decls eqs opt_eqs defs t =
   let a, b = destruct t in
   let eqs', opt_eqs', defs', a' = inf consts decls eqs opt_eqs defs a in
   let eqs'', opt_eqs'', defs'', b' = inf consts decls eqs' opt_eqs' defs' b in
   let eqs''', opt_eqs''', subst, a'' = Typeinf.typeinf_final consts eqs'' opt_eqs'' defs'' a' in
   let b'' = apply_subst (apply_subst b' subst) defs in
   let le1 = try_dest_univ a'' in
   let le2 = try_dest_univ b'' in
      eqs''', opt_eqs''', defs'', mk_univ_term (max_level_exp le1 le2 0)

let infer_univ_dep0_dep1 destruct inf consts decls eqs opt_eqs defs t =
   let v, a, b = destruct t in
   let eqs', opt_eqs', defs', a' = inf consts decls eqs opt_eqs defs a in
   let eqs'', opt_eqs'', defs'', b' =
      inf (StringSet.add v consts) ((v,a)::decls) eqs' opt_eqs' defs' b in
   let eqs''', opt_eqs''', subst, a'' = Typeinf.typeinf_final consts eqs'' opt_eqs'' defs'' a' in
   let b'' = apply_subst (apply_subst b' subst) defs in
   let le1 = try_dest_univ a'' in
   let le2 = try_dest_univ b'' in
      eqs''', opt_eqs''', defs'', mk_univ_term (max_level_exp le1 le2 0)

let infer_univ1 = Typeinf.infer_const univ1_term

(************************************************************************
 * SQUASH STABILITY                                                     *
 ************************************************************************)

(*
 * Equality is squash stable.
 *)
let squash_equalT p =
   equality_squashElimination (Sequent.hyp_count_addr p) p

let squash_rewriteT p =
   rewrite_squashElimination (Sequent.hyp_count_addr p) p

let squash_resource = Mp_resource.improve squash_resource (equal_term, squash_equalT)

let squash_typeT p =
   type_squashElimination (Sequent.hyp_count_addr p) p

let squash_resource = Mp_resource.improve squash_resource (type_term, squash_typeT)

let unsquashT v p =
   squashFromAny (Sequent.hyp_count_addr p) v p

(************************************************************************
 * OTHER TACTICS                                                        *
 ************************************************************************)

(*
 * H, x:T, J >- x = x in T
 *)
let equalAssumT i p =
   let i, j = Sequent.hyp_indices p i in
      equalityAxiom i j p

(*
 * Assumed membership.
 *)
let univAssumT i p =
   let j, k = Sequent.hyp_indices p i in
      universeAssumType j k p

(*
 * Automation.
 *
 * let triv_equalT i p =
 *    (equalAssumT i
 *    orelseT univAssumT i) p
 *)
let triv_equalT i p =
   let i, j = Sequent.hyp_indices p i in
   (equalityAxiom i j orelseT universeAssumType i j) p

(*
 * Reflexivity.
 *)
let equalRefT t p =
   equalityRef (Sequent.hyp_count_addr p) t p

(*
 * Symettry.
 *)
let equalSymT p =
   equalitySym (Sequent.hyp_count_addr p) p

(*
 * Transitivity.
 *)
let equalTransT t p =
   equalityTrans (Sequent.hyp_count_addr p) t p

(*
 * Typehood from equality.
 *)
let equalTypeT a b p =
   equalityTypeIsType (Sequent.hyp_count_addr p) a b p

(*
 * Universe cumulativity.
 *)
let cumulativityT u p =
   let i = Sequent.hyp_count_addr p in
      (universeCumulativity i u
       thenLT [tryT (rw reduce_cumulativity 0 thenT trueIntro i); idT]) p

(*
 * Typehood from truth.
 *)
let typeAssertT p =
   typeEquality (Sequent.hyp_count_addr p) p

let trivial_resource =
   Mp_resource.improve trivial_resource (**)
      { auto_name = "triv_equalT";
        auto_prec = trivial_prec;
        auto_tac = onSomeHypT triv_equalT
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
