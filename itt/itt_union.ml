(*
 * Rules for dependent product.
 *
 *)

include Tacticals

include Itt_equal
include Itt_rfun

open Printf
open Debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Resource

open Var
open Sequent
open Tacticals
open Typeinf

open Itt_equal
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_union%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare union{'A; 'B}
declare inl{'x}
declare inr{'x}
declare decide{'x; y. 'a['y]; z. 'b['z]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Reduction on decide.
 * decide(inl x; u. l[u]; v. r[v]) <--> l[x]
 * decide(inr x; u. l[u]; v. r[v]) <--> r[x]
 *)
primrw reduceDecideInl : decide{inl{'x}; u. 'l['u]; v. 'r['v]} <--> 'l['x]
primrw reduceDecideInr : decide{inr{'x}; u. 'l['u]; v. 'r['v]} <--> 'r['x]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_inl
prec prec_union

dform union_df : mode[prl] :: parens :: "prec"[prec_union] :: union{'A; 'B} =
   slot{'A} " " `"+" " " slot{'B}

dform inl_df : mode[prl] :: parens :: "prec"[prec_inl] :: inl{'a} =
   `"inl" " " slot{'a}

dform inr_df : mode[prl] :: parens :: "prec"[prec_inl] :: inr{'a} =
   `"inr" " " slot{'a}

dform decide_df : mode[prl] :: decide{'x; y. 'a; z. 'b} =
   szone pushm[0] pushm[3] `"match" " " slot{'a} " " `"with" hspace
   `"inl " slot{'y} `" -> " slot{'a} popm hspace
   pushm[3] `" | inr " slot{'z} `" -> " slot{'b} popm popm ezone

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext A + B
 * by unionFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
prim unionFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[@i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   'A + 'B

(*
 * H >- A1 + B1 = A2 + B2 in Ui
 * by unionEquality
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
prim unionEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- 'A1 + 'B1 = 'A2 + 'B2 in univ[@i:l] } =
   it

(*
 * H >- A + B ext inl a
 * by inlFormation
 * H >- A
 * H >- B = B in Ui
 *)
prim inlFormation 'H :
   ('a : sequent ['ext] { 'H >- 'A }) -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- 'A + 'B } =
   inl{'a}

(*
 * H >- A + B ext inl a
 * by inrFormation
 * H >- B
 * H >- A = A in Ui
 *)
prim inrFormation 'H :
   ('b : sequent ['ext] { 'H >- 'B }) -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- 'A + 'B } =
   inr{'b}

(*
 * H >- inl a1 = inl a2 in A + B
 * by inlEquality
 * H >- a1 = a2 in A
 * H >- B = B in Ui
 *)
prim inlEquality 'H :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- inl{'a1} = inl{'a2} in 'A + 'B } =
   it

(*
 * H >- inr b1 = inr b2 in A + B
 * by inrEquality
 * H >- b1 = b2 in B
 * H >- A = A in Ui
 *)
prim inrEquality 'H :
   sequent [squash] { 'H >- 'b1 = 'b2 in 'B } -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- inr{'b1} = inr{'b2} in 'A + 'B } =
   it

(*
 * H, x: A + B, J[x] >- T[x] ext decide(x; u. 'left['u]; v. 'right['v])
 * by unionElimination x u v
 * H, x: A # B, u:A, v:B[u], J[u, v] >- T[u, v] ext t[u, v]
 *)
prim unionElimination 'H 'J 'x 'u 'v :
   ('left['u] : sequent ['ext] { 'H; x: 'A + 'B; u: 'A; 'J[inl{'u}] >- 'T[inl{'u}] }) -->
   ('right['u] : sequent ['ext] { 'H; x: 'A + 'B; v: 'B; 'J[inr{'v}] >- 'T[inr{'v}] }) -->
   sequent ['ext] { 'H; x: 'A + 'B; 'J['x] >- 'T['x] } =
   decide{'x; u. 'left['u]; v. 'right['v]}

(*
 * H >- decide(e1; u1. l1[u1]; v1. r1[v1]) = decide(e2; u2. l2[u2]; v2. r2[v2]) in T[e1]
 * by unionEquality lambda(z. T[z]) (A + B) u v w
 * H >- e1 = e2 in A + B
 * H, u:A, w: e1 = inl u in A + B >- l1[u] = l2[u] in T[inl{u}]
 * H, v:A, w: e1 = inr v in A + B >- r1[v] = r2[v] in T[inr{v}]
 *)
prim decideEquality 'H lambda{z. 'T['z]} ('A + 'B) 'u 'v 'w :
   sequent [squash] { 'H >- 'e1 = 'e2 in 'A + 'B } -->
   sequent [squash] { 'H; u: 'A; w: 'e1 = inl{'u} in 'A + 'B >- 'l1['u] = 'l2['u] in 'T[inl{'u}] } -->
   sequent [squash] { 'H; v: 'B; w: 'e1 = inr{'v} in 'A + 'B >- 'r1['v] = 'r2['v] in 'T[inr{'v}] } -->
   sequent ['ext] { 'H >- decide{'e1; u1. 'l1['u1]; v1. 'r1['v1]} =
                   decide{'e2; u2. 'l2['u2]; v2. 'r2['v2]} in
                   'T['e1] } =
   it

(*
 * H >- A1 + B1 <= A2 + B2
 * by unionSubtype
 *
 * H >- A1 <= A2
 * H >- B1 <= B2
 *)
prim unionSubtype 'H :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H >- subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- subtype{ ('A1 + 'B1); ('A2 + 'B2) } } =
   it

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let union_term = << 'A + 'B >>
let union_opname = opname_of_term union_term
let is_union_term = is_dep0_dep0_term union_opname
let dest_union = dest_dep0_dep0_term union_opname
let mk_union_term = mk_dep0_dep0_term union_opname

let inl_term = << inl{'x} >>
let inl_opname = opname_of_term inl_term
let is_inl_term = is_dep0_term inl_opname
let dest_inl = dest_dep0_term inl_opname
let mk_inl_term = mk_dep0_term inl_opname

let inr_term = << inr{'x} >>
let inr_opname = opname_of_term inr_term
let is_inr_term = is_dep0_term inr_opname
let dest_inr = dest_dep0_term inr_opname
let mk_inr_term = mk_dep0_term inr_opname

let decide_term = << decide{'x; y. 'a['y]; z. 'b['z]} >>
let decide_opname = opname_of_term decide_term
let is_decide_term = is_dep0_dep1_dep1_term decide_opname
let dest_decide = dest_dep0_dep1_dep1_term decide_opname
let mk_decide_term = mk_dep0_dep1_dep1_term decide_opname

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * D the conclusion.
 *)
let d_concl_union p =
   let count = hyp_count p in
   let flag =
      try get_sel_arg p with
         Not_found ->
            raise (RefineError ("d_concl_union", StringError "requires a flag"))
   in
   let tac =
      match flag with
         1 ->
            inlFormation
       | 2 ->
            inrFormation
       | _ ->
            raise (RefineError ("d_concl_union", StringError "select either 1 or 2"))
   in
      (tac count thenLT [idT; addHiddenLabelT "wf"]) p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_union i p =
   let count = hyp_count p in
   let z, _ = Sequent.nth_hyp p i in
   let i, j = hyp_indices p i in
      (match maybe_new_vars [z; z] (declared_vars p) with
          [u; v] ->
             unionElimination i j z u v
        | _ ->
             failT) p

(*
 * Join them.
 *)
let d_unionT i =
   if i = 0 then
      d_concl_union
   else
      d_hyp_union i

let d_resource = d_resource.resource_improve d_resource (union_term, d_unionT)

(************************************************************************
 * EQCD TACTIC                                                          *
 ************************************************************************)

(*
 * EQCD union.
 *)
let eqcd_unionT p =
   let count = hyp_count p in
      (unionEquality count
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (union_term, eqcd_unionT)

(*
 * EQCD inl.
 *)
let eqcd_inlT p =
   let count = hyp_count p in
      (inlEquality count
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (inl_term, eqcd_inlT)

(*
 * EQCD inr.
 *)
let eqcd_inrT p =
   let count = hyp_count p in
      (inrEquality count
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (inr_term, eqcd_inrT)

(*
 * EQCD decide.
 *)
let eqcd_decideT p =
   raise (RefineError ("eqcd_decideT", StringError "not implemented"))

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (decide_term, eqcd_decideT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of disjoint union.
 *)
let inf_union f decl t =
   let a, b = dest_union t in
   let decl', a' = f decl a in
   let decl'', b' = f decl' b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (union_term, inf_union)

(*
 * Type of inl.
 *)
let inf_inl f decl t =
   let a = dest_inl t in
   let decl', a' = f decl a in
      decl', mk_union_term a' (mk_var_term (maybe_new_var "T" (List.map fst decl')))

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (inl_term, inf_inl)

(*
 * Type of inr.
 *)
let inf_inr f decl t =
   let a = dest_inr t in
   let decl', a' = f decl a in
      decl', mk_union_term (mk_var_term (maybe_new_var "T" (List.map fst decl'))) a'

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (inr_term, inf_inr)

(*
 * Type of decide.
 *)
let inf_decide (inf : typeinf_func) (decl : term_subst) (t : term) =
   let e, x, a, y, b = dest_decide t in
   let decl', e' = inf decl e in
   let l, r = dest_union e' in
   let decl'', a' = inf ((x, l)::decl') a in
   let decl''', b' = inf ((y, l)::decl'') b in
      unify decl''' a' b', a'

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (decide_term, inf_decide)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two union types.
 *)
let union_subtypeT p =
   (unionSubtype (hyp_count p)
    thenT addHiddenLabelT "subtype") p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (DSubtype ([<< 'A1 + 'B1 >>, << 'A2 + 'B2 >>;
               << 'A1 >>, << 'A2 >>;
               << 'B1 >>, << 'B2 >>],
              union_subtypeT))

(*
 * $Log$
 * Revision 1.14  1998/07/02 18:38:01  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.13  1998/07/01 04:37:53  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.12  1998/06/22 19:46:29  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.11  1998/06/16 16:26:13  jyh
 * Added itt_test.
 *
 * Revision 1.10  1998/06/15 22:33:38  jyh
 * Added CZF.
 *
 * Revision 1.9  1998/06/12 13:47:43  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.8  1998/06/09 20:52:48  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
 * Revision 1.7  1998/06/01 13:56:29  jyh
 * Proving twice one is two.
 *
 * Revision 1.6  1998/05/28 13:48:18  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.5  1998/04/24 02:43:53  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.4  1998/04/22 22:45:23  jyh
 * *** empty log message ***
 *
 * Revision 1.3  1998/04/09 18:26:10  jyh
 * Working compiler once again.
 *
 * Revision 1.2  1997/08/06 16:18:46  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:30  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.3  1996/10/23 15:18:13  jyh
 * First working version of dT tactic.
 *
 * Revision 1.2  1996/05/21 02:17:27  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.1  1996/03/28 02:51:35  jyh
 * This is an initial version of the type theory.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
