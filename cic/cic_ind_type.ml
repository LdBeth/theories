extends Cic_lambda
open Cic_lambda

open Lm_printf

open Basic_tactics

prim collapse_base {| intro [] |} :
	sequent { <H> >- 'C } -->
	sequent { <H> >- sequent { >- 'C } } = it

prim collapse_step {| intro [] |} :
	sequent { <H>; x:'T >- sequent { <J['x]> >- 'C['x] } } -->
	sequent { <H> >- sequent { x: 'T; <J['x]> >- 'C['x] } } = it

let collapseT = (repeatT collapse_step) thenT collapse_base

(*********************************************
 *         INDUCTIVE DEFINITIONS PART        *
**********************************************)

(* Coq's Ind(H)[Hp](Hi:=Hc) - inductive definition *)
declare IndTypes    (* for ind.defenitions, Hi - new types, defenitions of new types *)
declare IndParams (* for ind. defenirions, Hp - parameters of ind. defenition *)
declare IndConstrs (* for ind. defenitions, Hc - constructors *)

(*
 * These sequent args are used to state the well-formedness
 * of an inductive definition. We need them to distinguish WF
 * judgements from other uses of inductive definitions in order
 * to make indCarryOut inapplicable to WF judgements.
 *)
declare IndTypesWF
declare IndParamsWF
declare IndConstrsWF

(* declaration of a multiple product, i.e. (p1:P1)(p2:P2)...(pr:Pr)T *)
declare prodH     (*{ <H> >- 'T }*)

(*********************************************
 *         DISPLAY FORMS                     *
**********************************************)

declare display_sequent{'s}
declare display_hyp{v. 'e}
declare display_concl{'e}
declare display_hyps{'s}
declare display_hyps_emph{'s}

(*
 * Generic sequent printers
 *)

dform display_hyps_emph_df : display_hyps_emph{'s} =
	`"|" display_hyps{'s} `"|"

dform display_hyps_nil_df : display_hyps{sequent ['arg] { >- 'e }} =
	`""

dform display_hyps_cons_df : display_hyps{sequent ['arg] { x: 't; <H> >- 'e }} =
   display_hyp{x. 't} `"," hspace display_hyps{sequent ['arg] { <H> >- 'e }}

dform display_hyps_cons_df : display_hyps{sequent ['arg] { x: 't >- 'e }} =
   display_hyp{x. 't} display_hyps{sequent ['arg] { >- 'e }}

(*
 * Strip sequent_args if necessary.
 * Note, you can always override this by defining a more specific display form.
 *)

dform display_concl_df : display_concl{sequent ['arg] { <H> >- 'e<||> } } =
	slot{'e}

dform context_hyp_df : display_hyp{x. df_context{'c}} =
   df_context{'c}

dform display_hyp_df : display_hyp{x. 't[]} =
	slot{'x} `": " slot{'t}

dform prodH_df : except_mode[src] :: sequent [prodH] { <H> >- 'e } =
	math_fun{ display_hyps_emph{sequent [prodH] { <H> >- 'e }} ;
		display_concl{sequent [prodH] { <H> >- 'e }} }

dform ind_df : except_mode[src] ::
	sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi<| |> > >-
		   sequent [IndConstrs] { <Hc<| |> > >- 't<||> }}} =
	`"Ind[" display_hyps{sequent [IndParams]{ <Hp> >- 't<||> }} `"]("
		display_hyps{ sequent [IndTypes]{ <Hi> >- 't<||> }} `" := "
			display_hyps{ sequent [IndConstrs]{ <Hc> >- 't<||> }} `")" slot{'t}

dform indWF_df : except_mode[src] ::
	sequent [IndParamsWF] { <Hp> >-
	   sequent [IndTypesWF] { <Hi<| |> > >-
		   sequent [IndConstrsWF] { <Hc<| |> > >- it }}} =
	`"WF{ Ind[" display_hyps{sequent [IndParamsWF]{ <Hp> >- it }} `"]("
		display_hyps{ sequent [IndTypesWF]{ <Hi> >- it }} `" := "
			display_hyps{ sequent [IndConstrsWF]{ <Hc> >- it }} `") }"

(****************************************************************************
*                END OF DISPLAY FORMS DEFINITION                            *
*****************************************************************************)

(* inductive definition of multiple product *)
prim_rw prodH_base :
   sequent [prodH] { >- 'S } <--> 'S

prim_rw prodH_step :
   sequent [prodH] { <H>; x:'T >- 'S['x] } <-->
	sequent [prodH] { <H> >- x:'T -> 'S['x] }

let fold_prodH_base = makeFoldC <<sequent [prodH] { >- 'S }>> prodH_base
let fold_prodH_step0 = makeFoldC <<sequent [prodH] { <H>; x:'T >- 'S['x] }>> prodH_step
let fold_prodH_step = (higherC unfold_funC) thenC fold_prodH_step0

let fold_prodH = fold_prodH_base thenC (repeatC fold_prodH_step)
(*
let conclAddrC conv = termC (fun t -> (addrLiteralC (nth_concl_addr t 1) conv))

let indHeadAddrC conv = conclAddrC (conclAddrC (conclAddrC conv))
*)
(* base axioms about Ind and IndTypes *)
(* for new types *)
prim_rw indSubstDef 'Hi :
   sequent [IndParams] { <Hp> >-
	   (sequent [IndTypes] { <Hi>; x:'T<|Hp|>; <Ji<|Hp|> > >-
		   (sequent [IndConstrs] { <Hc['x]> >- 't['x]})})} <-->
   sequent [IndParams] { <Hp> >-
	   (sequent [IndTypes] { <Hi>; x1:'T<|Hp|>; <Ji<|Hp|> > >-
		   (sequent [IndConstrs] { <Hc['x1]> >-
			   't[sequent [IndParams] { <Hp> >-
				   (sequent [IndTypes] { <Hi>; x:'T<|Hp|>; <Ji<|Hp|> > >-
				      sequent [IndConstrs] { <Hc['x]> >- 'x}})}] })})}

interactive_rw indFoldDef 'Hi bind{x.'t['x]} :
   sequent [IndParams] { <Hp> >-
	   (sequent [IndTypes] { <Hi>; x1:'T<|Hp|>; <Ji<|Hp|> > >-
		   (sequent [IndConstrs] { <Hc['x1]> >-
			   't[sequent [IndParams] { <Hp> >-
				   (sequent [IndTypes] { <Hi>; x:'T<|Hp|>; <Ji<|Hp|> > >-
				      sequent [IndConstrs] { <Hc['x]> >- 'x}})}] })})} <-->
	sequent [IndParams] { <Hp> >-
	   (sequent [IndTypes] { <Hi>; x:'T<|Hp|>; <Ji<|Hp|> > >-
		   (sequent [IndConstrs] { <Hc['x]> >- 't['x]})})}

(* Returns sequent conclusion as a term, fails if there is more than one conclusion *)
let seq_concl seq =
   match SeqGoal.to_list (TermMan.explode_sequent seq).sequent_goals with
      [ t ] ->
			t
      | _ ->
         raise (Invalid_argument (sprintf "Cic_ind_type.seq_concl: only one goal is supported"))

(* Being applied to a inductive definition (3 nested sequents),
   it returns the term defined in the context of that inductive definition,
	i.e. conclusion of the third nested sequent.

	Let's call such this term the _head_ of the inductive definition, i.e.
	what this particular occurance of inductive definition means/defines.
 *)
let ind_head seq =
	seq_concl (seq_concl (seq_concl seq))

(* seq    - an inductive definition
   def    - inductive type definied via the same inductive definition,
				"def" is assumed to occur in the head of "seq"
	unfold - rewrite that unfolds def (into an explicit inductive definition)
	n      - position of def's definition in the inductive types' definitions
	indFoldDefAuxC first unfolds "def" using "unfold" and then removes inner
				inductive definition (appeared because of "unfold") redirecting
				all occurances of def-representing variable to the outer inductive definition
*)
let indFoldDefAuxC n def unfold seq =
	let target = ind_head seq in
	let bind = var_subst_to_bind target def in
	unfold thenC (indFoldDef n bind)

(* indFoldDefC does the same thing as indFoldDefAuxC but automatically extracts the last argument *)
let indFoldDefC n def unfold = termC (indFoldDefAuxC n def unfold)
let indFoldHDefC n def unfold = indFoldDefC n def (higherC unfold)

(* for constructors (names, types) *)
prim_rw indSubstConstr 'Hc :
   sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi> >-
		   sequent [IndConstrs] { <Hc>; c:'C<|Hi;Hp|>; < Jc<|Hi;Hp|> > >- 't['c]}}} <-->
   sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi> >-
		   sequent [IndConstrs] { <Hc>; c1:'C<|Hi; Hp|>; < Jc<|Hi; Hp|> > >-
				't[ sequent [IndParams] { <Hp> >-
				   sequent [IndTypes] { <Hi> >-
				      sequent [IndConstrs] { <Hc>; c:'C<|Hi; Hp|>; < Jc<|Hi; Hp|> > >- 'c}}}]}}}

interactive_rw indFoldConstr 'Hc bind{x.'t['x]} :
   sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi> >-
		   sequent [IndConstrs] { <Hc>; c1:'C<|Hi; Hp|>; < Jc<|Hi; Hp|> > >-
				't[ sequent [IndParams] { <Hp> >-
				   sequent [IndTypes] { <Hi> >-
				      sequent [IndConstrs] { <Hc>; c:'C<|Hi; Hp|>; < Jc<|Hi; Hp|> > >- 'c}}}]}}} <-->
	sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi> >-
		   sequent [IndConstrs] { <Hc>; c:'C<|Hi;Hp|>; < Jc<|Hi;Hp|> > >- 't['c]}}}

let indFoldConstrAuxC n constr unfold seq =
	let target = ind_head seq in
	let bind = var_subst_to_bind target constr in
	unfold thenC (indFoldConstr n bind)

let indFoldConstrC n constr unfold = termC (indFoldConstrAuxC n constr unfold)
let indFoldHConstrC n constr unfold = indFoldConstrC n constr (higherC unfold)

(* carry out ground terms from the Ind *)
prim_rw indCarryOut :
   sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi> >-
	      sequent [IndConstrs] { <Hc> >- 't<||> } } } <-->
	't<||>

interactive_rw indWrap
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi> >-
				sequent [IndConstrs] { <Hc> >- 'aux } } } :
	't <-->
   sequent [IndParams] { <Hp> >-
	   sequent [IndTypes] { <Hi> >-
	      sequent [IndConstrs] { <Hc> >- 't<||> } } }

let indWrapC def cnv = funC (fun e ->
	let p = env_arg e in
	let def' = Top_conversionals.apply_rewrite p cnv def in
	indWrap def'
)

(* implementation of the first part of the Coq's Ind-Const rule *)
prim ind_ConstDef 'Hi :
   sequent { <H> >-
	   sequent [IndParamsWF] { <Hp> >-
			sequent [IndTypesWF] { <Hi>; I:'A<|Hp;H|>; <Ji<|Hp;H|> > >-
				sequent [IndConstrsWF] { <Hc['I]> >- it }}} }  -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I:'A<|Hp;H|>; <Ji<|Hp;H|> > >-
				sequent [IndConstrs] { <Hc['I]> >- 'I } } }
		in	sequent [prodH] { <Hp> >- 'A} } = it

(* declaration of a multiple application, i.e. (...((Ip1)p2)p3...)pr *)
declare applH (* { <H> >- 'T } *)

dform applH_df : except_mode[src] :: sequent [applH] { <H> >- 'e } =
	display_concl{sequent [applH] { <H> >- 'e }} display_hyps_emph{sequent [applH] { <H> >- 'e }}


(*inductive definition of multiple application *)
prim_rw applHBase {| reduce |} :
   sequent [applH] { >- 'S } <-->
	'S

prim_rw applHStep {| reduce |} :
   sequent [applH] { x:'T; <H> >- 'S } <-->
	sequent [applH] { <H> >- apply{'S;'T}}

let fold_applHBase = makeFoldC <<sequent [applH] { >- 'S }>> applHBase
let fold_applHStep = makeFoldC <<sequent [applH] { x:'T; <H> >- 'S }>> applHStep
let fold_applH = fold_applHBase thenC (repeatC fold_applHStep)

(* declaration of multiple substitution C[I/(I p1)...pn] *)
declare IndParamsSubst
declare IndTypesSubst
declare IndConstrsSubst
declare IndParamsSubstAux
declare IndTypesSubstAux
declare Aux
declare IndConstrsSubstAux
declare IndParamsSubstApp
declare IndTypesSubstApp
declare IndConstrsSubstApp
declare IndParamsSubstAppAux
declare IndTypesSubstAppAux
declare IndConstrsSubstAppAux
declare IndParamsSubstProd
declare IndTypesSubstProd
declare IndConstrsSubstProd

dform indSubst_df : except_mode[src] ::
	sequent [IndParamsSubst] { <Hp> >-
	   sequent [IndTypesSubst] { <Hi<| |> > >-
		   sequent [IndConstrsSubst] { <Hc<| |> > >- 't<||> }}} =
	`"Subst[" display_hyps{sequent [IndParamsSubst]{ <Hp> >- 't<||> }} `"]("
		display_hyps{ sequent [IndTypesSubst]{ <Hi> >- 't<||> }} `" := "
			display_hyps{ sequent [IndConstrsSubst]{ <Hc> >- 't<||> }} `")" slot{'t}

dform indSubstAux_df : except_mode[src] ::
	sequent [IndParamsSubstAux] { <Hp> >-
	   sequent [IndTypesSubstAux] { <Hi<| |> > >-
			sequent { <Ji> >-
				sequent [IndConstrsSubstAux] { <Hc<| |> > >- 't<||> }}}} =
	`"SubstAux[" display_hyps{sequent [IndParamsSubstAux]{ <Hp> >- 't<||> }} `"]("
		display_hyps{ sequent [IndTypesSubstAux]{ <Hi> >- 't<||> }} `" | "
			display_hyps{ sequent [Aux] { <Ji> >- it}}  `" := "
				display_hyps{ sequent [IndConstrsSubstAux]{ <Hc> >- 't<||> }} `")" slot{'t}

dform indSubstApp_df : except_mode[src] ::
	sequent [IndParamsSubstApp] { <Hp> >-
	   sequent [IndTypesSubstApp] { <Hi<| |> > >-
			sequent { <Ji> >-
				sequent [IndConstrsSubstApp] { <Hc<| |> > >- 't<||> }}}} =
	`"SubstApp[" display_hyps{sequent [IndParamsSubstApp]{ <Hp> >- 't<||> }} `"]("
		display_hyps{ sequent [IndTypesSubstApp]{ <Hi> >- 't<||> }} `" | "
			display_hyps{ sequent [Aux] { <Ji> >- it}}  `" := "
				display_hyps{ sequent [IndConstrsSubstApp]{ <Hc> >- 't<||> }} `")" slot{'t}

dform indSubstAppAux_df : except_mode[src] ::
	sequent [IndParamsSubstAppAux] { <Hp> >-
		sequent { <Jp> >-
			sequent [IndTypesSubstAppAux] { <Hi<| |> > >-
				sequent { <Ji> >-
					sequent [IndConstrsSubstAppAux] { <Hc<| |> > >- 't<||> }}}}} =
	`"SubstAppAux[" display_hyps{sequent [IndParamsSubstAppAux]{ <Hp> >- 't<||> }} `" | "
		display_hyps{ sequent [Aux] { <Jp> >- it}} `"]("
			display_hyps{ sequent [IndTypesSubstAppAux]{ <Hi> >- 't<||> }} `" | "
				display_hyps{ sequent [Aux] { <Ji> >- it}}  `" := "
					display_hyps{ sequent [IndConstrsSubstAppAux]{ <Hc> >- 't<||> }} `")" slot{'t}

prim_rw substStart {| reduce |} :
   sequent [IndParamsSubst] { <Hp> >-
	   sequent [IndTypesSubst] { <Hi> >-
         sequent [IndConstrsSubst] { <Hc> >- 'c in 'C } } } <-->
   sequent [IndParamsSubstAux] { <Hp> >-
	   sequent [IndTypesSubstAux] { <Hi> >-
			sequent { >-
				sequent [IndConstrsSubstAux] { <Hc> >- 'c in 'C } } } }

let fold_substStart = makeFoldC
	<<sequent [IndParamsSubst] { <Hp> >-
	   sequent [IndTypesSubst] { <Hi> >-
         sequent [IndConstrsSubst] { <Hc> >- 'c in 'C } } }>> substStart

prim_rw substStep {| reduce |} :
	sequent [IndParamsSubstAux] { <Hp> >-
	   sequent [IndTypesSubstAux] { <Hi>; I: 'A >-
			sequent { <Ji> >-
				sequent [IndConstrsSubstAux] { <Hc['I]> >- 'c in 'C['I] } } } } <-->
	sequent [IndParamsSubstApp] { <Hp> >-
	   sequent [IndTypesSubstApp] { <Hi> >-
			sequent { I: 'A; <Ji> >-
				sequent [IndConstrsSubstApp] { <Hc['I]> >- 'c in 'C['I] } } } }

let fold_substStep = makeFoldC
	<<sequent [IndParamsSubstAux] { <Hp> >-
	   sequent [IndTypesSubstAux] { <Hi>; I: 'A >-
			sequent { <Ji> >-
				sequent [IndConstrsSubstAux] { <Hc['I]> >- 'c in 'C['I] } } } }>> substStep

prim_rw substProdStart {| reduce |} :
	sequent [IndParamsSubstAux] { <Hp> >-
	   sequent [IndTypesSubstAux] { >-
			sequent { <Ji> >-
				sequent [IndConstrsSubstAux] { <Hc> >- 'c in 'C } } } } <-->
	sequent [IndParamsSubstProd] { <Hp> >-
		sequent { >-
			sequent [IndTypesSubstProd] { <Ji> >-
				sequent [IndConstrsSubstProd] { <Hc> >- 'c in 'C } } } }

let fold_substProdStart = makeFoldC
	<<sequent [IndParamsSubstAux] { <Hp> >-
	   sequent [IndTypesSubstAux] { >-
			sequent { <Ji> >-
				sequent [IndConstrsSubstAux] { <Hc> >- 'c in 'C } } } }>> substProdStart

prim_rw substProdStep {| reduce |} :
	sequent [IndParamsSubstProd] { <Hp>; p: 'P >-
		sequent { <Jp['p]> >-
			sequent [IndTypesSubstProd] { <Hi['p]> >-
				sequent [IndConstrsSubstProd] { <Hc['p]> >- 'c in 'C['p] } } } } <-->
	sequent [IndParamsSubstProd] { <Hp> >-
		sequent { p: 'P; <Jp['p]> >-
			sequent [IndTypesSubstProd] { <Hi['p]> >-
				sequent [IndConstrsSubstProd] { <Hc['p]> >- 'c in (q:'P -> 'C['q]) } } } }

let fold_substProdStep = makeFoldC
	<<sequent [IndParamsSubstProd] { <Hp>; p: 'P >-
		sequent { <Jp['p]> >-
			sequent [IndTypesSubstProd] { <Hi['p]> >-
				sequent [IndConstrsSubstProd] { <Hc['p]> >- 'c in 'C['p] } } } }>> substProdStep

prim_rw substFinal {| reduce |} :
	sequent [IndParamsSubstProd] { >-
		sequent { <Jp> >-
			sequent [IndTypesSubstProd] { <Hi> >-
				sequent [IndConstrsSubstProd] { <Hc> >- 'c in 'C } } } } <-->
	sequent [IndParams] { <Jp> >-
	   sequent [IndTypes] { <Hi> >-
			sequent [IndConstrs] { <Hc> >- 'c in 'C } } }

let fold_substFinal = makeFoldC
	<<sequent [IndParamsSubstProd] { >-
		sequent { <Jp> >-
			sequent [IndTypesSubstProd] { <Hi> >-
				sequent [IndConstrsSubstProd] { <Hc> >- 'c in 'C } } } }>> substFinal

prim_rw appStart {| reduce |} :
	sequent [IndParamsSubstApp] { <Hp> >-
	   sequent [IndTypesSubstApp] { <Hi> >-
			sequent { <Ji> >-
				sequent [IndConstrsSubstApp] { <Hc> >- 'c in 'C } } } } <-->
	sequent [IndParamsSubstAppAux] { <Hp> >-
		sequent { >-
			sequent [IndTypesSubstAppAux] { <Hi> >-
				sequent { <Ji> >-
					sequent [IndConstrsSubstAppAux] { <Hc> >- 'c in 'C } } } } }

let fold_appStart = makeFoldC
	<<sequent [IndParamsSubstApp] { <Hp> >-
	   sequent [IndTypesSubstApp] { <Hi> >-
			sequent { <Ji> >-
				sequent [IndConstrsSubstApp] { <Hc> >- 'c in 'C } } } }>> appStart

prim_rw appStep {| reduce |} :
	sequent [IndParamsSubstAppAux] { <Hp>; p: 'P >-
		sequent { <Jp['p]> >-
			sequent [IndTypesSubstAppAux] { <Hi['p]> >-
				sequent { I: 'A['p]; <Ji['p]> >-
					sequent [IndConstrsSubstAppAux] { <Hc['I;'p]> >- 'c in 'C['I;'p] } } } } } <-->
	sequent [IndParamsSubstAppAux] { <Hp> >-
		sequent { p: 'P; <Jp['p]> >-
			sequent [IndTypesSubstAppAux] { <Hi['p]> >-
				sequent { I: 'A['p]; <Ji['p]> >-
					sequent [IndConstrsSubstAppAux] { <Hc['I;'p]> >- 'c in 'C[('I 'p);'p] } } } } }

interactive_rw fold_appStep bind{i,p.'C['i;'p]} :
	sequent [IndParamsSubstAppAux] { <Hp> >-
		sequent { p: 'P; <Jp['p]> >-
			sequent [IndTypesSubstAppAux] { <Hi['p]> >-
				sequent { I: 'A['p]; <Ji['p]> >-
					sequent [IndConstrsSubstAppAux] { <Hc['I;'p]> >- 'c in 'C[('I 'p);'p] } } } } } <-->
	sequent [IndParamsSubstAppAux] { <Hp>; p: 'P >-
		sequent { <Jp['p]> >-
			sequent [IndTypesSubstAppAux] { <Hi['p]> >-
				sequent { I: 'A['p]; <Ji['p]> >-
					sequent [IndConstrsSubstAppAux] { <Hc['I;'p]> >- 'c in 'C['I;'p] } } } } }

let fold_appStepAuxC seq =
	let first = seq_concl seq in
	let intermed = seq_concl (seq_concl first) in
	let head = seq_concl (seq_concl (intermed)) in
	let el,ty = two_subterms head in
	let defvar = mk_var_term (TermMan.nth_binding intermed 1) in
	let param = mk_var_term (TermMan.nth_binding first 1) in
	let appl = mk_apply_term defvar param in
	let bind = var_subst_to_bind2 ty appl param in
	fold_appStep bind

let fold_appStepC = termC fold_appStepAuxC

prim_rw appFinal {| reduce |} :
	sequent [IndParamsSubstAppAux] { >-
		sequent { <Jp> >-
			sequent [IndTypesSubstAppAux] { <Hi> >-
				sequent { <Ji> >-
					sequent [IndConstrsSubstAppAux] { <Hc> >- 'c in 'C } } } } } <-->
	sequent [IndParamsSubstAux] { <Jp> >-
		sequent [IndTypesSubstAux] { <Hi> >-
			sequent { <Ji> >-
				sequent [IndConstrsSubstAux] { <Hc> >- 'c in 'C } } } }

let fold_appFinalC = makeFoldC
	<<sequent [IndParamsSubstAppAux] { >-
		sequent { <Jp> >-
			sequent [IndTypesSubstAppAux] { <Hi> >-
				sequent { <Ji> >-
					sequent [IndConstrsSubstAppAux] { <Hc> >- 'c in 'C } } } } }>> appFinal
(*
interactive_rw fold_appFinal :
	sequent [IndParamsSubstAux] { <Jp> >-
		sequent [IndTypesSubstAux] { <Hi> >-
			sequent { <Ji> >-
				sequent [IndConstrsSubstAux] { <Hc> >- 'c in 'C } } } } <-->
	sequent [IndParamsSubstAppAux] { >-
		sequent { <Jp> >-
			sequent [IndTypesSubstAppAux] { <Hi> >-
				sequent { <Ji> >-
					sequent [IndConstrsSubstAppAux] { <Hc> >- 'c in 'C } } } } }

let fold_appFinalC = fold_appFinal
*)

let fold_substApp = fold_appFinalC thenC (repeatC fold_appStepC) thenC fold_appStart

let fold_substProd = fold_substFinal thenC (repeatC fold_substProdStep) thenC fold_substProdStart

let fold_subst = fold_substProd thenC
						(repeatC (fold_substApp thenC fold_substStep)) thenC
						fold_substStart

(* implementation of the second part of the Coq's Ind-Const rule *)
prim ind_ConstConstrs 'Hc :
   sequent { <H> >-
	   sequent [IndParamsWF] { <Hp> >-
		   sequent [IndTypesWF] { <Hi> >-
	         sequent [IndConstrsWF] { <Hc>; c:'C<|Hi;Hp;H|>; <Jc<|Hi;Hp;H|>['c]> >- it } }}}   -->
	sequent { <H> >-
	   sequent [IndParamsSubst] { <Hp> >-
		   sequent [IndTypesSubst] { <Hi> >-
	         sequent [IndConstrsSubst] { <Hc>; c:'C<|Hi;Hp;H|>; <Jc<|Hi;Hp;H|>['c]> >-
				   'c in 'C } } } } = it


(*******************************************************************************************
 *  in the next part the conditions for the W-Ind rule and the W-Ind rule are implemented  *
 *******************************************************************************************)

declare of_some_sort (* { <T> } *) (* any element of T is a type of some sort (Set, Prop or Type[i]) *)

(* declaration of 'arity of sort' notion *)
declare arity_of_some_sort_m (* (<Hi> >- <S>)*) (* Hi={I1:A1,...,Ik:Ak}, S={s1,...,sk},
                                            Aj is an arity of sort sj, j=1,...,k*)
declare arity_of_some_sort{'T} (* type T is an arity of some sort *)

dform arity_of_some_sort_df : arity_of_some_sort{'t} = `"arity_of_some_sort{" slot{'t} `"}"

dform arity_of_some_sort_m_df : sequent [arity_of_some_sort_m] { <T1> >- arity_of_some_sort_m} =
	`"arity_of_some_sort_m{" display_hyps{ sequent [arity_of_some_sort_m] { <T1> >-
			arity_of_some_sort_m}} `"}"

dform of_some_sort_df : of_some_sort{'t} = `"of_some_sort{" slot{'t} `"}"

prim arity_of_some_sort_Set {| intro [] |} :
   sequent { <H> >- arity_of_some_sort{Set} } = it

prim arity_of_some_sort_Prop {| intro [] |} :
	sequent { <H> >- arity_of_some_sort{Prop} } = it

prim arity_of_some_sort_Type {| intro [] |} :
   sequent { <H> >- arity_of_some_sort{"type"[i:l]} } = it

prim arity_of_some_sort_prod {| intro [] |} bind{x.'U['x]} :
   sequent { <H>; x:'T1 >- arity_of_some_sort{'U['x]} } -->
	sequent { <H> >- arity_of_some_sort{ (x:'T1 -> 'U['x])} } = it

prim arity_of_some_sort_m_base {| intro [] |} :
   sequent { <H> >- sequent [arity_of_some_sort_m] { >- arity_of_some_sort_m } } = it

prim arity_of_some_sort_m_step {| intro [] |} :
   sequent { <H> >- arity_of_some_sort{'T} } -->
	sequent { <H> >- sequent [arity_of_some_sort_m] { <T1> >- arity_of_some_sort_m} } -->
   sequent { <H> >- sequent [arity_of_some_sort_m] { <T1>; t:'T<||> >- arity_of_some_sort_m } } = it

declare arity_of_sort{'T;'s} (* type T is an arity of sort 's *)

dform arity_of_sort_df : arity_of_sort{'T;'s} =
	`"arity_of_sort{" slot{'T} `";" slot{'s} `"}"

prim arity_of_sort_Set {| intro [] |} :
   sequent { <H> >- arity_of_sort{Set;Set} } = it

prim arity_of_sort_Prop {| intro [] |} :
   sequent { <H> >- arity_of_sort{Prop;Prop} } = it

prim arity_of_sort_Type {| intro [] |} :
   sequent { <H> >- arity_of_sort{"type"[i:l];"type"[i:l]} } = it

prim arity_of_sort_prod {| intro [] |} bind{x.'U['x]} :
   sequent { <H>; x:'T1 >- arity_of_sort{'U['x]; 's} } -->
	sequent { <H> >- arity_of_sort{(x:'T1 -> 'U['x]); 's} } = it

(* declaration of 'type of constructor' notion *)
declare type_of_constructor{'T;'I} (* 'T is a type of constructor of 'I *)

dform type_of_constructor_df : type_of_constructor{'T;'I} =
	`"type_of_constructor{" slot{'T} `";" slot{'I} `"}"

prim type_of_constructor_app {| intro [] |} :
   sequent { <H> >- type_of_constructor{ (sequent [applH]{ <T1> >- 'I}); 'I } } = it

prim type_of_constructor_prod {| intro [] |} 'T1 bind{x.'C['x]} :
   sequent { <H>; x:'T1 >- type_of_constructor{'C['x];'I} } -->
	sequent { <H> >- type_of_constructor{ (x:'T1 -> 'C['x]); 'I } } = it

declare imbr_pos_cond_m (* { <Hc> >-( 'I >- 'x ) } *)
(* Hc={c1:C1,...,cn:Cn}, the types constructor Ci (each of them) of 'I
satisfies the imbricated positivity condition for a constant 'x *)

declare imbr_pos_cond{'T;'I;'x} (* the type constructor 'T of 'I satisfies the imbricated positivity
                                   condition of 'x *)

declare strictly_pos{'x;'T} (* constant 'x occurs strictly positively in 'T *)

declare positivity_cond{ 'T; 'x } (* the type of constructor 'T satisfies the positivity
												condition for a constant 'x *)

dform strictly_pos_df : strictly_pos{'x;'T} =
	`"strictly_pos{" slot{'x} `";" slot{'T} `"}"

dform positivity_cond_df : positivity_cond{'T;'x} =
	`"positivity_cond{" slot{'T} `";" slot{'x} `"}"

dform imbr_pos_cond_df : imbr_pos_cond{'T;'I;'x} =
	`"imbr_pos_cond{" slot{'T} `";" slot{'I} `";" slot{'x} `"}"

(* declaration of 'positivity condition' notion *)
prim positivity_cond_1 {| nth_hyp |} 'H :
	sequent { <H>; x:'T; <J['x]> >-
	   positivity_cond{ sequent [applH] { <T1> >- 'x} ;'x } } = it

prim positivity_cond_2 'H bind{x.'T['x]} bind{y,x.'U['y;'x]} :
   sequent { <H>; x:'S; <J['x]> >- strictly_pos{'x;'T['x]}} -->
	sequent { <H>; x:'S; <J['x]>; y:'T['x] >- positivity_cond{'U['y;'x];'x} } -->
	sequent { <H>; x:'S; <J['x]> >- positivity_cond{(y:'T['x] -> 'U['y;'x]);'x} } = it

(* declaration of multiple positivity condition *)
declare positivity_cond_m

dform positivity_cond_m_df : sequent [positivity_cond_m] { <Hi > >- 'C<||> } =
	`"positivity_cond_m{" slot{'C} `" for "
		display_hyps{sequent [positivity_cond_m] { <Hi > >- 'C<||> }} `"}"

prim positivity_cond_m_base {| intro [] |} :
   sequent { <H>; I:'A >- positivity_cond{'C['I];'I} } -->
	sequent { <H> >- sequent [positivity_cond_m] { I:'A >- 'C['I] } } = it

prim positivity_cond_m_step {| intro [] |} :
   sequent { <H>; I:'A >- sequent { <Hi> >- positivity_cond{'C['I];'I} } } -->
	sequent { <H>; I:'A >- sequent [positivity_cond_m] { <Hi > >- 'C['I] } } -->
	sequent { <H> >- sequent [positivity_cond_m] { <Hi>; I:'A<|H|> >- 'C['I] } } = it

(* declaration of 'strictly positive' notion *)
prim strictly_pos_1 {| nth_hyp |} 'H :
   sequent { <H>; x:'T1; <J['x]>  >- strictly_pos{'x;'T} } = it

prim strictly_pos_2 {| nth_hyp |} 'H :
	sequent { <H>; x:'T1; <J['x]> >- strictly_pos{'x;sequent [applH] { <T2> >- 'x}} } = it

prim strictly_pos_3 'H 'U bind{x,y.'V['x;'y]} :
   sequent { <H>; x:'T2; <J['x]>; x1:'U >- strictly_pos{'x;'V['x1;'x]} } -->
	sequent { <H>; x:'T2; <J['x]> >-
	   strictly_pos{'x ; (x1:'U -> 'V['x1;'x])} } = it

(*
prim strictly_pos_4 'H :
   sequent { <H>; x:'T2; <J['x]>; <A1['x]> >-
	   sequent [imbr_pos_cond_m] { <Hc<|A1;H;J|>['I;'x]> >-
		   sequent { 'I >- 'x } } } -->
	sequent { <H>; x:'T2; <J['x]> >-
	   strictly_pos{
		   'x;
			sequent [applH] { <T1>; <A1['x]> >-
				sequent [IndParams] { <Hp> >-
					sequent [IndTypes] { I:'A<|Hp;H;J|>['x] >-
						sequent [IndConstrs] { <Hc<|Hp;H;J|>['I;'x]> >- 'I } } } }} } = it
*)



(* declaration of 'imbricated positivity condition' notion *)

prim imbr_pos_cond_1 'H :
   sequent { <H>; x:'T; <J['x]> >-
	   type_of_constructor{ sequent [applH] { <T1> >- 'I<|J;H|>['x]} ;'I<|J;H|>['x]} } -->
	sequent { <H>; x:'T; <J['x]> >-
	   imbr_pos_cond{ sequent [applH] { <T1> >- 'I<|J;H|>['x]};'I<|J;H|>['x];'x} } = it

prim imbr_pos_cond_2 'H bind{x,y.'U['x;'y]} :
   sequent { <H>; x:'T2; <J['x]> >- type_of_constructor{ (x1:'T['x] -> 'U['x1;'x]) ;'I} } -->
   sequent { <H>; x:'T2; <J['x]> >- strictly_pos{'x;'T['x]} } -->
	sequent { <H>; x:'T2; <J['x]>; x1:'T['x] >- imbr_pos_cond{'U['x1;'x];'I;'x} } -->
	sequent { <H>; x:'T2; <J['x]> >- imbr_pos_cond{(x1:'T['x] -> 'U['x1;'x]);'I;'x} } = it

(* inductive definition of multiple imbricated positivity condition, i.e.
   of imbr_pos_cond_m *)
declare imbr_params{'I;'x}

dform imbr_params_df : imbr_params{'I;'x} = `"imbr_params{" slot{'I} `";" slot{'x} `"}"

dform imbr_pos_cond_m_df : sequent [imbr_pos_cond_m] { <Hc> >- 'T<| |> } =
	`"imbr_pos_cond_m{" display_hyps{ sequent [imbr_pos_cond_m] { <Hc> >- 'T<| |> } } `"|" slot{'T} `"}"

prim imbr_pos_cond_m_base {| nth_hyp |} 'H :
   sequent { <H>; x:'T; <J['x]> >-
		sequent [imbr_pos_cond_m] { >- imbr_params{'I['x];'x} } } = it

prim imbr_pos_cond_m_step 'H :
   sequent { <H>; x:'T; <J['x]> >- imbr_pos_cond{'C['x];'I['x];'x} } -->
	sequent { <H>; x:'T; <J['x]> >-
		sequent [imbr_pos_cond_m] { <Hc['x]> >-
			imbr_params{'I<|H;J|>['x];'x} } } -->
	sequent { <H>; x:'T; <J['x]> >- sequent [imbr_pos_cond_m] { <Hc['x]>; c:'C<|H;J|>['x] >-
	   imbr_params{'I<|H;J|>['x];'x} } } = it


(* declaration of 'of some sort' notion *)
declare of_some_sort_m (* { <T> } *) (* any element of T is a type of some sort (Set, Prop or Type[i]) *)

dform of_some_sort_m_df : sequent [of_some_sort_m] { <T1> >- of_some_sort_m } =
	`"of_some_sort_m{" display_hyps{ sequent [of_some_sort_m] { <T1> >- of_some_sort_m } } `"}"

(* inductive defenition of multiple of_come_sort_m *)
prim of_some_sort_m_base {| intro [] |} :
	sequent { <H> >- sequent [of_some_sort_m] { >- of_some_sort_m } } = it

prim of_some_sort_m_step {| intro [] |} :
   sequent { <H> >- of_some_sort{'T2} } -->
	sequent { <H> >- sequent [of_some_sort_m] { <T1> >- of_some_sort_m } } -->
	sequent { <H> >- sequent [of_some_sort_m] { <T1>; t:'T2<|H|> >- of_some_sort_m } } = it


(* description-defenition of the third condition in the declaration of w_Ind rule*)
declare req3{'C}
declare req3
declare req3_m

dform req3_df : req3{'C} = `"req3{" slot{'C} `"}"

dform req3_m_df : sequent [req3_m] { <Hi> >- sequent { <Hc<| |> > >- it } } =
	`"req3_m{" display_hyps{ sequent [req3_m] { <Hi> >- it } } `"|"
		display_hyps{ sequent [Aux] { <Hc> >- it } } `"}"

prim req3_intro 'Hi 's :
   sequent { <H> >- sequent { <Hi>; I:'A<|H|>; <Ji<|H|> > >- type_of_constructor{'C['I];'I} } } -->
   sequent { <H> >- sequent [positivity_cond_m] { <Hi>; I:'A<|H|>; <Ji<|H|> > >- 'I } } -->
	sequent { <H> >- arity_of_sort{'A<|H|>;'s<||>} } -->
	sequent { <H> >- sequent { <Hi>; I:'A<|H|>; <Ji<|H|> > >- 'C['I] in 's<||> } } -->
   sequent { <H> >- sequent [req3] { <Hi>; I:'A<|H|>; <Ji<|H|> > >- req3{'C['I]} } } = it

prim req3_m_base {| intro [] |} :
	sequent { <H> >- sequent [req3_m] { <Hi> >- sequent  { >- it } } } = it

prim req3_m_step {| intro [] |} :
	sequent { <H> >- sequent [req3_m] { <Hi> >- sequent { <Hc> >- it } } } -->
	sequent { <H> >- sequent [req3] { <Hi> >- req3{'C<|Hi;H|>} } } -->
	sequent { <H> >- sequent [req3_m] { <Hi> >- sequent { <Hc>; c:'C<|Hi;H|> >- it } } } = it


(* implementation of the Coq's W-Ind rule *)
prim w_Ind :
   sequent { <H> >- sequent { <Hp> >-
		sequent [of_some_sort_m] { <Hi> >- of_some_sort_m } } } -->
	sequent { <H> >- sequent { <Hp> >-
		sequent [arity_of_some_sort_m] { <Hi> >- arity_of_some_sort_m } } } -->
	sequent { <H> >- sequent { <Hp> >- sequent [req3_m] { <Hi> >- sequent { <Hc> >- it } } } } -->
	sequent { <H> >-
	   sequent [IndParamsWF] { <Hp> >-
			sequent [IndTypesWF] { <Hi> >-
				sequent [IndConstrsWF] { <Hc> >- it } } } } = it


(****************************************************************
 * *
 ****************************************************************)
