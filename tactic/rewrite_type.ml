(*
 * This is the basic rewrite data type.
 * A file with this name is required for every theory.
 *)

include Perv

open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermAddr
open Refiner.Refiner.Rewrite
open Refiner.Refiner.Refine

open Tactic_type
open Tacticals
open Var

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * A conversion is wither a regular rewrite,
 * or a conditional rewrite, or a composition.
 *
 * NOTE: we need to use a better data structure for
 * Compose and Choose that has more efficient
 * operations.
 *)
type env = tactic_arg * address

type conv =
   Rewrite of rw
 | CondRewrite of cond_rewrite
 | Compose of conv Flist.t
 | Choose of conv Flist.t
 | Address of address * conv
 | Fold of term * conv
 | Cut of term
 | Fun of (env -> conv)
 | Identity

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Justification for rewrites.
 *)
declare rewrite_just

(*
 * The basic rewrite axiom.
 * BUG: jyh: I don't know why we need the extra param here.
 *)
prim rewriteAxiom 'a : : "rewrite"{'x; 'x} = rewrite_just

(*
 * Sequent version of rewrite proposition.
 *)
prim rewriteSequentAxiom 'H : :
   sequent ['ext] { 'H >- "rewrite"{'x; 'x} } =
   rewrite_just

(*
 * Sequent replacement.
 *)
prim rewriteHypCut 'H 'J 'T1 :
   ('t : sequent ['ext] { 'H; x: 'T1; 'J['x] >- 'C['x] }) -->
   sequent ['ext] { 'H >- "rewrite"{'T1; 'T2} } -->
   sequent ['ext] { 'H; x: 'T2; 'J['x] >- 'C['x] } =
   't

prim rewriteConclCut 'H 'T1 :
   ('t : sequent ['ext] { 'H >- 'T1 }) -->
   sequent ['ext] { 'H >- "rewrite"{'T1; 'T2} } -->
   sequent ['ext] { 'H >- 'T2 } =
   't

prim rewriteContextCut 'H 'J (lambda{v. 'T['v]}) :
   ('t : "sequent"{'ext; ."context"[H:v]{'T["concl"{'C; ."concl"}]}}) -->
   "sequent"{'ext; ."context"[H:v]{."concl"{."rewrite"{.'T[rewrite_just]; ."context"[J:v]{rewrite_just}}; concl}}} -->
   "sequent"{'ext; ."context"[H:v]{."context"[J:v]{."concl"{'C; ."concl"}}}} =
   't

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Get the term of the environment.
 *)
let env_term (arg, addr) =
   term_subterm (Sequent.goal arg) addr

(*
 * Get the sequent that we are matching against.
 *)
let env_goal (arg, _) =
   Sequent.goal arg

(*
 * Create a conversion from a basic rewrite.
 * This function is required by filter_prog.
 *)
let rewrite_of_rewrite rw =
   Rewrite rw

(*
 * Create a conversion from a conditional rewrite.
 * This function is required by filter_prog.
 *)
let rewrite_of_cond_rewrite crw args =
   CondRewrite (crw args)

(*
 * Combine two lissts of conversion.
 * Note if the adjacent conversion can be combined.
 *)
let combine rw_f crw_f make clist1 clist2 =
   match Flist.last clist1, Flist.first clist2 with
      Rewrite rw1, Rewrite rw2 ->
         let rw = Rewrite (rw_f rw1 rw2) in
            if Flist.singleton clist1 & Flist.singleton clist2 then
               rw
            else
               make (Flist.append_skip clist1 rw clist2)
    | CondRewrite crw1, CondRewrite crw2 ->
         let crw = CondRewrite (crw_f crw1 crw2) in
            if Flist.singleton clist1 & Flist.singleton clist2 then
               crw
            else
               make (Flist.append_skip clist1 crw clist2)
    | _ ->
         make (Flist.append clist1 clist2)

let compose clist1 clist2 =
   combine andthenrw candthenrw (fun l -> Compose l) clist1 clist2

let choose clist1 clist2 =
   combine orelserw corelserw (fun l -> Choose l) clist1 clist2

let prefix_andthenC conv1 conv2 =
   let clist1 =
      match conv1 with
         Compose clist1 ->
            clist1
       | _ ->
            Flist.create conv1
   in
   let clist2 =
      match conv2 with
         Compose clist2 ->
            clist2
       | _ ->
            Flist.create conv2
   in
      compose clist1 clist2

let prefix_orelseC conv1 conv2 =
   let clist1 =
      match conv1 with
         Choose clist1 ->
            clist1
       | _ ->
            Flist.create conv1
   in
   let clist2 =
      match conv2 with
         Choose clist2 ->
            clist2
       | _ ->
            Flist.create conv2
   in
      choose clist1 clist2

(*
 * No action.
 *)
let idC = Identity

(*
 * Function conversion needs an argument.
 *)
let funC f =
   Fun f

(*
 * Apply the conversion at the specified address.
 *)
let addrC addr =
   let addr = make_address addr in
      (function
         Rewrite rw ->
            Rewrite (rwaddr addr rw)
       | CondRewrite crw ->
            CondRewrite (crwaddr addr crw)
       | conv ->
            Address (addr, conv))

(*
 * Reverse the conversion at the specified address.
 *)
let foldC t conv =
   Fold (t, conv)

(*
 * Build a fold conversion from the contractum
 * and the unfolding conversion.
 *)
let makeFoldC contractum conv =
   let fold_aux = function
      Rewrite rw ->
         let mseq = { mseq_hyps = []; mseq_goal = contractum } in
         let tac = rwtactic rw in
            begin
               (* Apply the unfold conversion *)
               match Refine.refine tac mseq with
                  [{ mseq_goal = redex }], _ ->
                     (* Unfolded it, so create a rewrite that reverses it *)
                     let rw' = term_rewrite ([||], [||]) [redex] [contractum] in
                     let doCE env =
                        try
                        match apply_rewrite rw' ([||], [||]) [env_term env] with
                           [contractum], _ ->
                              Fold (contractum, conv)
                         | _ ->
                              raise (RefineError ("Rewrite_type.fold", StringTermError ("rewrite failed", redex)))
                        with
                           Rewrite.RewriteError err ->
                              raise (RefineError ("Rewrite_Type.fold", RewriteError err))
                     in
                        Fun doCE
                | _ ->
                     raise (RefineError ("Rewrite_type.fold", StringTermError ("fold failed", contractum)))
            end
    | _ ->
         raise (RefineError ("Rewrite_type.fold", StringError "can't fold nontrivial rewrites"))
   in
      Refine_exn.print Dform.null_base fold_aux conv

(*
 * Cut just replaces the term an generates a rewrite
 * subgoal.
 *)
let cutC t =
   Cut t

(*
 * Apply cut sequent rule.
 * We have three cases:
 *    1. The replacement is in a hyp
 *    2. The replacement is in a hyp context
 *    3. The replacement is in the concl
 *)
let rewrite_just_term = << rewrite_just >>

let cutT i addr t p =
   if i = 0 then
      let t2 = Sequent.concl p in
      let j = Sequent.hyp_count p in
      let t1 = replace_subterm t2 addr t in
      let i = Sequent.hyp_count p in
         rewriteConclCut i t1 p
   else
      let goal = Sequent.goal p in
      let caddr = Sequent.clause_addr p i in
      let clause = term_subterm goal caddr in
         if is_context_term clause then
            let v = maybe_new_vars1 p "v" in
            let vt = mk_var_term v in
            let name, arg, args = dest_context clause in
            let t1 = mk_context_term name vt args in
            let t1 = replace_subterm t1 addr t in
            let t1 = mk_xlambda_term v t1 in
            let count = Sequent.hyp_count p in
            let i, j =
               if i < 0 then
                  count + i, -i
               else
                  i - 1, count - i + 1
            in
               rewriteContextCut i j t1 p
         else
            let _, t1 = Sequent.nth_hyp p i in
            let i, j = Sequent.hyp_indices p i in
            let t1 = replace_subterm t1 addr t in
               rewriteHypCut i j t1 p

(*
 * Apply axiom rule.
 *)
let rwAxiomT =
   rewriteAxiom << "string"["bogus argument"] >>

(*
 * Apply sequent axiom rule.
 *)
let rwSeqAxiomT p =
   rewriteSequentAxiom (Sequent.hyp_count p) p

(*
 * Apply the rewrite.
 *)
let rw conv i p =
   (*
    * root: address of the clause
    * rel: offset into the term
    * addr: compose_addrress root rel
    *)
   let rec apply i rel addr conv p =
      match conv with
         Rewrite rw ->
            tactic_of_rewrite (rwaddr addr rw) p
       | CondRewrite crw ->
            tactic_of_cond_rewrite (crwaddr addr crw) p
       | Compose clist ->
            composeT i rel addr (Flist.tree_of_list clist) p
       | Choose clist ->
            chooseT i rel addr (Flist.tree_of_list clist) p
       | Address (addr', conv) ->
            let rel = compose_address rel addr' in
            let addr = compose_address addr addr' in
               apply i rel addr conv p
       | Identity ->
            idT p
       | Fun f ->
            apply i rel addr (f (p, addr)) p
       | Fold (t, conv) ->
            (cutT i rel t thenLT [idT; solveCutT i rel conv]) p
       | Cut t ->
            cutT i rel t p

   and composeT i rel addr tree p =
      match tree with
         Flist.Empty ->
            idT p
       | Flist.Leaf conv ->
            apply i rel addr conv p
       | Flist.Append (tree1, tree2) ->
            (composeT i rel addr tree1
             thenT composeT i rel addr tree2) p

   and chooseT i rel addr tree p =
      match tree with
         Flist.Empty ->
            idT p
       | Flist.Leaf conv ->
            apply i rel addr conv p
       | Flist.Append (tree1, tree2) ->
            (chooseT i rel addr tree1
             orelseT chooseT i rel addr tree2) p

   and solveCutT i rel conv p =
      let rel = compose_address (make_address [0]) rel in
      let root = Sequent.clause_addr p 0 in
      let addr = compose_address root rel in
         (apply i rel addr conv thenT rwSeqAxiomT) p
   in
   let addr = Sequent.clause_addr p i in
      apply i (make_address []) addr conv p

(*
 * $Log$
 * Revision 1.4  1998/06/23 22:12:41  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 * Revision 1.3  1998/06/22 20:01:43  jyh
 * Fixed syntax error in term_addr_gen.ml
 *
 * Revision 1.2  1998/06/22 19:46:43  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.1  1998/06/03 22:19:55  jyh
 * Nonpolymorphic refiner.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
