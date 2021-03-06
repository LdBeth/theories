(* Labels as natural numberas *)

extends Itt_nat
extends Itt_nequal

open Basic_tactics

define unfold_label : label <--> nat

define unfold_zero : zero <--> 0

define unfold_next : next{'x} <--> ('x +@ 1)

define unfoldInd :   ind_lab{'n; 'base; l. 'up['l]} <-->
                     ind{'n; 'base; k,l . 'up['l]}

rule decide_eq_label 'x 'y :
   [wf] sequent{ <H> >- 'x in label} -->
   [wf] sequent{ <H> >- 'y in label} -->
   sequent{ <H>; u:'x='y in label >- 'C} -->
   sequent{ <H>; u: 'x <> 'y in label >- 'C} -->
   sequent{ <H> >- 'C}

topval decideEqLabel0T : term -> term -> tactic

val  label_sqequal : tactic
