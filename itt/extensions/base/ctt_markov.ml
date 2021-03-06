extends Itt_theory
extends Itt_nat

doc docoff

open Dtactic

interactive squash_stable1 't :
   sequent { <H>; x:'T >- 't in 'T} -->
   sequent { <H>; x:squash{'T} >- 'T}

interactive squash_stable2 bind{v.'t['v]} :
   sequent { <H>; v:squash{'T} >- 't['v] in 'T} -->
   sequent { <H>; x:'T >- 't[it] in 'T}

interactive squash_ex1 :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- squash{'A} => not{not{'A}} }

interactive squash_ex2 :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- iff{squash{'A};squash{squash{'A}}} }

interactive squash_ex3 :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- iff{squash{'A and 'B}; .squash{'A} and squash{'B}} }

interactive squash_ex4 :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- squash{'A => 'B} => (squash{'A} => squash{'B}) }

interactive squash_ex5 :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- iff{squash{not{'A}};not{squash{'A}}} }

interactive squash_ex6 :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- (squash{'A} or squash{'B}) => squash{'A or 'B} }

define unfold_sqst : sqst{'A} <--> (squash{'A} => 'A)

dform sqst_df : except_mode[src] :: sqst{'A} =
    `"sqst(" slot["le"]{'A} `")"

interactive sqst_ex1 :
   sequent { <H> >- sqst{"false"} }

interactive sqst_ex2 :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- sqst{not{'A}} }

interactive sqst_ex3 :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- sqst{squash{'A}} }

interactive sqst_ex4 :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- (sqst{'A} and sqst{'B}) => sqst{'A and 'B} }

interactive sqst_ex5 :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- (sqst{'B}) => sqst{'A => 'B} }

prim markov :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- not{not{'A}} } -->
   sequent { <H> >- squash{'A} } =
   it

interactive markov3 : (* proved from Markov *)
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- squash{('A or  not{'A})} }

interactive markov1 'A : (* proved from Markov3 *)
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H>; x:'A >- 'B } -->
   sequent { <H>; y:not{'A} >- 'B } -->
   [sqstable] sequent { <H>; v:squash{'B} >- 'B } -->
   sequent { <H> >- 'B }

interactive markov0 'A: (* proved from Markov1 *)
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H>; x:'A >- 't in 'T } -->
   sequent { <H>; y:not{'A} >- 't in 'T } -->
   sequent { <H> >- 't in 'T }

interactive markov2' :(* = Markov, proved from Markov0 *)
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- not{not{'A}} } -->
   sequent { <H> >- squash{'A} }

interactive markovN : (* proved from Markov *)
   [wf] sequent { <H> >- 's in 'T } -->
   [wf] sequent { <H> >- 't in 'T } -->
   [main] sequent { <H> >- not{not{'s='t in 'T}} } -->
   sequent { <H> >- 's='t in 'T }

interactive markov2 : (*  = Markov, proved from MarkovN *)
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- not{not{'A}} } -->
   sequent { <H> >- squash{'A} }

interactive markov4 {| intro [SelectOption 1] |} : (*  = proved from Markov *)
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H>; x:not{'A} >- "false" } -->
   sequent { <H> >- squash{'A} }

interactive markov2'' : (*  = Markov, proved from Markov4 *)
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- not{not{'A}} } -->
   sequent { <H> >- squash{'A} }

interactive markovPrinciple :
   [wf] sequent { <H>; n:nat >- "type"{'A 'n} } -->
   sequent { <H> >- all n:nat. ('A 'n or  not{'A 'n}) =>
                           not{not{exst n:nat.'A 'n}} =>
                           exst n:nat.'A 'n}

   (* Proof uses f =  fix{f.lambda{n.decide{('x 'n);a.('n,'a);b.'f ('n+@1)}}} *)

interactive squash_ex4m :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- (squash{'A} => squash{'B}) => squash{'A => 'B} }

interactive sqst_ex6 :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- sqst{'A} => not{not{'A}} =>'A }

define unfold_delta: delta{'A} <--> (quot x,y:'A//"true")

dform delta_df : except_mode[src] :: delta{'A} =
   Mpsymbols!Delta slot["le"]{'A}

interactive delta1 :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- ('A => delta{'A}) }

interactive delta2 :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- (delta{'A} => squash{'A}) }
