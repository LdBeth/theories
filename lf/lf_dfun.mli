(*
 * Valid kinds.
 *)

include Lf_sig;;

declare dfun{'A. x. 'K['x]};;
declare lambda{'A; x. 'B['x]};;
declare apply{'A; 'B};;

(*
 * Beta reduction.
 *)
rewrite beta : lambda{'A; x. 'M['x]} 'N <--> 'M['N];;

(*
 * Kinding judgement.
 *)
axiom pi_kind 'S 'C : sequent { 'S; 'C; x. 'A >> 'K['x] } -->
   sequent { 'S; 'C >> x: 'A -> 'K['x] };;

(*
 * Typehood.
 *)
axiom pi_fam 'S 'C :
   sequent { 'S; 'C; x. 'A >> mem{'B['x]; type} } -->
   sequent { 'S; 'C >> mem{x: 'A -> 'B['x]; type } };;

(*
 * Membership.
 *)
axiom pi_abs_fam 'S 'C :
   sequent { 'S; 'C; x. 'A >> mem{'B['x]; 'K['x]} } -->
   sequent { 'S; 'C >> mem{lambda{'A; x. 'B['x]}; y: 'A -> 'K['y] } };;

(*
 * Abs elimination.
 *)
axiom pi_app_fam 'S 'C (x: 'B -> 'K['x]) :
   sequent { 'S; 'C >> mem{'A; x: 'B -> 'K['x] } } -->
   sequent { 'S; 'C >> mem{'M; 'B} } -->
   sequent { 'S; 'C >> mem{'A 'M; 'K['M] } };;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
