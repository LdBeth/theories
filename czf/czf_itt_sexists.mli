(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_and

open Conversionals

declare "exists"{x. 'A['x]}

rewrite unfold_exists : "exists"{x. 'A['x]} <--> prod{set; x. 'A['x]}

val fold_exists : conv

(*
 * Intro.
 *
 * H >- exists x. A[x]
 * by exists_intro z
 * H >- member{z; set}
 * H >- A[z]
 *)
axiom exists_intro 'H 'z 'w :
   sequent ['ext] { 'H >- isset{'z} } -->
   sequent ['ext] { 'H >- 'A['z] } -->
   sequent ['ext] { 'H; w: set >- wf{'A['w]} } -->
   sequent ['ext] { 'H >- "exists"{x. 'A['x]} }

(*
 * Elimination.
 *
 * H, x: exists{y. A[y]}, J[x] >- T[x]
 * by exists_elim
 * H, x: exists{x. A[x]}, z: set, w: A[z], J[pair{z, w}] >- T[pair{z, w}]
 *)
axiom exists_elim 'H 'J 'x 'z 'w :
   sequent ['ext] { 'H;
                    x: "exists"{y. 'A['y]};
                    z: set;
                    w: 'A['z];
                    'J[pair{'z; 'w}]
                    >- 'T[pair{'z; 'w}]
                  } -->
   sequent ['ext] { 'H; x: "exists"{y. 'A['y]}; 'J['x] >- 'T['x] }

(*
 * Well formedness.
 *)
axiom exists_wf 'H 'y :
   sequent ['ext] { 'H; y: set >- wf{'A['y]} } -->
   sequent ['ext] { 'H >- wf{."exists"{x. 'A['x]} } }

(*
 * Simple quantification is restricted.
 *)
axiom exists_res 'H 'y :
   sequent ['ext] { 'H; y: set >- restricted{'A['x]} } -->
   sequent ['ext] { 'H >- restricted{."exists"{x. 'A['x]}} }

