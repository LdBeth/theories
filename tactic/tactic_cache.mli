(*
 * This is a forward-chaining cache, based on sequents.
 * Initially the cache is constructed from a list of rules
 * about forward chaining.  The rules specify how to
 * deduce new facts from old ones.
 *)

open Refiner.Refiner.Term
open Refiner.Refiner.Refine

(*
 * The cache is initially constructed as a "cache" from a collection of rules.
 * During refinement, this is compiled to a "extract", which propagates
 * inherited attributes down the tree.  After refinement, the synthesized
 * attributes are computed using "synthesis".
 *)
type 'a cache
type 'a extract
type 'a synthesis

(*
 * A forward-chaining rule.
 * The justification (which is probably going to be a tactic),
 * takes the indices of the hyps as arguments, takes
 * the names of the results, and produces an 'a (which is
 * probably a tactic).
 *)
type 'a frule =
   { fc_ants : term list;
     fc_concl : term list;
     fc_just : 'a
   }

(*
 * Similar back-chaining rule.
 *)
type 'a brule =
   { bc_concl : term;
     bc_ants : (term list * term) list;
     bc_just : 'a
   }

(*
 * A proof is a list of forward and backward components.
 *)
type 'a proof =
   ForeTactics of (int list * 'a) list
 | BackTactic of ('a * 'a proof list)
 | NthHyp of int
 | SeqTactic of 'a proof list

(*
 * Build up the cache.
 * The argument is a justification composition
 * function.
 *)
val new_cache : unit -> 'a cache
val join_cache : 'a cache -> 'a cache -> 'a cache
val add_frule : 'a cache -> 'a frule -> 'a cache
val add_brule : 'a cache -> 'a brule -> 'a cache
val extract : 'a cache -> 'a extract

(*
 * Actions that modify the current world.
 *)
val add_hyp  : 'a extract -> int -> string -> term -> 'a extract
val del_hyp  : 'a extract -> int -> 'a extract
val ref_hyp  : 'a extract -> int -> 'a extract
val name_hyp : 'a extract -> int -> string -> 'a extract
val set_goal : 'a extract -> term -> 'a extract
val set_msequent : 'a extract -> msequent -> 'a extract

(*
 * Queries.
 *)
val chain : 'a extract -> bool
val lookup : 'a extract -> 'a proof

(* Synthesized attributes *)
val synthesize : 'a extract -> 'a synthesis list -> 'a synthesis
val used_hyps : 'a synthesis -> int list

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
