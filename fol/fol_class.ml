(*
 * Classical reasoning.
 *)

include Fol_not

declare magic{x. 't['x]}

dform magic_df : magic = `"magic"

prim magic 'H 'x :
   ('t['x] : sequent ['ext] { 'H; x: "not"{'T} >- "false" }) -->
   sequent ['ext] { 'H >- 'T } =
   magic{x. 't['x]}

let magicT p =
   let v = Var.maybe_new_vars1 p "v" in
      magic (Sequent.hyp_count_addr p) v p

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
