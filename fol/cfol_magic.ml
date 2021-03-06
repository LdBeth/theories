(*
 * Classical reasoning.
 *)
extends Fol_not

declare magic{x. 't['x]}

dform magic_df : magic {x. 't} = `"magic"

prim magic :
   ('t['x] : sequent { <H>; x: "not"{'T} >- "false" }) -->
   sequent { <H> >- 'T } =
   magic{x. 't['x]}

let magicT = magic

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
