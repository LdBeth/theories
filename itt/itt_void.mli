(*
 * Here are rules for the Void base type.
 * Void has no elements.  Its propositional
 * interpretation is "False".
 *
 *)

include Itt_equal

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare void

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Void
 * by voidFormation
 *)
axiom voidFormation 'H : sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- Void = Void in Ui ext Ax
 * by voidEquality
 *)
axiom voidEquality 'H : sequent ['ext] { 'H >- void = void in univ[@i:l] }

(*
 * H; i:x:Void; J >- C
 * by voidElimination i
 *)
axiom voidElimination 'H 'J : sequent ['ext] { 'H; x: void; 'J['x] >- 'C['x] }

(*
 * $Log$
 * Revision 1.1  1997/04/28 15:52:32  jyh
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
 * Revision 1.8  1996/09/02 19:38:48  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.7  1996/05/21 02:18:34  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.6  1996/04/11 13:34:54  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.5  1996/03/28 02:51:48  jyh
 * This is an initial version of the type theory.
 *
 * Revision 1.4  1996/03/05 19:59:55  jyh
 * Version just before LogicalFramework.
 *
 * Revision 1.3  1996/02/15 20:36:47  jyh
 * Upgrading prlcomp.
 *
 * Revision 1.2  1996/02/13 21:36:15  jyh
 * Intermediate checkin while matching is bing added to the refiner.
 *
 * Revision 1.1  1996/02/10 20:18:18  jyh
 * Initiali checking for base+itt refiners.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
