(*
 * Atom is the type of tokens (strings)
 *
 *)

include Itt_equal

open Printf
open Nl_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Rformat
open Sequent
open Resource

open Itt_equal

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_atom%t" eflush

(* debug_string DebugLoad "Loading itt_atom..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare atom
declare token[@t:t]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform atom_df : mode[prl] :: atom = `"Atom"
dform token_df : mode[prl] :: token[@t:t] =
   slot[@t:s]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Atom
 * by atomFormation
 *)
prim atomFormation 'H : : sequent ['ext] { 'H >- univ[@i:l] } = atom

(*
 * H >- Atom = Atom in Ui ext Ax
 * by atomEquality
 *)
prim atomEquality 'H : : sequent ['ext] { 'H >- atom = atom in univ[@i:l] } = it

(*
 * Typehood.
 *)
prim atomType 'H : : sequent ['ext] { 'H >- "type"{atom} } = it

(*
 * H >- Atom ext "t"
 * by tokenFormation "t"
 *)
prim tokenFormation 'H token[@t:t] : : sequent ['ext] { 'H >- atom } =
   token[@t:t]

(*
 * H >- "t" = "t" in Atom
 * by tokenEquality
 *)
prim tokenEquality 'H : : sequent ['ext] { 'H >- token[@t:t] = token[@t:t] in atom } = it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let atom_term = << atom >>
let token_term = << token[@x:t] >>
let token_opname = opname_of_term token_term
let is_token_term = TermOp.is_token_term token_opname
let dest_token = TermOp.dest_token_term token_opname
let mk_token_term = TermOp.mk_token_term token_opname

(*
 * D
 *)
let bogus_token = << token["token":t] >>

let d_atomT i p =
   if i = 0 then
      tokenFormation (hyp_count_addr p) bogus_token p
   else
      raise (RefineError ("d_atomT", StringError "no elimination form"))

let d_resource = d_resource.resource_improve d_resource (atom_term, d_atomT)

(*
 * EqCD.
 *)
let eqcd_atomT p =
   atomEquality (hyp_count_addr p) p

let eqcd_tokenT p =
   let count = hyp_count_addr p in
      tokenEquality count p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (atom_term, eqcd_atomT)
let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (token_term, eqcd_tokenT)

(*
 * Typehood.
 *)
let atom_equal_term = << atom = atom in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (atom_equal_term, d_wrap_eqcd eqcd_atomT)

let d_atom_typeT i p =
   if i = 0 then
      atomType (hyp_count_addr p) p
   else
      raise (RefineError ("d_atom_typeT", StringError "no elimination form"))

let atom_type_term = << "type"{atom} >>

let d_resource = d_resource.resource_improve d_resource (atom_type_term, d_atom_typeT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of atom.
 *)
let inf_atom _ decl _ = decl, univ1_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (atom_term, inf_atom)

(*
 * Type of an equality is the type of the equality type.
 *)
let inf_token _ decl _ = decl, atom_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (token_term, inf_token)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
