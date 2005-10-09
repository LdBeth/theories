(*
 * Typed core language.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003-2005 Mojave Group, Caltech
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends Itt_theory

(************************************************************************
 * Typeclasses for the different kinds of expressions in the theory.
 * Since we are going to be using ITT for reasoning, these typeclasses
 * are all trivially equal to Term (since ITT is untyped).
 *)
declare typeclass TyVar : Term
declare typeclass TyExp : Term
declare typeclass Var   : Term
declare typeclass Exp   : Term

declare rewrite TyVar <--> Term
declare rewrite TyExp <--> Term
declare rewrite Var   <--> Term
declare rewrite Exp   <--> Term
declare rewrite Prop  <--> Term

(************************************************************************
 * Type expressions.
 *
 * This definition is based on the use of second-order abstract syntax,
 * described in Despeyroux, Joëlle and Hirschowitz, Andre, "Higher-order
 * abstract syntax with induction in Coq", INRIA tech report RR-2292,
 * 1994, http://www.inria.fr/rrrt/rr-2292.html.
 *
 * To summarize, variables are constructed explicitly, and Lambda
 * abstractions are represented by functions over the "Var" type.
 *)

(*
 * Types.
 *)
declare TyTop  : TyExp
declare TyVar{'v : TyVar} : TyExp
declare TyFun{'ty_domain : TyExp; 'ty_range : TyExp} : TyExp
declare TyAll{'ty_bound : TyExp; x : TyVar. 'ty['x] : TyExp} : TyExp

(************************************************************************
 * Expressions.
 *)

(*
 * Variables.
 *)
declare Var{'v : Var} : Exp

(*
 * Normal abstraction and application.
 *)
declare Lambda{'ty_arg : TyExp; x : Var. 'e['x] : Exp} : Exp
declare Apply{'e1 : Exp; 'e2 : Exp} : Exp

(*
 * Type abstraction and application.
 *)
declare TyLambda{'ty_bound : TyExp; x : TyVar. 'e['x] : Exp} : Exp
declare TyApply{'e : Exp; 'ty_arg : TyExp} : Exp

(************************************************************************
 * Judgments.
 *)

(*
 * Propositions (also called judgments).
 *)
declare "member"{'e : Exp; 'ty : TyExp} : Prop           (* 'e is an expression with type 'ty *)
declare "subtype"{'tsub : TyExp; 'tsup : TyExp} : Prop   (* 'tsub is a subtype of 'tsup *)

(************************************************************************
 * The rest of this file defines a LALR(1) grammar for parsing
 * types and expressions in Fsub.  This isn't really necessary, since
 * we can always use the native MetaPRL term syntax to construct
 * terms in Fsub.  However, a custom grammar means that the definitions
 * are much more readable.
 *
 * This should be viewed with some degree of skepticism.  The grammar
 * could potentially mean that the terms you type are not what
 * you intend.  For instance, we could imagine that some adversary
 * defines a grammar where all propositions parse to "true".  There are
 * two counterarguments:
 *
 *    1. Display is defined separately, so the adversary would have
 *       to corrupt the display definitions too.
 *
 *    2. LALR(1) grammars are routine in PL.  If you are skeptical,
 *       you should be able to examine the grammar to see if it
 *       defines what you think.
 *)

(************************************************
 * Lexing.
 *)
declare tok_itt          : Terminal
declare tok_top          : Terminal
declare tok_exp          : Terminal
declare tok_Var          : Terminal
declare tok_Exp          : Terminal
declare tok_TyVar        : Terminal
declare tok_TyExp        : Terminal

declare tok_tilde        : Terminal
declare tok_dt           : Terminal
declare tok_st           : Terminal
declare tok_left_curly   : Terminal
declare tok_right_curly  : Terminal

lex_token itt : "itt"    --> tok_itt
lex_token itt : "top"    --> tok_top
lex_token itt : "exp"    --> tok_exp
lex_token itt : "Var"    --> tok_Var
lex_token itt : "Exp"    --> tok_Exp
lex_token itt : "TyVar"  --> tok_TyVar
lex_token itt : "TyExp"  --> tok_TyExp

lex_token itt : "~"      --> tok_tilde
lex_token itt : "::"     --> tok_dt
lex_token itt : "<:"     --> tok_st
lex_token itt : "[{]"    --> tok_left_curly
lex_token itt : "[}]"    --> tok_right_curly

lex_prec nonassoc [tok_st; tok_dt] = prec_in

(************************************************
 * Parsing.
 *)

(************************************************
 * Types.
 *)
declare typeclass parsed_type_exp -> TyExp

declare tast_type{'ty : TyExp} : Nonterminal
declare tast_proper_type{'ty : TyExp} : Nonterminal

production tast_type{'e} <--
   itt_sovar{'e}

production tast_type{'e} <--
   tok_quotation{'e}

production tast_type{'e} <--
   tok_itt; tok_left_curly; itt_term{'e}; tok_right_curly

production tast_type{TyVar{'v}} <--
   tok_tilde; tok_id[v:s]

production tast_type{'e} <--
   tast_proper_type{'e}

production tast_proper_type{'e} <--
   tok_left_paren; tast_proper_type{'e}; tok_right_paren

production tast_proper_type{TyTop} <--
   tok_top

production tast_proper_type{TyFun{'ty1; 'ty2}} <--
   tast_type{'ty1}; tok_arrow; tast_type{'ty2}

production tast_proper_type{TyAll{'ty1; v. 'ty2}} <--
   tok_all; tok_id[v:s]; tok_st; tast_type{'ty1}; tok_dot; tast_type{'ty2}

(************************************************
 * Expressions.
 *
 * We have the usual issue with application-by-concatenation.
 * Applications are only allowed on identifiers and parenthesized
 * expressions.
 *)
declare typeclass parsed_exp -> Exp

declare tast_exp{'e : Exp} : Nonterminal
declare tast_exp_apply{'e : Exp} : Nonterminal
declare tast_exp_simple{'e : Exp} : Nonterminal

(* Simple expressions that can be used in an application *)
production tast_exp_simple{'e} <--
   itt_sovar{'e}

production tast_exp_simple{'e} <--
   tok_quotation{'e}

production tast_exp_simple{'e} <--
   tok_itt; tok_left_curly; itt_term{'e}; tok_right_curly

production tast_exp_simple{Var{'v}} <--
   tok_tilde; tok_id[v:s]

production tast_exp_simple{'e} <--
   tok_left_paren; tast_exp{'e}; tok_right_paren

(* Applications *)
production tast_exp_apply{'e} <--
   tast_exp_simple{'e}

production tast_exp_apply{Apply{'e1; 'e2}} <--
   tast_exp_apply{'e1}; tast_exp_simple{'e2}

(* All expressions *)
production tast_exp{'e} <--
   tast_exp_apply{'e}

production tast_exp{Lambda{'ty; v. 'e}} <--
   tok_fun; tok_id[v:s]; tok_colon; tast_type{'ty}; tok_arrow; tast_exp{'e}

production tast_exp{TyLambda{'ty; v. 'e}} <--
   tok_Fun; tok_id[v:s]; tok_st; tast_type{'ty}; tok_arrow; tast_exp{'e}

production tast_exp{TyApply{'e; 'ty}} <--
   tast_exp{'e}; tok_left_curly; tast_type{'ty}; tok_right_curly

(************************************************
 * Propositions.
 *)
production itt_term{Var} <--
    tok_Var

production itt_term{Exp} <--
    tok_Exp

production itt_term{TyVar} <--
    tok_TyVar

production itt_term{TyExp} <--
    tok_TyExp

production itt_term{TyTop} <--
    tok_top

production itt_term{"member"{'ty1; 'ty2}} <--
    itt_term{'ty1}; tok_dt; itt_term{'ty2}

production itt_term{"subtype"{'ty1; 'ty2}} <--
    itt_term{'ty1}; tok_st; itt_term{'ty2}

production itt_term{'e} <--
    tok_type; tok_left_curly; tast_type{'e}; tok_right_curly

production itt_term{'e} <--
    tok_exp; tok_left_curly; tast_exp{'e}; tok_right_curly

(************************************************
 * Toplevel productions.
 *)
declare fsub_exp{'e : Exp}      : Nonterminal
declare fsub_type{'ty : TyExp}  : Nonterminal

parser fsub_exp{'e}  : itt
parser fsub_type{'e} : itt

production fsub_exp{'e} <--
   tast_exp{'e}; tok_eof

production fsub_type{'e} <--
   tast_type{'e}; tok_eof

(*
 * Input forms.
 *)
iform strip_fsub_exp            : fsub_exp{'e} <--> 'e
iform strip_fsub_type           : fsub_type{'ty} <--> 'ty

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)