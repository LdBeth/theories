(*
 * @begin[doc]
 * @theory[Comment]
 *
 * Structured comments are comments with ! as the first character.
 * Currently, structured comments can be used only at the top level of
 * of an interface or implementation.  The text in the comment is parsed
 * into a sequence of strings in a list (using mk_xlist_term).  The text
 * can also contain terms.  All terms are described with the form
 *
 *    @opname[s1, ..., sm]{t1; ...; tn},
 *
 * where s1, ..., sn are strings, and where t1, ..., tn are comment text.
 * The parameters/subterms can be ommitted.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 *
 * Copyright (C) 2000 Jason Hickey, Caltech
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
 * jyh@cs.caltech.edu
 *
 * @end[license]
 *)

(*
 * @begin[doc]
 * @terms
 * Basic comment structure.
 * @end[doc]
 *)
declare comment_white
declare comment_string[s:s]
declare comment_term{'t}
declare comment_block{'t}

(*
 * @begin[doc]
 * These are the valid comment blocks.
 * @end[doc]
 *)
declare doc{'t}
declare license{'t}
declare spelling{'t}
declare misspelled{'t}

(*
 * These terms are used by the summary module for display forms.
 *)
declare prl_comment{'t}
declare tex_comment{'t}

(*
 * @begin[doc]
 * @terms
 * The @theory[name:s] term produces a section header for the current module.
 * @end[doc]
 *)
declare "theory"[name:s]{'t}

(*
 * @begin[doc]
 * The @thysection{'t} term prduces a subsection header.
 * @end[doc]
 *)
declare thysection{'t}

(*
 * @begin[doc]
 * The @thysubsection{'t} term prduces a subsection header.
 * @end[doc]
 *)
declare thysubsection{'t}

(*
 * Other forms of sectioning commands.
 *)
declare parents
declare rewrites
declare rules
declare convs
declare tactics
declare resources
declare terms

(*
 * Hypertext targets.
 *)
declare "term"[name:s]
declare "resource"[name:s]
declare "tactic"[name:s]
declare "conv"[name:s]
declare "rule"[name:s]
declare "rewrite"[name:s]

(*
 * Hypertext links.
 *)
declare hreftheory[name:s]
declare hrefterm[name:s]
declare hrefresource[name:s]
declare hrefrewrite[name:s]
declare hreftactic[name:s]
declare hrefconv[name:s]
declare hrefrule[name:s]

declare reftheory[name:s]
declare refterm[name:s]
declare refresource[name:s]
declare refrewrite[name:s]
declare reftactic[name:s]
declare refconv[name:s]
declare refrule[name:s]

(*
 * TeX structuring.
 *)
declare "begin"[name:s]
declare "end"[name:s]

(*
 * TeX control.
 *)
declare docoff
declare noindent
declare cite{'t}

(*
 * Special terms.
 *)
declare "MetaPRL"
declare "Nuprl"
declare "NuPRL"
declare "OCaml"
declare "LaTeX"
declare "MartinLof"

(*
 * Formatting.
 *)
declare math[s:s]
declare centermath[s:s]

declare code[text:s]
declare verbatim[text:s]
declare email[text:s]
declare center{'t}
declare quote{'t}
declare quotation{'t}
declare enumerate{'t}
declare itemize{'t}
declare description{'t}
declare item{'t}

(************************************************************************
 * MATH MODE                                                            *
 ************************************************************************)

(*
 * Toplevel forms.
 *)
declare math_misspelled{'t}

(*
 * Allow raw printing.
 *)
declare math_slot[tag:s]{'t}

(*
 * Font control in math mode.
 *)
declare math_bb{'t}
declare math_tt{'t}
declare math_bf{'t}
declare math_i{'t}
declare math_emph{'t}
declare math_mathop{'t}
declare math_mathrel{'t}

(*
 * Math symbols.
 *)
declare math_Type

declare math_colon
declare math_rightarrow
declare math_Rightarrow
declare math_leftarrow
declare math_Leftarrow
declare math_leftrightarrow
declare math_Leftrightarrow
declare math_longleftrightarrow

declare math_wedge
declare math_vee
declare math_phi
declare math_varphi
declare math_cap
declare math_cup
declare math_bigcap
declare math_bigcup
declare math_in
declare math_cdot
declare math_cdots
declare math_vdots
declare math_ldots
declare math_subset
declare math_subseteq
declare math_times
declare math_equiv
declare math_space
declare math_neg
declare math_neq
declare math_forall
declare math_exists
declare math_lambda
declare math_int

(*
 * Sub/superscripts.
 *)
declare math_subscript{'t1; 't2}
declare math_superscript{'t1; 't2}

(*
 * Math blocks.
 *
 * An array looks like this:
 * @begin[array, rcl]
 * @begin[line]
 * @item{x}
 * @item{y}
 * @item{z}
 * @end[line]
 *
 * ...
 * @end[array]
 *)
declare math_array[tags]{'t}
declare math_tabular[tags]{'t}
declare math_line{'t}
declare math_item{'t}
declare math_cr
declare math_hline

(*
 * These macros are used to declare rules,
 * and display ruleboxes.
 *)
declare math_defrule{'name; 'args; 'hyps; 'goal}
declare math_rulebox{'tac; 'args; 'hyps; 'goal}
declare math_sequent{'ext; 'hyps; 'goal}

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
