(*
 * Judgments for FSub.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005 Mojave Group, Caltech
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
extends Itt_hoas_sequent_native
extends Pmn_core_terms

open Basic_tactics

(************************************************************************
 * The subtyping judgment.
 *)
declare "fsub_subtype"{'ty1; 'ty2}
declare "fsub_member"{'e; 'ty}

(************************************************************************
 * Tactics.
 *)
topval fold_isJudgment : conv

(************************************************************************
 * The hooks for reflected rules.
 *)
declare SOVar{'d}
declare CVar{'d}
declare Sequent
declare ProofStep

(************************************************************************
 * Grammar.
 *)
declare tok_colon_in_colon : Terminal

lex_token xterm : ":in:" --> tok_colon_in_colon

lex_prec nonassoc [tok_colon_in_colon] = prec_in

production xterm_term{"fsub_subtype"{'ty1; 'ty2}} <--
   xterm_term{'ty1}; tok_st; xterm_term{'ty2}

production xterm_term{"fsub_member"{'e; 'e}} <--
   xterm_term{'e}; tok_colon_in_colon; xterm_term{'ty2}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
