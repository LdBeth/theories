doc <:doc< 
   @spelling{cycgroup}
  
   @begin[doc]
   @module[Czf_itt_cyclic_subgroup]
  
   The @tt{Czf_itt_cyclic_subgroup} module defines cyclic subgroups.
   A cyclic subgroup of group $g$ generated by $a$ is a subgroup of
   $g$ whose carrier is the collection of $a^n (n @in @int)$ where
   $a @in @car{g}$. In other words, the carrier is the set of 
   elements in $@car{g}$ that is equal to $a^n$ for some $n @in @int$.
  
   @end[doc]
  
   ----------------------------------------------------------------
  
   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.
  
   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.
  
   Copyright (C) 2002 Xin Yu, Caltech
  
   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.
  
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
  
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
  
   Author: Xin Yu
   @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>
extends Czf_itt_group_power
extends Czf_itt_subgroup
doc <:doc< @docoff >>

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Simple_print
open Printf
open Mp_debug

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

let _ =
   show_loading "Loading Czf_itt_cyclic_subgroup%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< @doc{@terms} >>
declare cyc_subg{'s; 'g; 'a}
doc <:doc< @docoff >>

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rewrites
  
   A group $s$ is a cyclic subgroup of group $g$ generated by $a$
   if the carrier of $s$ is the set of elements $x$ in $@car{g}$
   which is equal to $@power{g; a; n}$ for some integer $n$, and
   if the binary operation of $s$ is the same as that of $g$.
   @end[doc]
>>
prim_rw unfold_cyc_subg : cyc_subg{'s; 'g; 'a} <-->
   (group{'s} & group{'g} & mem{'a; car{'g}} & equal{car{'s}; sep{car{'g}; x. (exst n: int. eq{'x; power{'g; 'a; 'n}})}} & (all a: set. all b: set. (mem{'a; car{'s}} => mem{'b; car{'s}} => eq{op{'s; 'a; 'b}; op{'g; 'a; 'b}})))
doc <:doc< @docoff >>

let fold_cyc_subg = makeFoldC << cyc_subg{'s; 'g; 'a} >> unfold_cyc_subg

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform cyc_subg_df : except_mode[src] :: cyc_subg{'s; 'g; 'a} =
   `"cyclic_subgroup(" slot{'s} `"; " slot{'g} `"; " slot{'a} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

interactive exst_power_fun {| intro [] |} :
   sequent [squash] { <H> >- 'g IN label } -->
   sequent [squash] { <H> >- isset{'a} } -->
   sequent ['ext] { <H> >- fun_prop{z. (exst n: int. eq{'z; power{'g; 'a; 'n}})} }

interactive exst_power_res {| intro [] |} :
   sequent [squash] { <H> >- 'g IN label } -->
   sequent [squash] { <H> >- isset{'a} } -->
   sequent [squash] { <H> >- isset{'z} } -->
   sequent ['ext] { <H> >- restricted{(exst n: int. eq{'z; power{'g; 'a; 'n}})} }

doc <:doc< 
   @begin[doc]
   @rules
   @modsubsection{Typehood}
  
   The $@cycsubg{s; g; a}$ is well-formed if $s$ and $g$ are labels
   and $a$ is a set.
   @end[doc]
>>
interactive cyc_subg_wf {| intro [] |} :
   sequent [squash] { <H> >- 'g IN label } -->
   sequent [squash] { <H> >- 's IN label } -->
   sequent [squash] { <H> >- isset{'a} } -->
   sequent ['ext] { <H> >- "type"{cyc_subg{'s; 'g; 'a}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction}
  
   The proposition $@cycsubg{s; g; a}$ is true if it is well-formed,
   $s$ and $g$ are groups, $@mem{a; @car{g}}$,
   $@equal{@car{g}; @sep{x; @car{s}; @exists{n; @int; @eq{x; @power{g; a; x}}}}}$, and
   $@op{s; a; b}$ is defined as $@op{g; a; b}$ for $a, b @in @car{s}$.
   @end[doc]
>>
interactive cyc_subg_intro {| intro [] |} :
   sequent [squash] { <H> >- 'g IN label } -->
   sequent [squash] { <H> >- 's IN label } -->
   sequent ['ext] { <H> >- group{'g} } -->
   sequent ['ext] { <H> >- group{'s} } -->
   sequent [squash] { <H> >- isset{'a} } -->
   sequent ['ext] { <H> >- mem{'a; car{'g}} } -->
   sequent ['ext] { <H> >- equal{car{'s}; sep{car{'g}; x. (exst n: int. eq{'x; power{'g; 'a; 'n}})}} } -->
   sequent ['ext] { <H>; b: set; c: set; x: mem{'b; car{'s}}; y: mem{'c; car{'s}} >- eq{op{'s; 'b; 'c}; op{'g; 'b; 'c}} } -->
   sequent ['ext] { <H> >- cyc_subg{'s; 'g; 'a} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Properties}
  
   A cyclic subgroup is a subgroup.
   @end[doc]
>>
interactive cycsubg_subgroup 'a :
   sequent [squash] { <H> >- 'g IN label } -->
   sequent [squash] { <H> >- 's IN label } -->
   sequent ['ext] { <H> >- group{'g} } -->
   sequent ['ext] { <H> >- group{'s} } -->
   sequent [squash] { <H> >- isset{'a} } -->
   sequent ['ext] { <H> >- mem{'a; car{'g}} } -->
   sequent ['ext] { <H> >- cyc_subg{'s; 'g; 'a} } -->
   sequent ['ext] { <H> >- subgroup{'s; 'g} }

doc <:doc< @docoff >>
(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @tactics
  
   @begin[description]
   @item{@tactic[cycsubgSubgroupT];
      The tactic applies the @hrefrule[cycsubg_subgroup] rule
      and proves a group is a subgroup by showing it is a
      cyclic subgroup.}
   @end[description]
   @docoff
   @end[doc]
>>
let cycsubgSubgroupT = cycsubg_subgroup

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
