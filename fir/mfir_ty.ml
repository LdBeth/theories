(*!
 * @spelling{exn tailcalls th ty tyRawInt tyFloat tyApply tyEnum var}
 *
 * @begin[doc]
 * @module[Mfir_ty]
 *
 * The @tt[Mfir_ty] module declares terms to represent the FIR type system.
 * @end[doc]
 *
 * ------------------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.  Additional
 * information about the system is available at
 * http://www.metaprl.org/
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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
 * Author: Brian Emre Aydemir
 * @email{emre@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)

extends Base_theory
extends Mfir_basic

(**************************************************************************
 * Declarations.
 **************************************************************************)

(*
 * DROPPED: TyPointer.        Not worrying about this optimization.
 * TODO:    TyFrame.          I'm confused.
 * DROPPED: TyCase.           Part of the (unsound) FIR object system.
 * DROPPED: TyObject.         Part of the (unsound) FIR object system.
 * DROPPED: TyDelayed.        Not doing type inference.
 * TODO:    frame.            I'm confused.
 *)

(*!
 * @begin[doc]
 * @terms
 * @modsubsection{Numbers}
 *
 * The type @tt[tyInt] refers to signed, 31-bit, ML-style integers.  The type
 * @tt{tyEnum[i:n]} includes the integers $@{0,@ldots,i-1@}$.  The native
 * integer type @tt{tyRawInt[precision:n, sign:s]} includes integers of
 * varying bit precisions (8, 16, 32, and 64) and signedness (``signed'' or
 * ``unsigned'').  The type @tt{tyFloat[precision:n]} includes floating-point
 * values of a specified bit-precision (32, 64, or 80).
 * @end[doc]
 *)

declare tyInt
declare tyEnum[i:n]
declare tyRawInt[precision:n, sign:s]
declare tyFloat[precision:n]

(*!
 * @begin[doc]
 * @modsubsection{Functions}
 *
 * The type @tt[tyFun] represents functions that take an argument of
 * type @tt[arg_type], and return a result of type @tt[res_type].  Strictly
 * speaking, all function calls in the FIR are tailcalls, so functions never
 * return.  They usually have a return type of @tt{tyEnum[0]}.  The @MetaPRL
 * representation, though, represents functions in curried form.  Thus,
 * @tt[res_type] maybe another @tt[tyFun] term.
 * @end[doc]
 *)

declare tyFun{ 'arg_type; 'res_type }

(*!
 * @begin[doc]
 * @modsubsection{Aggregate data}
 *
 * The type @tt[tyUnion] represents values in a polymorphic union type.  The
 * @tt[ty_var] subterm refers to a polymorphic union definition (see
 * @hrefterm[tyDefUnion]), which is instantiated at the types in @tt[ty_list].
 * The third subterm is an integer set that selects a subset of the union
 * cases.  Union cases are indexed starting at zero.
 * @end[doc]
 *)

declare tyUnion{ 'ty_var; 'ty_list; 'intset }

(*!
 * @begin[doc]
 *
 * The type @tt[tyTuple] represents tuples with arity $n$ if @tt[ty_list]
 * is a list of $n$ types. The parameter @tt[tc] is a tuple class, which
 * can either be ``normal'' or ``box''.  ``box'' tuples must always have
 * arity one, and are used pass arbitrary values (such as floating-point
 * values or raw integers) as polymorphic values.
 * @end[doc]
 *)

declare tyTuple[tc:s]{ 'ty_list }

(*!
 * @begin[doc]
 *
 * Arrays are similar to tuples, except all the elements of an array have the
 * same type, and arrays may have arbitrary, non-negative dimension.
 * @end[doc]
 *)

declare tyArray{ 'ty }

(*!
 * @begin[doc]
 *
 * The unsafe type @tt[tyRawData] represents arbitrary data.  It is commonly
 * used to represent data aggregates in imperative programming languages, such
 * as C, that allow assignment of values to a data area without regard for the
 * type.
 * @end[doc]
 *) declare tyRawData

(*!
 * @begin[doc]
 * @modsubsection{Polymorphism}
 *
 * The term @tt[tyVar] represents a type variable.
 * @end[doc]
 *)

declare tyVar{ 'ty_var }

(*!
 * @begin[doc]
 *
 * The term @tt{tyApply@{'ty_var@; 'ty_list@}} applies the types @tt[ty_list]
 * to a type function given by @tt[ty_var].
 * @end[doc]
 *)

declare tyApply{ 'ty_var; 'ty_list }

(*!
 * @begin[doc]
 *
 * The existential type @tt[tyExists] defines a type @tt[ty] abstracted over a
 * type variable @tt[t].  The term @tt[tyAll] defines a polymorphic type,
 * where @tt[ty] is restricted to be either @tt[tyFun] or another @tt[tyAll].
 * This corresponds to value restriction @cite["ullman:sml"].
 * @end[doc]
 *)

declare tyExists{ t. 'ty['t] }
declare tyAll{ t. 'ty['t] }

(*!
 * @begin[doc]
 *
 * If @tt[var] is a ``packed'' existential value (see @hrefterm[atomTyPack]),
 * then the term @tt[tyProject] is the $i^{th}$ type in the packing, where
 * indexing starts at zero.
 * @end[doc]
 *)

declare tyProject[i:n]{ 'var }

(*!
 * @begin[doc]
 * @modsubsection{Type definitions}
 *
 * Type definitions defined parameterized types and unions.  The term
 * @tt[tyDefPoly] abstracts a type @tt[ty] over @tt[t].
 * @end[doc]
 *)

declare tyDefPoly{ t. 'ty['t] }

(*!
 * @begin[doc]
 *
 * The term @tt[tyDefUnion] is used to define a disjoint union.  The parameter
 * @tt[str] should either be ``normal'' or ``exn''.  Unions are tagged with
 * ``exn'' when they have more than 100 cases.  The subterms @tt[cases] should
 * be a list of @tt[unionCase] terms, and each @tt[unionCase] term should have
 * a list of @tt[unionCaseElt] terms.  A union case can be viewed as a tuple
 * space in which each field is tagged with a boolean indicating whether or
 * not it is mutable.
 * @end[doc]
 *)

declare unionCaseElt{ 'ty; 'boolean }
declare unionCase{ 'elts }
declare tyDefUnion[str:s]{ 'cases }

(*!
 * @docoff
 *)

(**************************************************************************
 * Display forms.
 **************************************************************************)

(*
 * Numbers.
 *)

dform tyInt_df : except_mode[src] ::
   tyInt =
   mathbbZ sub{31}

dform tyEnum_df : except_mode[src] ::
   tyEnum[i:n] =
   bf["enum"] sub{slot[i:n]}

dform tyRawInt_df : except_mode[src] ::
   tyRawInt[precision:n, sign:s] =
   mathbbZ sub{slot[precision:n]} sup{bf{slot[sign:s]}}

dform tyFloat_df : except_mode[src] ::
   tyFloat[precision:n] =
   mathbbR sub{slot[precision:n]}

(*
 * Functions.
 *)

dform tyFun_df : except_mode[src] ::
   tyFun{ 'arg_type; 'res_type } =
   `"(" slot{'arg_type} rightarrow slot{'res_type} `")"

(*
 * Aggregate data.
 *)

dform tyUnion_df : except_mode[src] ::
   tyUnion{ 'ty_var; 'ty_list; 'intset } =
   bf["union"] `"(" slot{'ty_var} slot{'ty_list} `", " slot{'intset} `")"

dform tyTuple_df : except_mode[src] ::
   tyTuple[tc:s]{ 'ty_list } =
   bf["tuple"] sub{bf[tc:s]} slot{'ty_list}

dform tyArray_df : except_mode[src] ::
   tyArray{ 'ty } =
   `"(" slot{'ty} `" " bf["array"] `")"

dform tyRawData_df : except_mode[src] ::
   tyRawData =
   bf["data"]

(*
 * Polymorphism.
 *)

dform tyVar_df : except_mode[src] ::
   tyVar{ 'ty_var } =
   bf["tvar"] `"(" slot{'ty_var} `")"

dform tyApply_df : except_mode[src] ::
   tyApply{ 'ty_var; 'ty_list } =
   slot{'ty_var} slot{'ty_list}

dform tyExists_df : except_mode[src] ::
   tyExists{ t. 'ty } =
   exists slot{'t} `". " slot{'ty}

dform tyAll_df : except_mode[src] ::
   tyAll{ t. 'ty } =
   forall slot{'t} `". " slot{'ty}

dform tyProject_df : except_mode[src] ::
   tyProject[i:n]{ 'var } =
   slot{'var} `"." slot[i:n]

(*
 * Type definitions.
 *)

dform tyDefPoly_df : except_mode[src] :: except_mode[tex] ::
   tyDefPoly{ t. 'ty } =
   lambda uparrow slot{'t} `". " slot{'ty}

dform tyDefPoly_df : mode[tex] ::
   tyDefPoly{ t. 'ty } =
   izone `"\\Lambda " ezone slot{'t} `". " slot{'ty}

dform unionCaseElt : except_mode[src] ::
   unionCaseElt{ 'ty; 'boolean } =
   `"(" slot{'ty} `"," slot{'boolean} `")"

dform unionCase_df : except_mode[src] ::
   unionCase{ 'elts } =
   `"+" slot{'elts}

dform tyDefUnion_df : except_mode[src] ::
   tyDefUnion[str:s]{ 'cases } =
   bf["union"] sub{bf[str:s]} slot{'cases}