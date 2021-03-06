(*
 * The Mfir_termOp module provides term construction
 * and deconstruction terms for FIR theory terms.
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

extends Mfir_option
extends Mfir_bool
extends Mfir_token
extends Mfir_record
extends Mfir_int
extends Mfir_int_set
extends Mfir_list
extends Mfir_ty
extends Mfir_exp

open Lm_symbol
open Refiner.Refiner.TermType

val none_term : term
val is_none_term : term -> bool

val some_term : term
val is_some_term : term -> bool
val mk_some_term : term -> term
val dest_some_term : term -> term

val true_term : term
val is_true_term : term -> bool

val false_term : term
val is_false_term : term -> bool

val or_term : term
val is_or_term : term -> bool
val mk_or_term : term -> term -> term
val dest_or_term : term -> term * term

val and_term : term
val is_and_term : term -> bool
val mk_and_term : term -> term -> term
val dest_and_term : term -> term * term

val not_term : term
val is_not_term : term -> bool
val mk_not_term : term -> term
val dest_not_term : term -> term

val ifthenelse_term : term
val is_ifthenelse_term : term -> bool
val mk_ifthenelse_term : term -> term -> term -> term
val dest_ifthenelse_term : term -> term * term * term

val token_term : term
val is_token_term : term -> bool
val mk_token_term : string -> term
val dest_token_term : term -> string

val token_eq_term : term
val is_token_eq_term : term -> bool
val mk_token_eq_term : term -> term -> term
val dest_token_eq_term : term -> term * term

val recordEnd_term : term
val is_recordEnd_term : term -> bool

val record_term : term
val is_record_term : term -> bool
val mk_record_term : string -> term -> term -> term
val dest_record_term : term -> string * term * term

val field_term : term
val is_field_term : term -> bool
val mk_field_term : string -> term -> term
val dest_field_term : term -> string * term

val field_mem_term : term
val is_field_mem_term : term -> bool
val mk_field_mem_term : string -> term -> term
val dest_field_mem_term : term -> string * term

val number_term : term
val is_number_term : term -> bool
val mk_number_term : Lm_num.num -> term
val dest_number_term : term -> Lm_num.num

val add_term : term
val is_add_term : term -> bool
val mk_add_term : term -> term -> term
val dest_add_term : term -> term * term

val sub_term : term
val is_sub_term : term -> bool
val mk_sub_term : term -> term -> term
val dest_sub_term : term -> term * term

val mul_term : term
val is_mul_term : term -> bool
val mk_mul_term : term -> term -> term
val dest_mul_term : term -> term * term

val div_term : term
val is_div_term : term -> bool
val mk_div_term : term -> term -> term
val dest_div_term : term -> term * term

val rem_term : term
val is_rem_term : term -> bool
val mk_rem_term : term -> term -> term
val dest_rem_term : term -> term * term

val minus_term : term
val is_minus_term : term -> bool
val mk_minus_term : term -> term
val dest_minus_term : term -> term

val int_min_term : term
val is_int_min_term : term -> bool
val mk_int_min_term : term -> term -> term
val dest_int_min_term : term -> term * term

val int_max_term : term
val is_int_max_term : term -> bool
val mk_int_max_term : term -> term -> term
val dest_int_max_term : term -> term * term

val int_eq_term : term
val is_int_eq_term : term -> bool
val mk_int_eq_term : term -> term -> term
val dest_int_eq_term : term -> term * term

val int_neq_term : term
val is_int_neq_term : term -> bool
val mk_int_neq_term : term -> term -> term
val dest_int_neq_term : term -> term * term

val int_lt_term : term
val is_int_lt_term : term -> bool
val mk_int_lt_term : term -> term -> term
val dest_int_lt_term : term -> term * term

val int_le_term : term
val is_int_le_term : term -> bool
val mk_int_le_term : term -> term -> term
val dest_int_le_term : term -> term * term

val int_gt_term : term
val is_int_gt_term : term -> bool
val mk_int_gt_term : term -> term -> term
val dest_int_gt_term : term -> term * term

val int_ge_term : term
val is_int_ge_term : term -> bool
val mk_int_ge_term : term -> term -> term
val dest_int_ge_term : term -> term * term

val nil_term : term
val is_nil_term : term -> bool

val cons_term : term
val is_cons_term : term -> bool
val mk_cons_term : term -> term -> term
val dest_cons_term : term -> term * term

val length_term : term
val is_length_term : term -> bool
val mk_length_term : term -> term
val dest_length_term : term -> term

val nth_elt_term : term
val is_nth_elt_term : term -> bool
val mk_nth_elt_term : term -> term -> term
val dest_nth_elt_term : term -> term * term

val interval_term : term
val is_interval_term : term -> bool
val mk_interval_term : term -> term -> term
val dest_interval_term : term -> term * term

val intset_term : term
val is_intset_term : term -> bool
val mk_intset_term : Lm_num.num -> string -> term -> term
val dest_intset_term : term -> Lm_num.num * string * term

val member_term : term
val is_member_term : term -> bool
val mk_member_term : term -> term -> term
val dest_member_term : term -> term * term

val normalize_term : term
val is_normalize_term : term -> bool
val mk_normalize_term : term -> term
val dest_normalize_term : term -> term

val subset_term : term
val is_subset_term : term -> bool
val mk_subset_term : term -> term -> term
val dest_subset_term : term -> term * term

val set_eq_term : term
val is_set_eq_term : term -> bool
val mk_set_eq_term : term -> term -> term
val dest_set_eq_term : term -> term * term

val union_term : term
val is_union_term : term -> bool
val mk_union_term : term -> term -> term
val dest_union_term : term -> term * term

val intset_max_term : term
val is_intset_max_term : term -> bool
val mk_intset_max_term : Lm_num.num -> string -> term
val dest_intset_max_term : term -> Lm_num.num * string

val enum_max_term : term
val is_enum_max_term : term -> bool

val mutable_term : term
val is_mutable_term : term -> bool

val immutable_term : term
val is_immutable_term : term -> bool

val mutable_ty_term : term
val is_mutable_ty_term : term -> bool
val mk_mutable_ty_term : term -> term -> term
val dest_mutable_ty_term : term -> term * term

val tyDefPoly_term : term
val is_tyDefPoly_term : term -> bool
val mk_tyDefPoly_term : var -> term -> term
val dest_tyDefPoly_term : term -> var * term

val frameSubField_term : term
val is_frameSubField_term : term -> bool
val mk_frameSubField_term : term -> term -> term
val dest_frameSubField_term : term -> term * term

val tyDefUnion_term : term
val is_tyDefUnion_term : term -> bool
val mk_tyDefUnion_term : term -> term
val dest_tyDefUnion_term : term -> term

val tyDefDTuple_term : term
val is_tyDefDTuple_term : term -> bool
val mk_tyDefDTuple_term : term -> term
val dest_tyDefDTuple_term : term -> term

val tyInt_term : term
val is_tyInt_term : term -> bool

val tyEnum_term : term
val is_tyEnum_term : term -> bool
val mk_tyEnum_term : Lm_num.num -> term
val dest_tyEnum_term : term -> Lm_num.num

val tyRawInt_term : term
val is_tyRawInt_term : term -> bool
val mk_tyRawInt_term : Lm_num.num -> string -> term
val dest_tyRawInt_term : term -> Lm_num.num * string

val tyFloat_term : term
val is_tyFloat_term : term -> bool
val mk_tyFloat_term : Lm_num.num -> term
val dest_tyFloat_term : term -> Lm_num.num

val tyFun_term : term
val is_tyFun_term : term -> bool
val mk_tyFun_term : term -> term -> term
val dest_tyFun_term : term -> term * term

val tyUnion_term : term
val is_tyUnion_term : term -> bool
val mk_tyUnion_term : term -> term -> term -> term
val dest_tyUnion_term : term -> term * term * term

val tyTuple_term : term
val is_tyTuple_term : term -> bool
val mk_tyTuple_term : string -> term -> term
val dest_tyTuple_term : term -> string * term

val tyDTuple_term : term
val is_tyDTuple_term : term -> bool
val mk_tyDTuple_term : term -> term -> term
val dest_tyDTuple_term : term -> term * term

val tyTag_term : term
val is_tyTag_term : term -> bool
val mk_tyTag_term : term -> term -> term
val dest_tyTag_term : term -> term * term

val tyArray_term : term
val is_tyArray_term : term -> bool
val mk_tyArray_term : term -> term
val dest_tyArray_term : term -> term

val tyRawData_term : term
val is_tyRawData_term : term -> bool

val tyFrame_term : term
val is_tyFrame_term : term -> bool
val mk_tyFrame_term : term -> term -> term
val dest_tyFrame_term : term -> term * term

val tyVar_term : term
val is_tyVar_term : term -> bool
val mk_tyVar_term : term -> term
val dest_tyVar_term : term -> term

val tyApply_term : term
val is_tyApply_term : term -> bool
val mk_tyApply_term : term -> term -> term
val dest_tyApply_term : term -> term * term

val tyExists_term : term
val is_tyExists_term : term -> bool
val mk_tyExists_term : var -> term -> term
val dest_tyExists_term : term -> var * term

val tyAll_term : term
val is_tyAll_term : term -> bool
val mk_tyAll_term : var -> term -> term
val dest_tyAll_term : term -> var * term

val tyProject_term : term
val is_tyProject_term : term -> bool
val mk_tyProject_term : Lm_num.num -> term -> term
val dest_tyProject_term : term -> Lm_num.num * term

val notEnumOp_term : term
val is_notEnumOp_term : term -> bool
val mk_notEnumOp_term : Lm_num.num -> term
val dest_notEnumOp_term : term -> Lm_num.num

val uminusIntOp_term : term
val is_uminusIntOp_term : term -> bool

val notIntOp_term : term
val is_notIntOp_term : term -> bool

val absIntOp_term : term
val is_absIntOp_term : term -> bool

val uminusRawIntOp_term : term
val is_uminusRawIntOp_term : term -> bool
val mk_uminusRawIntOp_term : Lm_num.num -> string -> term
val dest_uminusRawIntOp_term : term -> Lm_num.num * string

val notRawIntOp_term : term
val is_notRawIntOp_term : term -> bool
val mk_notRawIntOp_term : Lm_num.num -> string -> term
val dest_notRawIntOp_term : term -> Lm_num.num * string

val rawBitFieldOp_term : term
val is_rawBitFieldOp_term : term -> bool
val mk_rawBitFieldOp_term : Lm_num.num -> string -> term -> term -> term
val dest_rawBitFieldOp_term : term -> Lm_num.num * string * term * term

val uminusFloatOp_term : term
val is_uminusFloatOp_term : term -> bool
val mk_uminusFloatOp_term : Lm_num.num -> term
val dest_uminusFloatOp_term : term -> Lm_num.num

val absFloatOp_term : term
val is_absFloatOp_term : term -> bool
val mk_absFloatOp_term : Lm_num.num -> term
val dest_absFloatOp_term : term -> Lm_num.num

val sinFloatOp_term : term
val is_sinFloatOp_term : term -> bool
val mk_sinFloatOp_term : Lm_num.num -> term
val dest_sinFloatOp_term : term -> Lm_num.num

val cosFloatOp_term : term
val is_cosFloatOp_term : term -> bool
val mk_cosFloatOp_term : Lm_num.num -> term
val dest_cosFloatOp_term : term -> Lm_num.num

val tanFloatOp_term : term
val is_tanFloatOp_term : term -> bool
val mk_tanFloatOp_term : Lm_num.num -> term
val dest_tanFloatOp_term : term -> Lm_num.num

val asinFloatOp_term : term
val is_asinFloatOp_term : term -> bool
val mk_asinFloatOp_term : Lm_num.num -> term
val dest_asinFloatOp_term : term -> Lm_num.num

val acosFloatOp_term : term
val is_acosFloatOp_term : term -> bool
val mk_acosFloatOp_term : Lm_num.num -> term
val dest_acosFloatOp_term : term -> Lm_num.num

val atanFloatOp_term : term
val is_atanFloatOp_term : term -> bool
val mk_atanFloatOp_term : Lm_num.num -> term
val dest_atanFloatOp_term : term -> Lm_num.num

val sinhFloatOp_term : term
val is_sinhFloatOp_term : term -> bool
val mk_sinhFloatOp_term : Lm_num.num -> term
val dest_sinhFloatOp_term : term -> Lm_num.num

val coshFloatOp_term : term
val is_coshFloatOp_term : term -> bool
val mk_coshFloatOp_term : Lm_num.num -> term
val dest_coshFloatOp_term : term -> Lm_num.num

val tanhFloatOp_term : term
val is_tanhFloatOp_term : term -> bool
val mk_tanhFloatOp_term : Lm_num.num -> term
val dest_tanhFloatOp_term : term -> Lm_num.num

val expFloatOp_term : term
val is_expFloatOp_term : term -> bool
val mk_expFloatOp_term : Lm_num.num -> term
val dest_expFloatOp_term : term -> Lm_num.num

val logFloatOp_term : term
val is_logFloatOp_term : term -> bool
val mk_logFloatOp_term : Lm_num.num -> term
val dest_logFloatOp_term : term -> Lm_num.num

val log10FloatOp_term : term
val is_log10FloatOp_term : term -> bool
val mk_log10FloatOp_term : Lm_num.num -> term
val dest_log10FloatOp_term : term -> Lm_num.num

val sqrtFloatOp_term : term
val is_sqrtFloatOp_term : term -> bool
val mk_sqrtFloatOp_term : Lm_num.num -> term
val dest_sqrtFloatOp_term : term -> Lm_num.num

val ceilFloatOp_term : term
val is_ceilFloatOp_term : term -> bool
val mk_ceilFloatOp_term : Lm_num.num -> term
val dest_ceilFloatOp_term : term -> Lm_num.num

val floorFloatOp_term : term
val is_floorFloatOp_term : term -> bool
val mk_floorFloatOp_term : Lm_num.num -> term
val dest_floorFloatOp_term : term -> Lm_num.num

val intOfFloatOp_term : term
val is_intOfFloatOp_term : term -> bool
val mk_intOfFloatOp_term : Lm_num.num -> term
val dest_intOfFloatOp_term : term -> Lm_num.num

val intOfRawIntOp_term : term
val is_intOfRawIntOp_term : term -> bool
val mk_intOfRawIntOp_term : Lm_num.num -> string -> term
val dest_intOfRawIntOp_term : term -> Lm_num.num * string

val floatOfIntOp_term : term
val is_floatOfIntOp_term : term -> bool
val mk_floatOfIntOp_term : Lm_num.num -> term
val dest_floatOfIntOp_term : term -> Lm_num.num

val floatOfFloatOp_term : term
val is_floatOfFloatOp_term : term -> bool
val mk_floatOfFloatOp_term : Lm_num.num -> Lm_num.num -> term
val dest_floatOfFloatOp_term : term -> Lm_num.num * Lm_num.num

val floatOfRawIntOp_term : term
val is_floatOfRawIntOp_term : term -> bool
val mk_floatOfRawIntOp_term : Lm_num.num -> Lm_num.num -> string -> term
val dest_floatOfRawIntOp_term : term -> Lm_num.num * Lm_num.num * string

val rawIntOfIntOp_term : term
val is_rawIntOfIntOp_term : term -> bool
val mk_rawIntOfIntOp_term : Lm_num.num -> string -> term
val dest_rawIntOfIntOp_term : term -> Lm_num.num * string

val rawIntOfEnumOp_term : term
val is_rawIntOfEnumOp_term : term -> bool
val mk_rawIntOfEnumOp_term : Lm_num.num -> string -> Lm_num.num -> term
val dest_rawIntOfEnumOp_term : term -> Lm_num.num * string * Lm_num.num

val rawIntOfFloatOp_term : term
val is_rawIntOfFloatOp_term : term -> bool
val mk_rawIntOfFloatOp_term : Lm_num.num -> string -> Lm_num.num -> term
val dest_rawIntOfFloatOp_term : term -> Lm_num.num * string * Lm_num.num

val rawIntOfRawIntOp_term : term
val is_rawIntOfRawIntOp_term : term -> bool
val mk_rawIntOfRawIntOp_term : Lm_num.num -> string -> Lm_num.num -> string -> term
val dest_rawIntOfRawIntOp_term : term -> Lm_num.num * string * Lm_num.num * string

val rawIntOfPointerOp_term : term
val is_rawIntOfPointerOp_term : term -> bool
val mk_rawIntOfPointerOp_term : Lm_num.num -> string -> term
val dest_rawIntOfPointerOp_term : term -> Lm_num.num * string

val pointerOfRawIntOp_term : term
val is_pointerOfRawIntOp_term : term -> bool
val mk_pointerOfRawIntOp_term : Lm_num.num -> string -> term
val dest_pointerOfRawIntOp_term : term -> Lm_num.num * string

val dtupleOfDTupleOp_term : term
val is_dtupleOfDTupleOp_term : term -> bool
val mk_dtupleOfDTupleOp_term : term -> term -> term
val dest_dtupleOfDTupleOp_term : term -> term * term

val unionOfUnionOp_term : term
val is_unionOfUnionOp_term : term -> bool
val mk_unionOfUnionOp_term : term -> term -> term -> term -> term
val dest_unionOfUnionOp_term : term -> term * term * term * term

val rawDataOfFrameOp_term : term
val is_rawDataOfFrameOp_term : term -> bool
val mk_rawDataOfFrameOp_term : term -> term -> term
val dest_rawDataOfFrameOp_term : term -> term * term

val andEnumOp_term : term
val is_andEnumOp_term : term -> bool
val mk_andEnumOp_term : Lm_num.num -> term
val dest_andEnumOp_term : term -> Lm_num.num

val orEnumOp_term : term
val is_orEnumOp_term : term -> bool
val mk_orEnumOp_term : Lm_num.num -> term
val dest_orEnumOp_term : term -> Lm_num.num

val xorEnumOp_term : term
val is_xorEnumOp_term : term -> bool
val mk_xorEnumOp_term : Lm_num.num -> term
val dest_xorEnumOp_term : term -> Lm_num.num

val plusIntOp_term : term
val is_plusIntOp_term : term -> bool

val minusIntOp_term : term
val is_minusIntOp_term : term -> bool

val mulIntOp_term : term
val is_mulIntOp_term : term -> bool

val divIntOp_term : term
val is_divIntOp_term : term -> bool

val remIntOp_term : term
val is_remIntOp_term : term -> bool

val lslIntOp_term : term
val is_lslIntOp_term : term -> bool

val lsrIntOp_term : term
val is_lsrIntOp_term : term -> bool

val asrIntOp_term : term
val is_asrIntOp_term : term -> bool

val andIntOp_term : term
val is_andIntOp_term : term -> bool

val orIntOp_term : term
val is_orIntOp_term : term -> bool

val xorIntOp_term : term
val is_xorIntOp_term : term -> bool

val maxIntOp_term : term
val is_maxIntOp_term : term -> bool

val minIntOp_term : term
val is_minIntOp_term : term -> bool

val eqIntOp_term : term
val is_eqIntOp_term : term -> bool

val neqIntOp_term : term
val is_neqIntOp_term : term -> bool

val ltIntOp_term : term
val is_ltIntOp_term : term -> bool

val leIntOp_term : term
val is_leIntOp_term : term -> bool

val gtIntOp_term : term
val is_gtIntOp_term : term -> bool

val geIntOp_term : term
val is_geIntOp_term : term -> bool

val cmpIntOp_term : term
val is_cmpIntOp_term : term -> bool

val plusRawIntOp_term : term
val is_plusRawIntOp_term : term -> bool
val mk_plusRawIntOp_term : Lm_num.num -> string -> term
val dest_plusRawIntOp_term : term -> Lm_num.num * string

val minusRawIntOp_term : term
val is_minusRawIntOp_term : term -> bool
val mk_minusRawIntOp_term : Lm_num.num -> string -> term
val dest_minusRawIntOp_term : term -> Lm_num.num * string

val mulRawIntOp_term : term
val is_mulRawIntOp_term : term -> bool
val mk_mulRawIntOp_term : Lm_num.num -> string -> term
val dest_mulRawIntOp_term : term -> Lm_num.num * string

val divRawIntOp_term : term
val is_divRawIntOp_term : term -> bool
val mk_divRawIntOp_term : Lm_num.num -> string -> term
val dest_divRawIntOp_term : term -> Lm_num.num * string

val remRawIntOp_term : term
val is_remRawIntOp_term : term -> bool
val mk_remRawIntOp_term : Lm_num.num -> string -> term
val dest_remRawIntOp_term : term -> Lm_num.num * string

val slRawIntOp_term : term
val is_slRawIntOp_term : term -> bool
val mk_slRawIntOp_term : Lm_num.num -> string -> term
val dest_slRawIntOp_term : term -> Lm_num.num * string

val srRawIntOp_term : term
val is_srRawIntOp_term : term -> bool
val mk_srRawIntOp_term : Lm_num.num -> string -> term
val dest_srRawIntOp_term : term -> Lm_num.num * string

val andRawIntOp_term : term
val is_andRawIntOp_term : term -> bool
val mk_andRawIntOp_term : Lm_num.num -> string -> term
val dest_andRawIntOp_term : term -> Lm_num.num * string

val orRawIntOp_term : term
val is_orRawIntOp_term : term -> bool
val mk_orRawIntOp_term : Lm_num.num -> string -> term
val dest_orRawIntOp_term : term -> Lm_num.num * string

val xorRawIntOp_term : term
val is_xorRawIntOp_term : term -> bool
val mk_xorRawIntOp_term : Lm_num.num -> string -> term
val dest_xorRawIntOp_term : term -> Lm_num.num * string

val maxRawIntOp_term : term
val is_maxRawIntOp_term : term -> bool
val mk_maxRawIntOp_term : Lm_num.num -> string -> term
val dest_maxRawIntOp_term : term -> Lm_num.num * string

val minRawIntOp_term : term
val is_minRawIntOp_term : term -> bool
val mk_minRawIntOp_term : Lm_num.num -> string -> term
val dest_minRawIntOp_term : term -> Lm_num.num * string

val rawSetBitFieldOp_term : term
val is_rawSetBitFieldOp_term : term -> bool
val mk_rawSetBitFieldOp_term : Lm_num.num -> string -> term -> term -> term
val dest_rawSetBitFieldOp_term : term -> Lm_num.num * string * term * term

val eqRawIntOp_term : term
val is_eqRawIntOp_term : term -> bool
val mk_eqRawIntOp_term : Lm_num.num -> string -> term
val dest_eqRawIntOp_term : term -> Lm_num.num * string

val neqRawIntOp_term : term
val is_neqRawIntOp_term : term -> bool
val mk_neqRawIntOp_term : Lm_num.num -> string -> term
val dest_neqRawIntOp_term : term -> Lm_num.num * string

val ltRawIntOp_term : term
val is_ltRawIntOp_term : term -> bool
val mk_ltRawIntOp_term : Lm_num.num -> string -> term
val dest_ltRawIntOp_term : term -> Lm_num.num * string

val leRawIntOp_term : term
val is_leRawIntOp_term : term -> bool
val mk_leRawIntOp_term : Lm_num.num -> string -> term
val dest_leRawIntOp_term : term -> Lm_num.num * string

val gtRawIntOp_term : term
val is_gtRawIntOp_term : term -> bool
val mk_gtRawIntOp_term : Lm_num.num -> string -> term
val dest_gtRawIntOp_term : term -> Lm_num.num * string

val geRawIntOp_term : term
val is_geRawIntOp_term : term -> bool
val mk_geRawIntOp_term : Lm_num.num -> string -> term
val dest_geRawIntOp_term : term -> Lm_num.num * string

val cmpRawIntOp_term : term
val is_cmpRawIntOp_term : term -> bool
val mk_cmpRawIntOp_term : Lm_num.num -> string -> term
val dest_cmpRawIntOp_term : term -> Lm_num.num * string

val plusFloatOp_term : term
val is_plusFloatOp_term : term -> bool
val mk_plusFloatOp_term : Lm_num.num -> term
val dest_plusFloatOp_term : term -> Lm_num.num

val minusFloatOp_term : term
val is_minusFloatOp_term : term -> bool
val mk_minusFloatOp_term : Lm_num.num -> term
val dest_minusFloatOp_term : term -> Lm_num.num

val mulFloatOp_term : term
val is_mulFloatOp_term : term -> bool
val mk_mulFloatOp_term : Lm_num.num -> term
val dest_mulFloatOp_term : term -> Lm_num.num

val divFloatOp_term : term
val is_divFloatOp_term : term -> bool
val mk_divFloatOp_term : Lm_num.num -> term
val dest_divFloatOp_term : term -> Lm_num.num

val remFloatOp_term : term
val is_remFloatOp_term : term -> bool
val mk_remFloatOp_term : Lm_num.num -> term
val dest_remFloatOp_term : term -> Lm_num.num

val maxFloatOp_term : term
val is_maxFloatOp_term : term -> bool
val mk_maxFloatOp_term : Lm_num.num -> term
val dest_maxFloatOp_term : term -> Lm_num.num

val minFloatOp_term : term
val is_minFloatOp_term : term -> bool
val mk_minFloatOp_term : Lm_num.num -> term
val dest_minFloatOp_term : term -> Lm_num.num

val eqFloatOp_term : term
val is_eqFloatOp_term : term -> bool
val mk_eqFloatOp_term : Lm_num.num -> term
val dest_eqFloatOp_term : term -> Lm_num.num

val neqFloatOp_term : term
val is_neqFloatOp_term : term -> bool
val mk_neqFloatOp_term : Lm_num.num -> term
val dest_neqFloatOp_term : term -> Lm_num.num

val ltFloatOp_term : term
val is_ltFloatOp_term : term -> bool
val mk_ltFloatOp_term : Lm_num.num -> term
val dest_ltFloatOp_term : term -> Lm_num.num

val leFloatOp_term : term
val is_leFloatOp_term : term -> bool
val mk_leFloatOp_term : Lm_num.num -> term
val dest_leFloatOp_term : term -> Lm_num.num

val gtFloatOp_term : term
val is_gtFloatOp_term : term -> bool
val mk_gtFloatOp_term : Lm_num.num -> term
val dest_gtFloatOp_term : term -> Lm_num.num

val geFloatOp_term : term
val is_geFloatOp_term : term -> bool
val mk_geFloatOp_term : Lm_num.num -> term
val dest_geFloatOp_term : term -> Lm_num.num

val cmpFloatOp_term : term
val is_cmpFloatOp_term : term -> bool
val mk_cmpFloatOp_term : Lm_num.num -> term
val dest_cmpFloatOp_term : term -> Lm_num.num

val atan2FloatOp_term : term
val is_atan2FloatOp_term : term -> bool
val mk_atan2FloatOp_term : Lm_num.num -> term
val dest_atan2FloatOp_term : term -> Lm_num.num

val powerFloatOp_term : term
val is_powerFloatOp_term : term -> bool
val mk_powerFloatOp_term : Lm_num.num -> term
val dest_powerFloatOp_term : term -> Lm_num.num

val ldExpFloatIntOp_term : term
val is_ldExpFloatIntOp_term : term -> bool
val mk_ldExpFloatIntOp_term : Lm_num.num -> term
val dest_ldExpFloatIntOp_term : term -> Lm_num.num

val eqEqOp_term : term
val is_eqEqOp_term : term -> bool
val mk_eqEqOp_term : term -> term
val dest_eqEqOp_term : term -> term

val neqEqOp_term : term
val is_neqEqOp_term : term -> bool
val mk_neqEqOp_term : term -> term
val dest_neqEqOp_term : term -> term

val atomNil_term : term
val is_atomNil_term : term -> bool
val mk_atomNil_term : term -> term
val dest_atomNil_term : term -> term

val atomInt_term : term
val is_atomInt_term : term -> bool
val mk_atomInt_term : term -> term
val dest_atomInt_term : term -> term

val atomEnum_term : term
val is_atomEnum_term : term -> bool
val mk_atomEnum_term : Lm_num.num -> term -> term
val dest_atomEnum_term : term -> Lm_num.num * term

val atomRawInt_term : term
val is_atomRawInt_term : term -> bool
val mk_atomRawInt_term : Lm_num.num -> string -> term -> term
val dest_atomRawInt_term : term -> Lm_num.num * string * term

val atomFloat_term : term
val is_atomFloat_term : term -> bool
val mk_atomFloat_term : Lm_num.num -> string -> term
val dest_atomFloat_term : term -> Lm_num.num * string

val atomVar_term : term
val is_atomVar_term : term -> bool
val mk_atomVar_term : term -> term
val dest_atomVar_term : term -> term

val atomLabel_term : term
val is_atomLabel_term : term -> bool
val mk_atomLabel_term : string -> string -> term -> term -> term
val dest_atomLabel_term : term -> string * string * term * term

val atomSizeof_term : term
val is_atomSizeof_term : term -> bool
val mk_atomSizeof_term : term -> term -> term
val dest_atomSizeof_term : term -> term * term

val atomConst_term : term
val is_atomConst_term : term -> bool
val mk_atomConst_term : term -> term -> term -> term
val dest_atomConst_term : term -> term * term * term

val atomTyApply_term : term
val is_atomTyApply_term : term -> bool
val mk_atomTyApply_term : term -> term -> term -> term
val dest_atomTyApply_term : term -> term * term * term

val atomTyPack_term : term
val is_atomTyPack_term : term -> bool
val mk_atomTyPack_term : term -> term -> term -> term
val dest_atomTyPack_term : term -> term * term * term

val atomTyUnpack_term : term
val is_atomTyUnpack_term : term -> bool
val mk_atomTyUnpack_term : term -> term
val dest_atomTyUnpack_term : term -> term

val atomUnop_term : term
val is_atomUnop_term : term -> bool
val mk_atomUnop_term : term -> term -> term
val dest_atomUnop_term : term -> term * term

val atomBinop_term : term
val is_atomBinop_term : term -> bool
val mk_atomBinop_term : term -> term -> term -> term
val dest_atomBinop_term : term -> term * term * term

val allocArray_term : term
val is_allocArray_term : term -> bool
val mk_allocArray_term : term -> term -> term
val dest_allocArray_term : term -> term * term

val allocVArray_term : term
val is_allocVArray_term : term -> bool
val mk_allocVArray_term : term -> term -> term -> term
val dest_allocVArray_term : term -> term * term * term

val allocMalloc_term : term
val is_allocMalloc_term : term -> bool
val mk_allocMalloc_term : term -> term -> term
val dest_allocMalloc_term : term -> term * term

val allocFrame_term : term
val is_allocFrame_term : term -> bool
val mk_allocFrame_term : term -> term -> term
val dest_allocFrame_term : term -> term * term

val letAtom_term : term
val is_letAtom_term : term -> bool
val mk_letAtom_term : term -> term -> var -> term -> term
val dest_letAtom_term : term -> term * term * var * term

val letExt_term : term
val is_letExt_term : term -> bool
val mk_letExt_term : string -> term -> term -> term -> var -> term -> term
val dest_letExt_term : term -> string * term * term * term * var * term

val tailCall_term : term
val is_tailCall_term : term -> bool
val mk_tailCall_term : term -> term -> term
val dest_tailCall_term : term -> term * term

val matchCase_term : term
val is_matchCase_term : term -> bool
val mk_matchCase_term : term -> term -> term
val dest_matchCase_term : term -> term * term

val matchExp_term : term
val is_matchExp_term : term -> bool
val mk_matchExp_term : term -> term -> term
val dest_matchExp_term : term -> term * term

val letAlloc_term : term
val is_letAlloc_term : term -> bool
val mk_letAlloc_term : term -> var -> term -> term
val dest_letAlloc_term : term -> term * var * term

val letSubscript_term : term
val is_letSubscript_term : term -> bool
val mk_letSubscript_term : term -> term -> term -> var -> term -> term
val dest_letSubscript_term : term -> term * term * term * var * term

val setSubscript_term : term
val is_setSubscript_term : term -> bool
val mk_setSubscript_term : term -> term -> term -> term -> term -> term
val dest_setSubscript_term : term -> term * term * term * term * term

val letGlobal_term : term
val is_letGlobal_term : term -> bool
val mk_letGlobal_term : term -> term -> var -> term -> term
val dest_letGlobal_term : term -> term * term * var * term

val setGlobal_term : term
val is_setGlobal_term : term -> bool
val mk_setGlobal_term : term -> term -> term -> term -> term
val dest_setGlobal_term : term -> term * term * term * term
