doc <:doc<
   @spelling{MUL DIV cc}
   @module[M_x86_asm]

   This module defines our representation of x86 assembly code.
   The one difference here, compared to traditional approaches,
   is that we continue to use variable scoping.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2003 Jason Hickey, Caltech

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

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Base_theory

(*************************************************************************
 * Operands.
 *)

doc <:doc<
   @modsection{x86 operands}
>>
declare ImmediateNumber[i:n]
declare ImmediateLabel[label:s]{'R}
declare ImmediateCLabel[label:s]{'R}
declare Register{'v}
declare SpillMemory{'label}
declare SpillRegister{'v; 'label}
declare ContextRegister[label:s]
declare MemReg{'r}
declare MemRegOff[i:n]{'r}
declare MemRegRegOffMul[off:n, mul:n]{'r1; 'r2}

(*************************************************************************
 * Condition codes.
 *)

doc <:doc<
   @modsection{Condition codes}

   These condition codes are used in the @tt[Jcc] (conditional jump)
   instruction below.
>>
declare CC[cc:s]

(*************************************************************************
 * Instructions.
 *)

doc <:doc<
   @modsection{Instructions}

   We want the assembly to have ``semi-functional'' property,
   meaning that registers are immutable.  The register allocator
   will coalesce registers, creating implicit assignments
   in the process.

   This presents an interesting problem for the x86, since it
   uses the two-operand instruction form.  To get around this,
   we define a normal two-operand instruction set for @emph{memory}
   operands.  Then we define a three-operand set for register
   destination operands.  Again, the allocator is responsible
   for making sure the <<'dst>> and the first <<'src>> register are the
   same.

   Further, for simplicity, we categorize instructions into
   several kinds:

   @begin[itemize]
   @item{@tt[Mov] defines a new register from an arbitrary operand}
   @item{<<'Inst1['opname]>>: a normal one-operand instruction}
   @item{<<'Inst2['opname]>>: this is a normal two-operand instruction}
   @item{<<'Inst3['opname]>>: a MUL/DIV instruction}
   @item{$@tt[Shift][<<'opname>>]$: a shift instruction}
   @item{$@tt[Cmp][<<'opname>>]$: a comparison@; both operands are sources}
   @item{$@tt[Set][<<'opname>>]$: the set/cc instruction}
   @end[itemize]
>>
declare Mov{'src; dst. 'rest['dst]}
declare Spill[opcode:s]{'src; dst. 'rest['dst]}
declare Inst1[opcode:s]{'dst; 'rest}
declare Inst1[opcode:s]{'src; dst. 'rest['dst]}
declare Inst2[opcode:s]{'src; 'dst; 'rest}
declare Inst2[opcode:s]{'src1; 'src2; dst. 'rest['dst]}
declare Inst3[opcode:s]{'src1; 'src2; 'src3; dst2, dst3. 'rest['dst2; 'dst3]}
declare Shift[opcode:s]{'src; 'dst; 'rest}
declare Shift[opcode:s]{'src1; 'src2; dst. 'rest['dst]}
declare Cmp[opcode:s]{'src1; 'src2; 'rest}
declare Set[opcode:s]{'cc; 'dst; 'rest['dst]}
declare Set[opcode:s]{'cc; 'src; dst. 'rest['dst]}

(*
 * Various forms of tailcalls.
 * The tailcall takes the arguments in a list.
 *)
declare AsmArgNil
declare AsmArgCons{'a; 'rest}
declare Jmp[opcode:s]{'label; 'args}

(*
 * For conditional jumps, pretend that it is a real
 * conditional.  The printer will have to insert a label.
 *)
declare Jcc[opcode:s]{'cc; 'rest1; 'rest2}

doc <:doc<
   This is a pseudo-instruction that calls the garbage collector to ensure
   that the specified number of words is available.  The parameters are the
   live registers (normally the parameters to the current function).
>>
declare AsmReserve[words:n]{'params}

doc <:doc<
   The @tt[Comment] instruction is not a real instruction.  It is used to
   include a comment in the program output; the text is given in the string
   parameter.
>>
declare Comment[comment:s]{'rest}

doc <:doc<
   The program initialization is wrapped in the @tt[Init] term; we don't
   include the initialization code in the program output.
>>
declare Init{'rest}

(*************************************************************************
 * Programs.
 *)

doc <:doc<
   @modsection{Programs}

   A program is a set of recursive definitions, just like it is
   in the IR.  The labels in the assembly correspond to functions,
   and the register allocator is responsible for ensuring that the
   calling convention is respected.
>>
declare LabelAsm[label:s]{'R}

declare LabelRec{R1. 'fields['R1]; R2. 'rest['R2]}
declare LabelDef{'label; 'code; 'rest}
declare LabelEnd

declare LabelFun{v. 'insts['v]}

doc docoff

(************************************************************************
 * Display forms.
 *)

(*
 * Operands.
 *)
dform immediate_number_df : ImmediateNumber[i:n] =
   `"$" slot[i:n]

dform immediate_label_df : ImmediateLabel[label:s]{'R} =
   slot{'R} `"." slot[label:s]

dform immediate_clabel_df : ImmediateCLabel[label:s]{'R} =
   `"$" slot{'R} `"." slot[label:s]

dform register_df : Register{'v} =
   `"%" slot{'v}

dform spill_memory_df : SpillMemory{'spill} =
   bf["spill["] slot{'spill} bf["]"]

dform spill_register_df : SpillRegister{'v; 'spill} =
   bf["spill["] slot{'v} bf[", "] slot{'spill} bf["]"]

dform context_register_df : ContextRegister[name:s] =
   bf["context["] slot[name:s] bf["]"]

dform mem_reg_df : MemReg{'r} =
   `"(%" slot{'r} `")"

dform mem_reg_off_df : MemRegOff[i:n]{'r} =
   slot[i:n] `"(%" slot{'r} `")"

dform mem_reg_reg_off_mul_df : MemRegRegOffMul[off:n, mul:n]{'r1; 'r2} =
   `"(%" slot{'r1} `",%" slot{'r2} `"," slot[off:n] `"," slot[mul:n] `")"

(*
 * Condition codes.
 *)
dform cc_df : CC[cc:s] =
   bf{slot[cc:s]}

(*
 * Instructions.
 *)
dform mov_df1 : Mov{'src; dst. 'rest} =
    bf["mov "] slot{'src} bf[", %"] slot{'dst} bf[" /* LET */"] hspace slot{'rest}

dform set_spill_df : Spill["set"]{'src; dst. 'rest} =
    bf["mov "] slot{'src} bf[", spill["] slot{'dst} bf["] /* SPILL(set) */"] hspace slot{'rest}

dform get_spill_df : Spill["get"]{'src; dst. 'rest} =
    bf["mov "] slot{'src} bf[", %"] slot{'dst} bf[" /* SPILL(get) */"] hspace slot{'rest}

dform copy_spill_df : Spill["copy"]{'src; dst. 'rest} =
    bf["mov "] slot{'src} bf[", %"] slot{'dst} bf[" /* SPILL(copy) */"] hspace slot{'rest}

dform inst1_df1 : Inst1[opcode:s]{'dst; 'rest} =
    bf{slot[opcode:s]} `" " slot{'dst} bf[" /* Memory operand */"] hspace slot{'rest}

dform inst1_df2 : Inst1[label:s]{'src; dst. 'rest} =
    bf{slot[label:s]} `" " slot{'src} bf[", %"] slot{'dst} hspace slot{'rest}

dform inst2_df1 : Inst2[label:s]{'src; 'dst; 'rest} =
    bf{slot[label:s]} `" " slot{'src} bf[", "] slot{'dst} bf[" /* Memory operand */"] hspace slot{'rest}

dform inst2_df2 : Inst2[label:s]{'src1; 'src2; dst. 'rest} =
    bf{slot[label:s]} `" " slot{'src1} bf[", "] slot{'src2} bf[", "] slot{'dst} hspace slot{'rest}

dform inst3_df : Inst3[label:s]{'src1; 'src2; 'src3; dst2, dst3. 'rest} =
    bf{slot[label:s]} `" " slot{'src1} bf[", "] slot{'src2} bf[", %"] slot{'dst2} bf[", %"] slot{'dst3} hspace slot{'rest}

dform shift_df1 : Shift[label:s]{'src; 'dst; 'rest} =
    bf{slot[label:s]} `" " slot{'src} bf[", "] slot{'dst} bf[" /* Memory operand */"] hspace slot{'rest}

dform shift_df2 : Shift[label:s]{'src1; 'src2; dst. 'rest} =
    bf{slot[label:s]} `" " slot{'src1} bf[", "] slot{'src2} bf[", %"] slot{'dst} hspace slot{'rest}

dform cmp_df : Cmp[opcode:s]{'src1; 'src2; 'rest} =
   bf{slot[opcode:s]} `" " slot{'src1} bf[", "] slot{'src2} hspace slot{'rest}

dform set_df : Set[opcode:s]{'cc; 'src; dst. 'rest} =
   bf{slot[opcode:s]} `"[" 'cc `"] " slot{'src} bf[", %"] slot{'dst} hspace slot{'rest}

dform jmp_df : Jmp[opcode:s]{'src; 'args} =
   bf{slot[opcode:s]} `" " slot{'src} bf["("] slot{'args} bf[")"]

dform jcc_df : Jcc[opcode:s]{'cc; 'rest1; 'rest2} =
   szone pushm[0] pushm[3] bf{slot[opcode:s]} `"[" 'cc `"]" bf[" begin"] hspace slot{'rest1} popm hspace bf["end"] popm ezone
   hspace slot{'rest2}

dform asm_arg_cons_df1 : AsmArgCons{'a1; AsmArgCons{'a2; 'rest}} =
   slot{'a1} `", " AsmArgCons{'a2; 'rest}

dform asm_arg_cons_df2 : AsmArgCons{'a; AsmArgNil} =
   slot{'a}

dform asm_arg_cons_df3 : AsmArgCons{'a1; 'a2} =
   slot{'a1} `" :: " slot{'a2}

dform asm_arg_nil_df : AsmArgNil =
   `"()"

(*
 * Reserve.
 *)
dform asm_reserve_df : AsmReserve[words:n]{'args} =
   bf["reserve "] slot[words:n] bf[" words args("] slot{'args} bf[") in"]

(*
 * Comments.
 *)
dform comment_df : Comment[comment:s]{'rest} =
   `"/* Comment: " slot[comment:s] `" */" hspace slot{'rest}

dform init_df : Init{'rest} =
   szone pushm[0] pushm[3] bf["initialize"]
   hspace slot{'rest}
   popm hspace
   bf["end"]
   popm ezone

(*
 * Programs.
 *)
dform label_fun_df : LabelFun{v. 'insts} =
   `"/* param " slot{'v} `" */" hspace slot{'insts}

dform label_rec_df : LabelRec{R1. 'fields; R2. 'rest} =
   szone `"/* LabelRecFields[" slot{'R1} `"] begins here */"
   hspace slot{'fields} `"/* LabelRecFields[" slot{'R1} `"] ends here */" ezone
   hspace `"/* LabelRecBody[" slot{'R2} `"] begins here */" hspace slot{'rest}

dform label_def_df : LabelDef{'label; 'insts; 'rest} =
   szone pushm[3] slot{'label} hspace slot{'insts} popm ezone hspace slot{'rest}

dform label_end_df : LabelEnd =
   `""

dform label_asm_df : LabelAsm[label:s]{'R} =
   slot{'R} `"." slot[label:s] `":"

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
