(*
 * This file contains the primitive syntax and display
 * for ocaml terms.
 *)

open Debug
open Printf

let _ =
   if !debug_load then
      eprintf "Loading Ocaml_base_df%t" eflush

(************************************************************************
 * DISPLAY TERMS                                                        *
 ************************************************************************)

(*
 * Operators.
 *)
declare "["
declare "]"
declare "[|"
declare "|]"
declare "[<"
declare ">]"
declare "{"
declare "}"
declare "("
declare ")"

declare "+"
declare "-"
declare "*"
declare "/"
declare "mod"

declare "&"
declare "or"
declare "="
declare "=="
declare "::"
declare ":="
declare "."
declare ".("
declare ".["
declare ":>"
declare ";"
declare "->"
declare "|"
declare "<>"
declare ":"
declare "_"
declare "#"
declare "'"
declare "\""

declare "if"
declare "then"
declare "else"

declare "for"
declare "while"
declare "to"
declare "downto"
declare "do"
declare "done"

declare "type"
declare "exception"
declare "let"
declare "letrec"
declare "in"
declare "and"
declare "with"
declare "val"
declare "as"
declare "external"
declare "of"

declare "module"
declare "moduletype"
declare "open"
declare "sig"
declare "struct"
declare "functor"
declare "end"

declare push_indent

(*
 * Display control tags.
 *)
declare patt_format

(************************************************************************
 * DISPLAYS                                                             *
 ************************************************************************)

(*
 * Operators.
 *)
dform left_brack_df	: "["		= pushfont["bold"] `"[" popfont
dform right_brack_df	: "]"		= pushfont["bold"] `"]" popfont
dform left_array_df	: "[|"		= pushfont["bold"] `"[|" popfont
dform right_array_df	: "|]"		= pushfont["bold"] `"|]" popfont
dform left_stream_df	: "[<"		= pushfont["bold"] `"[<" popfont
dform right_stream_df	: ">]"		= pushfont["bold"] `">]" popfont
dform left_curly_df	: "{"		= pushfont["bold"] `"{" popfont
dform right_curly_df	: "}"		= pushfont["bold"] `"}" popfont
dform left_paren_df	: "("		= pushfont["bold"] `"(" popfont
dform right_paren_df	: ")"		= pushfont["bold"] `")" popfont

dform plus_df		: "+"		= pushfont["bold"] `"+" popfont
dform minus_df		: "-"		= pushfont["bold"] `"-" popfont
dform star_df		: "*"		= pushfont["bold"] `"*" popfont
dform slash_df		: "/"		= pushfont["bold"] `"/" popfont
dform mod_df_df    	: "mod"		= pushfont["bold"] `"mod" popfont

dform and_df		: "&"		= pushfont["bold"] `"&" popfont
dform or_df		: "or"		= pushfont["bold"] `"or" popfont
dform eq_df		: "="		= pushfont["bold"] `"=" popfont
dform eqeq_df		: "=="		= pushfont["bold"] `"==" popfont
dform colon_colon_df	: "::"		= pushfont["bold"] `"::" popfont
dform colon_eq_df	: ":="		= pushfont["bold"] `":=" popfont
dform dot_df		: "."		= pushfont["bold"] `"." popfont
dform array_sub_df	: ".("		= pushfont["bold"] `".(" popfont
dform string_sub_df	: ".["		= pushfont["bold"] `".[" popfont
dform coerce_df         : ":>"		= pushfont["bold"] `":>" popfont
dform semicolon_df	: ";"		= pushfont["bold"] `";" popfont
dform arrow_df		: "->"		= pushfont["bold"] `"->" popfont
dform pipe_df		: "|"		= pushfont["bold"] `"|" popfont
dform neq_df    	: "<>"		= pushfont["bold"] `"<>" popfont
dform colon_df          : ":"		= pushfont["bold"] `":" popfont
dform underscore_df	: "_"		= pushfont["bold"] `"_" popfont
dform hash_df		: "#"		= pushfont["bold"] `"#" popfont
dform quote_df		: "'"		= pushfont["bold"] `"'" popfont
dform backslash_df	: "\""		= pushfont["bold"] `"\"" popfont

dform if_df		: "if"		= pushfont["bold"] `"if" popfont
dform then_df		: "then"	= pushfont["bold"] `"then" popfont
dform else_df		: "else"	= pushfont["bold"] `"else" popfont

dform for_df		: "for"		= pushfont["bold"] `"for" popfont
dform while_df		: "while"	= pushfont["bold"] `"while" popfont
dform to_df		: "to"		= pushfont["bold"] `"to" popfont
dform downto_df		: "downto"	= pushfont["bold"] `"downto" popfont
dform do_df		: "do"		= pushfont["bold"] `"do" popfont
dform done_df		: "done"	= pushfont["bold"] `"done" popfont

dform type_df		: "type"	= pushfont["bold"] `"type" popfont
dform exception_df	: "exception"	= pushfont["bold"] `"exception" popfont
dform let_df		: "let"		= pushfont["bold"] `"let" popfont
dform letrec_df		: "letrec"	= pushfont["bold"] `"let rec" popfont
dform in_df		: "in"		= pushfont["bold"] `"in" popfont
dform and_df		: "and"		= pushfont["bold"] `"and" popfont
dform with_df		: "with"	= pushfont["bold"] `"with" popfont
dform val_df		: "val"		= pushfont["bold"] `"val" popfont
dform as_df		: "as"		= pushfont["bold"] `"as" popfont
dform external_df	: "external"	= pushfont["bold"] `"of" popfont
dform of_df		: "of"		= pushfont["bold"] `"external" popfont

dform module_df		: "module"	= pushfont["bold"] `"module" popfont
dform moduletype_df	: "moduletype"	= pushfont["bold"] `"module type" popfont
dform open_df		: "open"	= pushfont["bold"] `"open" popfont
dform sig_df		: "sig"		= pushfont["bold"] `"sig" popfont
dform struct_df		: "struct"	= pushfont["bold"] `"struct" popfont
dform functor_df	: "functor"	= pushfont["bold"] `"functor" popfont
dform end_df		: "end"		= pushfont["bold"] `"end" popfont

dform push_ident_df     : push_indent   = pushm[3]

(*
 * $Log$
 * Revision 1.3  1998/04/29 20:53:57  jyh
 * Initial working display forms.
 *
 * Revision 1.2  1998/04/29 14:48:45  jyh
 * Added ocaml_sos.
 *
 * Revision 1.1  1998/02/18 18:47:05  jyh
 * Initial ocaml semantics.
 *
 * Revision 1.1  1998/02/13 16:02:06  jyh
 * Partially implemented semantics for caml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
