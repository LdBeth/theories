(*
 * Display forms for signature items.
 *)

include Ocaml
include Ocaml_base_df
include Ocaml_expr_df

open Nl_debug
open Printf

let _ =
   if !debug_load then
      eprintf "Loading Ocaml_sig_df%t" eflush

(*
 * Display instructions.
 *)
declare sig_type_next
declare sig_name
declare sig_slt

(*
 * Signatures and structures are treated as records.
 * Their names are strings, not variables, and they do not
 * alpha-vary.  We could have external and internal names
 * like Harper's translucent sums, but we would diverge
 * from the ocaml type theory.
 *)

(*
 * Exception declarations name type constructors.
 *)
dform sig_exception_df : sig_exception[@name:s]{'tl} =
   szone push_indent "_exception" space stl{.Ocaml!"string"[@name:s]; 'tl} popm ezone

dform sig_exception_df2 : sig_exception[@start:n, @finish:n, @name:s]{'tl} =
   sig_exception[@name:s]{'tl}

(*
 * External function declaration.
 *)
dform sig_external_df1 : sig_external[@name:s]{'t; 'sl} =
   szone push_indent "_external" space slot[@name:s] space
   ":" space slot{'t}
   "=" space slot{list_expr; 'sl}

dform sig_external_df2 : sig_external[@start:n, @finish:n, @name:s]{'t; 'sl} =
   sig_external[@name:s]{'t; 'sl}

(*
 * Module declaration.
 *)
dform sig_module_df1 : sig_module[@name:s]{'mt} =
   "_module" space slot[@name] space ":" space slot{'mt}

dform sig_module_df2 : sig_module[@start:n, @finish:n, @name:s]{'mt} =
   sig_module[@name:s]{'mt}

(*
 * Module type declaration.
 *)
dform sig_module_type_df1 : sig_module_type[@name:s]{'mt} =
   szone push_indent "_moduletype" space slot[@name] space "=" space slot{'mt} popm ezone

dform sig_module_type_df2 : sig_module_type[@start:n, @finish:n, @name:s]{'mt} =
   sig_module_type[@name:s]{'mt}

(*
 * Open a module in scope.
 *)
dform sig_open_df1 : sig_open{'sl} =
   "_open" space slot{ident_expr; 'sl}

dform sig_open_df2 : sig_open[@start:n, @finish:n]{'sl} =
   sig_open{'sl}

(*
 * Type definition.
 *)
declare type_arg

dform sig_type_df1 : sig_type{cons{'sslt; 'ssltl}} =
   szone pushm[0] "_type" `" " slot{'sslt} slot{sig_type; 'ssltl} popm ezone

dform sig_type_df2 : slot{sig_type; cons{'sslt; 'ssltl}} =
   newline "_and" `" " slot{'sslt}
   slot{sig_type; 'ssltl}

dform sig_type_df3 : sig_type[@start:n, @finish:n]{'ssltl} =
   sig_type{'ssltl}

dform sig_type_df3 : slot{sig_type; nil} =
   `""

dform sslt_df1 : sslt{.Ocaml!"string"[@name:s]; nil; 't} =
   slot[@name:s] `" =" hspace slot{'t}

dform sslt_df2 : sslt{.Ocaml!"string"[@name:s]; 'sl; 't} =
   "(" slot{type_arg; 'sl} ")" `" " slot[@name:s] `" =" hspace slot{'t}

dform type_arg_cons_df1 : slot{type_arg; cons{.Ocaml!"string"[@name:s]; nil}} =
   "'" slot[@name]

dform type_arg_cons_df2 : slot{type_arg; cons{.Ocaml!"string"[@name:s]; 'sl}} =
   "'" slot[@name] `", " slot{type_arg; 'sl}

(*
 * Value declaration.
 *)
dform sig_value_df1 : sig_value[@name:s]{'t} =
   szone push_indent "_val" `" " slot[@name:s] `" : " slot{'t} popm ezone

dform sig_value_df2 : sig_value[@start:n, @finish:n, @name:s]{'t} =
   sig_value[@name:s]{'t}

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
