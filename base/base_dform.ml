(*
 * Display forms for basic objects.
 *)

include Perv
include Nuprl_font

open Printf
open Nl_debug

open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Dform
open Rformat

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Base_dform%t" eflush

(*
 * Display forms.
 *)
declare bvar{var[@v:v]}
declare " "
declare "^"
declare "_"
declare "{"
declare "}"
declare "$"
declare "["
declare "]"
declare ";"
declare "\\"

(*
 * Variables.
 *)
dform var_src_df : mode[src] :: var[@v:v] =
   `"'" slot[@v:s]

dform var_prl_df : mode[prl] :: var[@v:v] =
   slot[@v:s]

dform so_var1_df : var[@v:v]{'x1} = var[@v:v] "[" 'x1  "]"

dform so_var2_df : var[@v:v]{'x1; 'x2} =
   szone var[@v:v] "[" pushm[0] 'x1 ";" space 'x2 popm "]" ezone

dform so_var3_df : var[@v:v]{'x1; 'x2; 'x3} =
   szone var[@v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 popm "]" ezone

dform so_var4_df : var[@v:v]{'x1; 'x2; 'x3; 'x4} =
   szone var[@v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 popm "]" ezone

dform so_var5_df : var[@v:v]{'x1; 'x2; 'x3; 'x4; 'x5} =
   szone var[@v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 popm "]" ezone

dform so_var6_df : var[@v:v]{'x1; 'x2; 'x3; 'x4; 'x5; 'x6} =
   szone var[@v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 ";"
                       space 'x6 popm "]" ezone

dform so_var7_df : var[@v:v]{'x1; 'x2; 'x3; 'x4; 'x5; 'x6; 'x7} =
   szone var[@v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 ";"
                       space 'x6 ";"
                       space 'x7 popm "]" ezone

dform so_var8_df : var[@v:v]{'x1; 'x2; 'x3; 'x4; 'x5; 'x6; 'x7; 'x8} =
   szone var[@v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 ";"
                       space 'x6 ";"
                       space 'x7 ";"
                       space 'x8 popm "]" ezone

dform so_var9_df : var[@v:v]{'x1; 'x2; 'x3; 'x4; 'x5; 'x6; 'x7; 'x8; 'x9} =
   szone var[@v:v] "[" pushm[0] 'x1 ";"
                       space 'x2 ";"
                       space 'x3 ";"
                       space 'x4 ";"
                       space 'x5 ";"
                       space 'x6 ";"
                       space 'x7 ";"
                       space 'x8 ";"
                       space 'x9 popm "]" ezone

mldform bvar_df : bvar{var[@v:v]} format_term buf =
   format_string buf v

(*
 * Rewriting.
 *)
dform rewrite_df : mode["src"] :: "rewrite"{'redex; 'contractum} =
   slot{'redex} `"<-->" slot{'contractum}

dform rewrite_df : mode["prl"] :: "rewrite"{'redex; 'contractum} =
   szone pushm[3] slot{'redex} " " longleftrightarrow " " slot{'contractum} popm ezone

(*
 * For sequents.
 * In the "format" function,
 *    i is the hyp number, if it is known
 *    cflag is true if the last term was a conclusion
 *    t is the term to be printed.
 *)
mldform sequent_src_df : mode["src"] :: "sequent"{'ext; 'seq} format_term buf =
   (let rec format (i, cflag, sflag, t) =
      let sep = if sflag then "; " else "" in
	 if is_context_term t then
            (* This is a context hypothesis *)
	    let v, subterm, values = dest_context t in
	       format_string buf sep;
	       format_space buf;
	       format_term buf NOParens (mk_so_var_term v values);
	       format (i + 1, cflag, true, subterm)

         else if is_hyp_term t then
            let v, a, b = dest_hyp t in
	       format_string buf sep;
	       format_space buf;
	       format_string buf v;
	       format_string buf ". ";
               format_term buf NOParens a;
               format (i + 1, false, true, b)

         else if t = null_concl then
            ()

         else if is_concl_term t then
            let a, b = dest_concl t in
	       format_string buf (if cflag then sep else " >>");
               format_space buf;
               format_term buf NOParens a;
               format (i + 1, true, true, b)

         else
            raise (RefineError ("sequent_print", TermMatchError (seq, "not a sequent")))
   in
      format_szone buf;
      format_pushm buf 0;
      format_string buf "sequent {";
      format (1, false, false, seq);
      format_string buf " }";
      format_popm buf;
      format_ezone buf)

mldform sequent_prl_df : mode["prl"] :: "sequent"{'ext; 'seq} format_term buf =
   let format_arg = function
      [] ->
         ()
    | args ->
         format_string buf "[";
         let rec format = function
            arg::t ->
               format_term buf NOParens arg;
               if t <> [] then
                  format_string buf "; ";
               format t
          | [] ->
               ()
         in
            format args;
            format_string buf "]";
            format_space buf
   in
   let rec format (i, cflag, sflag, t) =
      let lead = (string_of_int i) ^ ". " in
      let sep = if sflag then "; " else "" in
      let format_xbreak = if sflag then format_break else format_ibreak in
	 if is_context_term t then
            (* This is a context hypothesis *)
	    let v, subterm, values = dest_context t in
	       format_xbreak buf lead sep;
	       format_term buf NOParens (mk_so_var_term v values);
	       format (i + 1, cflag, true, subterm)

         else if is_hyp_term t then
            let v, a, b = dest_hyp t in
               format_xbreak buf lead sep;
	       format_string buf v;
	       format_string buf ": ";
               format_term buf NOParens a;
               format (i + 1, false, true, b)

         else if t = null_concl then
            ()

         else if is_concl_term t then
            let a, b = dest_concl t in
               format_xbreak buf
	       (if cflag then "   " else "\159  ")
	       (if cflag then sep else " \159 ");
               format_term buf NOParens a;
               format (i + 1, true, true, b)

         else
            format_term buf NOParens t
   in
      format_szone buf;
      format_pushm buf 0;
      format_arg (dest_xlist ext);
      format (1, false, false, seq);
      format_popm buf;
      format_ezone buf

(************************************************************************
 * COMMANDS                                                             *
 ************************************************************************)

dform space_df : " " = space
dform hat_df : "^" = `"^"
dform underscore_df : "_" = `"_"
dform left_curly_df : "{" = `"{"
dform right_curly_df : "}" = `"}"
dform dollar_df : "$" = `"$"
dform left_brack_df : "[" = `"["
dform right_brack_df : "]" = `"]"
dform semicolor_df : ";" = `";"
dform newline_df : "\\" = \newline

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
