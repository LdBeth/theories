(*
 * Display forms for module types.
 *)

include Ocaml
include Ocaml_base_df
include Ocaml_expr_df

open Nl_debug
open Printf

open Ocaml_expr_df

let _ =
   if !debug_load then
      eprintf "Loading Ocaml_mt_df%t" eflush

(*
 * Projection.
 *)
dform mt_proj_df1 : parens :: "prec"[prec_proj] :: mt_proj{'mt1; 'mt2} =
   slot{'mt1} "." slot{'mt2}

dform mt_proj_df2 : mt_proj[@start:n, @finish:n]{'mt1; 'mt2} =
   mt_proj{'mt1; 'mt2}

(*
 * Application.
 *)
dform mt_apply_df1 : parens :: "prec"[prec_apply] :: mt_apply{'mt1; 'mt2} =
   slot{'mt1} space slot{'mt2}

dform mt_apply_df2 : mt_apply[@start:n, @finish:n]{'mt1; 'mt2} =
   mt_apply{'mt1; 'mt2}

(*
 * Functor.
 *)
dform mt_functor_df1 : parens :: "prec"[prec_fun] :: mt_functor[@name:s]{'mt1; 'mt2} =
   "_functor" space "(" slot[@name:s] space ":" space slot{'mt1} ")"
   space "->" slot{'mt2}

dform mt_functor_df2 : mt_functor[@start:n, @finish:n, @name:s]{'mt1; 'mt2} =
mt_functor[@name:s]{'mt1; 'mt2}

(*
 * Id.
 *)
dform mt_lid_df1 : mt_lid[@name:s] =
   slot[@name:s]

dform mt_lid_df2 : mt_lid{'v} =
   slot{'v}

dform mt_lid_df3 : mt_lid[@start:n, @finish:n]{'v} =
   mt_lid{'v}

dform mt_uid_df1 : mt_uid[@name:s] =
   slot[@name:s]

dform mt_uid_df2 : mt_uid{'v} =
   slot{'v}

dform mt_uid_df3 : mt_uid[@start:n, @finish:n]{'v} =
   mt_uid{'v}

(*
 * Signature.
 *)
dform mt_sig_df1 : mt_sig{'sil} =
   szone "_sig" hspace
   slot{list_expr; 'sil}
   hspace "_end" ezone

dform mt_sig_df2 : mt_sig[@start:n, @finish:n]{'sil} =
   mt_sig{'sil}

(*
 * Module type with clause.
 *)
dform mt_with_df1 : mt_with{'mt; 'wcl} =
   szone pushm[0] slot{'mt} slot{mt_with; 'wcl} popm ezone

dform mt_with_df2 : mt_with[@start:n, @finish:n]{'mt; 'wcl} =
   mt_with{'mt; 'wcl}

dform mt_with_nil_df : slot{mt_with; nil} = `""

dform mt_with_cons_df : slot{mt_with; cons{'wc; 'wcl}} =
   slot{'wc} slot{mt_with; 'wcl}

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
