(*
 * Operational semantics for expressions.
 * In many forms, the order of evaluation is not specified,
 * so we force the sub-expressions to be values.  For instance,
 * the expressions "e1" and "e2" in (e1, e2) must be values,
 * because the compiler spec doesn't tell us which form is to
 * be evaluated first.
 *
 * Those who wish to write tuples with side-effects, should wrap them
 * in a "let" to force the order of side-effects.
 *     let x = e1 in
 *     let y = e2 in
 *        (x, y)
 *)

include Ocaml
include Ocaml_base_sos

(************************************************************************
 * CONSTANTS                                                            *
 ************************************************************************)

(*
 * Constants.
 *)
axiom bool_equiv :
   sequent { 'H >- value_equiv{'S; "bool"[$f:s]; "bool"[$f:s]; type_bool}
             
axiom bool_value :
   sequent { 'H >- is_value{"bool"[$f:s]} }

axiom char_equiv : 
   sequent { 'H >- value_equiv{'S; "char"[$c:s]; "char"[$c:s]; type_char} }

axiom char_value :
   sequent { 'H >- is_value{"char"[$c:s]} }

axiom int_equiv :
   sequent { 'H >- value_equiv{'S; "int"[$i:n]; "int"[$i:n]; type_int} }

axiom int_value :
   sequent { 'H >- is_value{'S; "int"[$i:n]} }

(************************************************************************
 * CONTROL EXPRESSIONS                                                  *
 ************************************************************************)

(*
 * We just throw off the types in a type cast during reduction.
 * We <em>do</em> restrict the equivalence rule, but of course
 * the rule can be bypassed by performing the rewrite step.
 *)
axiom cast_equiv :
   sequent { 'H >- equiv{'S; 'e1; 'e2; 't; 'exn} } -->
   sequent { 'H >- equiv{'S; cast{'e1; 't}; cast{'e2; 't}; 't; 'exn} }

axiom cast_value_equiv :
   sequent { 'H >- value_equiv{'S; 'e1; 'e2; 't} } -->
   sequent { 'H >- value_equiv{'S; cast{'e1; 't}; cast{'e2; 't}; 't} }

rewrite cast_eval :
   cast{'e; 't} <--> 'e

(*
 * Conditional.
 *)
axiom ifthenelse_equiv :
   sequent { 'H >- equiv{'S; 'e1; 'e4; 't; 'exn} } -->
   sequent { 'H >- equiv{state{'S; 'e1}; 'e2; 'e5; 't; 'exn} } -->
   sequent { 'H >- equiv{state{'S; 'e1}; 'e3; 'e6; 't; 'exn} } -->
   sequent { 'H >- equiv{'S; ifthenelse{'e1; 'e2; 'e3}; ifthenelse{'e4; 'e5; 'e6}; 't; 'exn} }

axiom ifthenelse_value_equiv :
   sequent { 'H >- value_equiv{'S; 'e1; 'e4; 't} } -->
   sequent { 'H >- value_equiv{'S; 'e2; 'e5; 't} } -->
   sequent { 'H >- value_equiv{'S; 'e3; 'e6; 't} } -->
   sequent { 'H >- value_equiv{'S; ifthenelse{'e1; 'e2; 'e3}; ifthenelse{'e4; 'e5; 'e6}; 't} }

rewrite ifthenelse_eval :
   eval{'S; ifthenelse{'e1; 'e2; 'e3}} <-->
      spread{eval{'S; 'e1}; S2, flag.
         eval{'S2; ifthenelse{flag; 'e2; 'e3}}

rewrite ifthenelse_true :
   ifthenelse{bool["true":s]; 'e1; 'e2} <--> 'e1

rewrite ifthenelse_false :
   ifthenelse{bool["false":s]; 'e1; 'e2} <--> 'e2

rewrite ifthenelse_raise :
   ifthenelse{raise{'e}; 'e1; 'e2} <--> raise{'e}

(*
 * Loops.
 * We don't give equivalence rules for these terms.
 * Instead, we define unrollings.  We will rely on the
 * induction forms of the type theory to supply
 * reasoning about loops.
 *)
rewrite for_upto_eval :
   is_value{'S; 'e1} -->
   is_value{'S; 'e2} -->
      (for_upto{'e1; 'e2; x. 'e3['x]} <-->
          ifthenelse{le_int{'e1; 'e2};
                     sequence{'e3['e1]; for_upto{add{'e1; "int"[1]}; 'e2; x. 'e3['x]}};
                     unit})

rewrite for_downto_eval :
   is_value{'S; 'e1} -->
   is_value{'S; 'e2} -->
      (for_downto{'e1; 'e2; x. 'e3['x]} <-->
          ifthenelse{ge_int{'e1; 'e2};
                     sequence{'e3['e1]; for_downto{sub{'e1; "int"[1]}; 'e2; x. 'e3['x]}};
                     unit})
                       
rewrite while_eval :
   "while"{'e1; 'e2} <-->
      ifthenelse{'e1; sequence{'e2; while{'e1; 'e2}}; unit}

(************************************************************************
 * ASSIGNMENT                                                           *
 ************************************************************************)

(*
 * Assignment.
 * Two cases:
 *    *1. lval is a value
 *    *2. rval is a value
 *)
axiom assign_left_value_equiv : 't :
   sequent { 'H >- value_equiv{'S; 'e1; 'e3; type_ref{'t}} } -->
   sequent { 'H >- equiv{'S; 'e2; 'e4; 't; 'exn} } -->
   sequent { 'H >- equiv{'S; assign{'e1; 'e2}; assign{'e3; 'e4}; type_unit; 'exn} }

axiom assign_right_value_equiv : 't :
   sequent { 'H >- equiv{'S; 'e1; 'e3; type_ref{'t}; 'exn} } -->
   sequent { 'H >- value_equiv{'S; 'e2; 'e4; 't} } -->
   sequent { 'H >- equiv{'S; assign{'e1; 'e2}; assign{'e3; 'e4}; type_unit; 'exn} }

rewrite assign_eval :
   or{is_value{'S; 'e1}; is_value{'S; 'e2}} -->
      (eval{'S; assign{'e1; 'e2}} <-->
          eval{'S; assign{expr{'S; 'e1}; expr{'S; 'e2}}})

rewrite assign_redex :
   is_value{'e2} -->
      (eval{'S; assign{address[$name:s]; 'e2}} <-->
          "value"{replace{'S; address[$n:s]; expr_value{'S; 'e2}}; unit})

rewrite assign_left_raise :
   is_value{'S; 'e2} -->
      (assign{raise{'e1}; 'e2} <--> raise{'e1})

rewrite assign_right_raise :
   is_value{'S; 'e1} -->
      (assign{'e1; raise{'e2}} <--> raise{'e2})

(************************************************************************
 * LISTS                                                                *
 ************************************************************************)

(*
 * Lists are handled differently from other sequences because they
 * are not mutable.
 *
 * Three cases:
 *    *1. car val, cdr val
 *    *2. car arb, cdr val
 *    *3. car val, cdr arb
 *)
axiom list_nil_equiv :
   sequent { 'H >- is_type{'t} } -->
   sequent { 'H >- value_equiv{'S; list{nil}; list{nil}; type_list{'t}} }

axiom list_cons_equiv :
   sequent { 'H >- value_equiv{'S; 'e1; 'e2; 't} } -->
   sequent { 'H >- value_equiv{'S; list{'el1}; list{'el2}; type_list{'t}} } -->
   sequent { 'H >- value_equiv{'S; list{cons{'e1; 'el1}}; list{cons{'e2; 'el2}}; type_list{'t}} }

axiom list_hd_equiv :
   sequent { 'H >- value_equiv{'S; 'e1; 'e2; 't} } -->
   sequent { 'H >- equiv{'S; list{'el1}; list{'el2}; type_list{'t}; 'exn} } -->
   sequent { 'H >- equiv{'S; list{cons{'e1; 'el1}}; list{cons{'e2; 'el2}}; type_list{'t}; 'exn} }

axiom list_tl_equiv :
   sequent { 'H >- equiv{'S; 'e1; 'e2; 't; 'exn} } -->
   sequent { 'H >- value_equiv{'S; list{'el1}; list{'el2}; type_list{'t}} } -->
   sequent { 'H >- equiv{'S; list{cons{'e1; 'el1}}; list{cons{'e2; 'el2}}; type_list{'t}; 'exn} }

axiom nil_equiv :
   sequent { 'H >- is_type{'t} } -->
   sequent { 'H >- value_equiv{'S; nil; nil; type_list{'t}} }

axiom cons_equiv :
   sequent { 'H >- value_equiv{'S; 'e1; 'e3; 't} } -->
   sequent { 'H >- value_equiv{'S; 'e2; 'e4; type_list{'t}} } -->
   sequent { 'H >- value_equiv{'S; cons{'e1; 'e2}; cons{'e3; 'e4}; type_list{'t}} }

axiom cons_hd_equiv :
   sequent { 'H >- value_equiv{'S; 'e1; 'e3; 't} } -->
   sequent { 'H >- equiv{'S; 'e2; 'e4; type_list{'t}; 'exn} } -->
   sequent { 'H >- equiv{'S; cons{'e1; 'e2}; cons{'e3; 'e4}; type_list{'t}; 'exn} }

axiom cons_tl_equiv :
   sequent { 'H >- equiv{'S; 'e1; 'e3; 't; 'exn} } -->
   sequent { 'H >- value_equiv{'S; 'e2; 'e4; type_list{'t}} } -->
   sequent { 'H >- equiv{'S; cons{'e1; 'e2}; cons{'e3; 'e4}; type_list{'t}; 'exn} }

rewrite list_cons_eval :
   "or"{is_value{'S; 'e}; is_value{'S; 'el}} -->
      (eval{'S; list{cons{'e; 'el}}} <-->
          eval{'S; list{cons{expr{'S; 'e1}; expr{'S; list{'el}}}}})

rewrite cons_eval :
   "or"{is_value{'S; 'e1}; is_value{'S; 'e2}} -->
      (eval{'S; cons{'e1; 'e2}} <--> eval{'S; cons{expr{'S; 'e1}; expr{'S; 'e2}}})

(************************************************************************
 * STRINGS                                                              *
 ************************************************************************)

(*
 * When a string is evaluated, it adds itself to the state.
 * This is a little different from standard ocaml, because
 * string constants are added to the state once--at load time.
 * Undoubtably, we will have to fix this at some point.
 *)
axiom string_equiv : :
   sequent { 'H >- equiv{'S; string[$s:s]; string[$s:s]; type_string; type_void} }

rewrite string_eval :
   eval{'S; string[$s:s]} <--> allocate{'S; string[$s:s]}

(*
 * Subscripting.
 * It is also reasonable to add rules for when the
 * array is not a value, but the subscript is.
 *
 * Six cases:
 *     *1. array value, subscript value, in bounds
 *      2. array arb, subscript value, in bounds
 *      3. array value, subscript arb, in bounds
 *      + same three cases,but out-of-bounds
 *)
axiom string_subscript_value_equiv : :
   sequent { 'H >- value_equiv{'S; 'e1; 'e3; type_string} } -->
   sequent { 'H >- value_equiv{'S; 'e2; 'e4; type_int} } -->
   sequent { 'H >- prim_string_bounds{'S; 'e1; 'e2} } -->
   sequent { 'H >- value_equiv{'S; string_subscript{'e1; 'e2}; string_subscript{'e3; 'e4}; type_char} }

rewrite string_subscript_eval :
   or{is_value{'S; 'e1}; is_value{'S; 'e2}} -->
      (eval{'S; string_subscript{'e1; 'e2}} <-->
          eval{'S; string_subscript{expr{'S; 'e1}; expr{'S; 'e2}}})

rewrite string_subscript_redex :
   (eval{'S; string_subscript{address[$name:s]; "int"[$index:n]}} <-->
       eval{'S; prim_string_subscript{lookup{'S; address[$name:s]}; "int"[$index:n]}})

rewrite string_subscript_left_raise :
   is_value{'S; 'e2} -->
      (eval{'S; string_subscript{"raise"{'e1}; 'e2}} <--> eval{'S; "raise"{'e1}})

rewrite string_subscript_right_raise :
   is_value{'S; 'e1} -->
      (eval{'S; string_subscript{'e1; "raise"{'e2}}} <--> eval{'S; "raise"{'e2}})

(*
 * Set a character.
 * Eight cases:
 *    *1. all values
 *     2. array arb, subscript value, value value, in bounds
 *     3. array value, subscript arb, value value, in bounds
 *     4. array value, subscript value, value arb, in bounds
 *     + same four cases, but out-of-bounds
 *)
axiom string_set_equiv :
   sequent { 'H >- value_equiv{'S; 'e1; 'e4; type_string} } -->
   sequent { 'H >- value_equiv{'S; 'e2; 'e5; type_int }} -->
   sequent { 'H >- value_equiv{'S; 'e3; 'e6; type_char }} -->
   sequent { 'H >- string_bounds{'S; 'e1; 'e2} } -->
   sequent { 'H >- equiv{'S; string_set{'e1; 'e2; 'e3}; string_set{'e4; 'e5; 'e6}; type_unit; 'exn} }

rewrite string_set_eval :
   two_values{is_value{'S; 'e1}; is_value{'S; 'e2}; is_value{'S; 'e3}} -->
      (eval{'S; string_set{'e1; 'e2; 'e3}} <-->
          eval{'S; string_set{expr{'S; 'e1}; expr{'S; 'e2}; expr{'S; 'e3}}})

rewrite string_set_redex :
   eval{'S; address[$name:s]; "int"[$index:n]; "char"[$value:s]} <-->
      set{'S; address[$name:s];
          prim_string_set{lookup{'S; address[$name:s]};
                          "int"[$index:n];
                          "char"[$value:s]}}

rewrite string_set_array_raise :
   (is_value{'S; 'e1} & is_value{'S; 'e2} & is_value{'S; 'e3}) -->
      (eval{'S; string_set{"raise"{'e1}; 'e2; 'e3}} <-->
          eval{'S; "raise"{'e1}})
   
rewrite string_set_index_raise :
   (is_value{'S; 'e1} & is_value{'S; 'e2} & is_value{'S; 'e3}) -->
      (eval{'S; string_set{'e1; "raise"{'e2}; 'e3}} <-->
          eval{'S; "raise"{'e2}})
   
rewrite string_set_value_raise :
   (is_value{'S; 'e1} & is_value{'S; 'e2} & is_value{'S; 'e3}) -->
      (eval{'S; string_set{'e1; 'e2; "raise"{'e3}}} <-->
          eval{'S; "raise"{'e3}})
   
(************************************************************************
 * ARRAYS                                                               *
 ************************************************************************)

(*
 * Arrays.
 * We _could_ allow one entry not to be a value, but that's too hard.
 * Force all the entries to be values.
 *)
axiom array_cons_equiv :
   sequent { 'H >- value_equiv{'S; 'e1; 'e2; 't} } -->
   sequent { 'H >- equiv{'S; array{'el1}; array{'el2}; type_array{'t}; 'exn} } -->
   sequent { 'H >- equiv{'S; array{cons{'e1; 'el1}}; array{cons{'e2; 'el2}}; type_array{'t}; 'exn} }

(*
 * The evaluation of an array performs an allocation.
 *)
rewrite array_eval :
   is_value{'S; 'el} -->
      (eval{'S; array{'el}} <-->
          spread{eval{'S; 'el}; S2, l.
             allocate{'S2; array{'l}}})

(*
 * Get an element.
 * Six cases:
 *     *1. array value, index value, in bounds
 *      2. array arb, index value, in bounds
 *      3. array value, index arb, in bounds
 *      + same three cases but out-of-bounds
 *)
axiom array_subscript_equiv : :
   sequent { 'H >- value_equiv{'S; 'e1; 'e3; type_array{'t}} } -->
   sequent { 'H >- value_equiv{'S; 'e2; 'e4; type_int} } -->
   sequent { 'H >- prim_array_bounds{'S; 'e1; 'e2} } -->
   sequent { 'H >- value_equiv{'S; array_subscript{'e1; 'e2}; array_subscript{'e3; 'e4}; 't}}

rewrite array_subscript_eval :
   "or"{is_value{'S; 'e1}; is_value{'S; 'e2}} -->
      (eval{'S; array_subscript{'e1; 'e2}} <-->
          eval{'S; array_subscript{expr{'S; 'e1}; expr{'S; 'e2}}})

rewrite array_subscript_redex :
   eval{'S; array_subscript{address[$name:s]; int[$index:n]}} <-->
      value{'S; prim_array_subscript{lookup{'S; address[$name:s]}; int[$index:n]}}

rewrite array_subscript_array_raise :
   is_value{'S; 'e2} -->
      (eval{'S; array_subscript{"raise"{'e1}; 'e2}} <-->
          eval{'S; "raise"{'e1}})

rewrite array_subscript_subscript_raise :
   is_value{'S; 'e1} -->
      (eval{'S; array_subscript{'e1; "raise"{'e2}}} <-->
          eval{'S; "raise"{'e2}})

(*
 * Set an element.
 * Eight cases:
 *    *1. array val, subscript val, value val, in bounds
 *     2. array arb, subscript val, value val, in bounds
 *     3. array val, subscript arb, value val, in bounds
 *     4. array val, subscript val, value arb, in bounds
 *     + same four cases, but out-of-bounds
 *)
axiom array_set_equiv :
   sequent { 'H >- value_equiv{'S; 'e1; 'e4; type_array{'t}} } -->
   sequent { 'H >- value_equiv{'S; 'e2; 'e5; type_int} } -->
   sequent { 'H >- value_equiv{'S; 'e3; 'e6; 't} } -->
   sequent { 'H >- equiv{'S; array_set{'e1;'e2; 'e3}; array_set{'e4; 'e5; 'e6}; type_unit; 'exn} }

rewrite array_set_eval :
   two_values{is_value{'S; 'e1}; is_value{'S; 'e2}; is_value{'S; 'e3}} -->
      (eval{'S; array_set{'e1; 'e2; 'e3}} <-->
          eval{'S; array_set{expr{'S; 'e1}; expr{'S; 'e2}; expr{'S; 'e3}}})

rewrite array_set_redex :
   is_value{'S; 'e} -->
      (eval{'S; array_set{address[$name:s]; int[$index:n]; 'e}} <-->
          eval{'S; prim_array_set{address[$name:s]; int[$index:n]; expr_value{'S; 'e}}})

rewrite array_set_array_raise :
   (is_value{'S; 'e2} & is_value{'S; 'e3}) -->
      (eval{'S; array_set{"raise"{'exn}; 'e2; 'e3}} <-->
          eval{'S; "raise"{'exn}})

rewrite array_set_subscript_raise :
   (is_value{'S; 'e1} & is_value{'S; 'e3}) -->
      (eval{'S; array_set{'e1; "raise"{'exn}; 'e3}} <-->
          eval{'S; "raise"{'exn}})

rewrite array_set_value_raise :
   (is_value{'S; 'e1} & is_value{'S; 'e2}) -->
      (eval{'S; array_set{'e1; 'e2; "raise"{'exn}}} <-->
          eval{'S; "raise"{'exn}})

(************************************************************************
 * RECORDS                                                              *
 ************************************************************************)

(*
 * Record creation.
 * Force all the entries to be values.
 *)
axiom record_equiv :
   sequent { 'H >- value_equiv{'S; 'e1; 'e2; 't1} } -->
   sequent { 'H >- equiv{'S; record{'el1}; record{'el2}; type_record{'tl1}; 'exn} } -->
   sequent { 'H >- equiv{'S;
                         record{cons{cons{'n1; 'e1}; 'el1}};
                         record{cons{cons{'n1; 'e2}; 'el2}};
                         type_record{cons{'n1; 't1}; 'tl1};
                         'exn} }

rewrite record_eval :
   is_value{'S; 'el} -->
      (eval{'S; record{'el}} <-->
          allocate{'S; record{expr_value{'S; 'vl}}})

(*
 * Projection.
 * Two cases:
 *    *1. record val, label val
 *    *2. record arb, label val
 *)
axiom proj_value_equiv :
   sequent { 'H >- value_equiv{'S; 'e1; 'e2; type_record{cons{cons{lid[$n:s]; 't}; nil}}} } -->
   sequent { 'H >- value_equiv{'S; proj{'e1; lid[$n:s]}; proj{'e2; lid[$n:s]}; 't} }

axiom proj_equiv :
   sequent { 'H >- equiv{'S; 'e1; 'e2; type_record{cons{cons{lid[$n:s]; 't}; nil}}; 'exn} } -->
   sequent { 'H >- equiv{'S; proj{'e1; lid[$n:s]}; proj{'e2; lid[$n:s]}; 't; 'exn} }

rewrite proj_eval :
      (eval{'S; proj{'e1; lid[$label:s]}} <-->
          eval{'S; proj{expr{'S; 'e1}; lid[$label:s]}})

rewrite proj_redex :
   eval{'S; proj{address[$name:s]; lid[$label:s]}} <-->
      eval{'S; prim_proj{lookup{'S; address[$name:s]}; lid[$label:s]}}

(*
 * Set a record field.
 * Three cases:
 *    *1. record val, label val, value val
 *    *2. record arb, label val, value val
 *    *3. record val, label val, value arb
 *)
axiom record_set_value_equiv :
   sequent { 'H >- value_equiv{'S; 'e1; 'e3; type_record{cons{cons{lid[$n:s]; 't}; nil}}} } -->
   sequent { 'H >- value_equiv{'S; 'e2; 'e4; 't} } -->
   sequent { 'H >- value_equiv{'S;
                               record_set{'e1; lid[$n:s]; 'e2}; 
                               record_set{'e3; lid[$n:s]; 'e4};
                               type_unit} }

axiom record_set_record_equiv :
   sequent { 'H >- equiv{'S; 'e1; 'e3; type_record{cons{cons{lid[$n:s]; 't}; nil}}; 'exn} } -->
   sequent { 'H >- value_equiv{'S; 'e2; 'e4; 't} } -->
   sequent { 'H >- equiv{'S;
                         record_set{'e1; lid[$n:s]; 'e2}; 
                         record_set{'e3; lid[$n:s]; 'e4};
                         type_unit;
                         'exn} }

axiom record_set_arg_equiv :
   sequent { 'H >- value_equiv{'S; 'e1; 'e3; type_record{cons{cons{lid[$n:s]; 't}; nil}}} } -->
   sequent { 'H >- equiv{'S; 'e2; 'e4; 't; 'exn} } -->
   sequent { 'H >- equiv{'S;
                         record_set{'e1; lid[$n:s]; 'e2}; 
                         record_set{'e3; lid[$n:s]; 'e4};
                         type_unit;
                         'exn} }

rewrite record_set_eval :
   "or"{is_value{'e1}; is_value{'e3}} -->
      (eval{'S; record_set{'e1; lid[$label:s]; 'e3}} <-->
          eval{'S; record_set{expr{'S; 'e1}; lid[$label:s]; expr{'S; 'e3}}})

rewrite record_set_redex :
   is_value{'S; 'e} -->
      (eval{'S; record_set{address[$name:s]; lid[$label:s]; 'e}} <-->
          set{'S; address[$name:s];
              prim_record_set{lookup{'S; address[$name:s]};
                              lid[$label:s];
                              expr_value{'S; 'e}}})

(************************************************************************
 * FUNCTIONS                                                            *
 ************************************************************************)

(*
 * Intensional equivalence of functions.
 *)
axiom fun_equiv :
   sequent { 'H >- value_equiv{'S; "fun"{'pwel1}; "fun"{'pwel2}; type_fun{'t1; 't2}} }

(************************************************************************
 * LET                                                                  *
 ************************************************************************)

axiom let_equiv :
   sequent { 'H >- equiv{'S; 'el1; 'el2; 'tl} } -->
   sequent { 'H >- equiv{state{'S; 'el1}; 'p1; 'p2; type_fun{'tl; 't}} } -->
   sequent { 'H >- equiv{'S; "let"{'p1; 'e1}; "let"{'p2; 'e2}; 't} }

axiom let_value_equiv :
   sequent { 'H >- value_equiv{'S; 'el1; 'el2; 'tl} } -->
   sequent { 'H >- value_equiv{'S; 'p1; 'p2; type_fun{'tl; 't}} } -->
   sequent { 'H >- value_equiv{'S; "let"{'p1; 'e1}; "let"{'p2; 'e2}; 't} }

rewrite let_eval :
   eval{'S; "let"{'p; 'e} <-->
      eval{'S; "match"{'e; 'p}}

(************************************************************************
 * MATCH                                                                *
 ************************************************************************)
        
axiom match_equiv :
   sequent { 'H >- equiv{'S; 'e1; 'e2; 't2} } -->
   sequent { 'H >- equiv{'S; 'p1; 'p2; type_fun{'t2; 't1} } -->
   sequent { 'H >- equiv{'S; "match"{'e1; 'p1}; "match"{'e2; 'p2}; 't} }
             
axiom match_value_equiv :
   sequent { 'H >- value_equiv{'S; 'e1; 'e2; 't2} } -->
   sequent { 'H >- value_equiv{'S; 'p1; 'p2; functional{'t2; 't1} } -->
   sequent { 'H >- value_equiv{'S; "match"{'e1; 'p1}; "match"{'e2; 'p2}; 't} }
             
(************************************************************************
 * TRY                                                                  *
 ************************************************************************)
             
axiom try_equiv :
   sequent { 'H >- equiv{'S; 'e1; 'e2; 't} } -->
      sequent { 'H
(*
 * Application.
 *)
axiom apply_equiv :
   sequent { 'H >- equiv{'S; 'f1; 'f2; type_fun{'t1; 't2}} } -->
   sequent { 'H >- equiv{'S; 'a1; 'a2; 't1 } -->
   sequent { 'H >- equiv{'S; apply{'f1; 'a1}; apply{'f2; 'a2}; 't2}}
             
axiom apply_value_equiv :
   sequent { 'H >- value_equiv{'S; 'f1; 'f2; functional{'t1; 't2}} } -->
   sequent { 'H >- value_equiv{'S; 'a1; 'a2; 't1} } -->
   sequent { 'H >- value_equiv{'S; apply{'f1; 'a1}; apply{'f2; 'a2}; 't2} }

rewrite apply_eval :
   (eval{'S; apply{'e1; 'e2}} <--> 
       spread{eval{'S; 'e1}; f, S2.
          eval{'S2; apply{'f; 'e2}}})

rewrite apply_apply_eval :
   eval{'S; apply{fun{'pwel}; 'e2} <-->
      eval{'S; "match"{'e2; 'pwel}}

(*
 * $Log$
 * Revision 1.2  1998/02/13 22:10:25  jyh
 * Adding pattern semantics.
 *
 * Revision 1.1  1998/02/13 16:02:13  jyh
 * Partially implemented semantics for caml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
