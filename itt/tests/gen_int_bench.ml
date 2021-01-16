open Printf

(******************************************
 * Benchmark
 ******************************************)

let print_var co k v =
   if v = 0 then
      fprintf co "%i" k
   else
      fprintf co "%i *@ 'v%i" k v

let print_var_smt ct k v =
   if v = 0 then
      fprintf ct "%i" k
   else
      fprintf ct "(* %i v%i)" k v

type expr = Var of int * int | Add of expr * expr

let rec print_expr co = function
	 Var(k,v) -> print_var co k v
 | Add(e1,e2) -> fprintf co "(%a) +@ (%a)" print_expr e1 print_expr e2

let rec print_expr_smt ct = function
   Var(k,v) -> print_var_smt ct k v
 | Add(e1,e2) -> fprintf ct "(+ %a %a)" print_expr_smt e1 print_expr_smt e2

let rec gen_expr nvars intrange maxdepth =
	if maxdepth>0 && (Random.bool ()) then
		Add(gen_expr nvars intrange (maxdepth-1), gen_expr nvars intrange (maxdepth-1))
	else
		Var(Random.int intrange, Random.int (nvars+1))

let print_seq printer co arg =
	fprintf co "sequent { <H> >- %a }" printer arg

let print_assum printer co arg =
	fprintf co "%a -->\n" (print_seq printer) arg

let print_decl co v =
   fprintf co "v%i : int; " v

let print_decl_smt ct v =
   fprintf ct "(declare-const v%i Int)\n" v

let print_goal co printer =
	fprintf co "sequent { %t >- \"false\" } = \"testT\"\n" printer

let print_goal_smt ct printer =
   fprintf ct "(push) %t (check-sat) (pop)\n" printer

type ineq = Ge | Gt | Le | Lt | Eq | Ne

let gen_ineq () =
	match Random.int 6 with
		 0 -> Ge
	 | 1 -> Gt
	 | 2 -> Le
	 | 3 -> Lt
	 | 4 -> Eq
	 | _ -> Ne

let print_ineq (ineq, e1, e2) co =
	match ineq with
     Ge -> fprintf co "%a >= %a" print_expr e1 print_expr e2
	 | Gt -> fprintf co "%a > %a" print_expr e1 print_expr e2
	 | Le -> fprintf co "%a <= %a" print_expr e1 print_expr e2
	 | Lt -> fprintf co "%a < %a" print_expr e1 print_expr e2
	 | Eq -> fprintf co "%a = %a in int" print_expr e1 print_expr e2
	 | Ne -> fprintf co "%a <> %a" print_expr e1 print_expr e2

let print_ineq_smt (ineq, e1, e2) ct =
	match ineq with
     Ge -> fprintf ct "(assert (>= %a %a))" print_expr_smt e1 print_expr_smt e2
	 | Gt -> fprintf ct "(assert (> %a %a))" print_expr_smt e1 print_expr_smt e2
	 | Le -> fprintf ct "(assert (<= %a %a))" print_expr_smt e1 print_expr_smt e2
	 | Lt -> fprintf ct "(assert (< %a %a))" print_expr_smt e1 print_expr_smt e2
	 | Eq -> fprintf ct "(assert (= %a %a))" print_expr_smt e1 print_expr_smt e2
	 | Ne -> fprintf ct "(assert (not (= %a %a)))" print_expr_smt e1 print_expr_smt e2

let gen_rule nineq nvars intrange maxdepth =
   nvars, Array.init nineq (fun _ -> let e1 = gen_expr nvars intrange maxdepth in
                                     let e2 = gen_expr nvars intrange maxdepth in
                                     let ineq = gen_ineq () in
                                        ineq, e1, e2)
let print_all (nvars, eqs) co =
	for i=1 to nvars do
     print_decl co i
	done;
  let ub = Array.length eqs - 1 in
     Array.iteri (fun i a -> fprintf co "\n%t" (print_ineq a);
                             if i < ub then fprintf co ";") eqs

let print_all_smt (nvars, eqs) ct =
   for i=1 to nvars do
     print_decl_smt ct i
	done;
  Array.iter (fun a -> fprintf ct "\n%t" (print_ineq_smt a)) eqs

let print_rule co n tests =
	fprintf co "\nthm test%i :\n" n;
	print_goal co (print_all tests)

let print_rule_smt ct n tests =
   fprintf ct "\n(echo \"interactive test%i :\")\n" n;
   print_goal_smt ct (print_all_smt tests)

let gen_bench name ~smt ~seed ~nrules ~nineq ~nvars ~intrange ~maxdepth =
	Random.init seed;
	let rules = Array.init nrules (fun _ -> gen_rule nineq nvars intrange maxdepth) in
	let co = open_out (name ^ ".ml") in
	fprintf co "extends Itt_int_test\n\n";
	(* fprintf co "open Itt_int_test\n\n"; *)
  Array.iteri (print_rule co) rules;
	flush co;
  (* generate smtlib files that can be checked by smt solver *)
  if smt then
     let ct = open_out (name ^ ".smt") in
        Array.iteri (print_rule_smt ct) rules;
        flush ct

let _ = gen_bench "itt_int_bench"
	~smt:true ~seed:23 ~nrules:10 ~nineq:10 ~nvars:5 ~intrange:10 ~maxdepth:3

let _ = gen_bench "itt_int_bench2"
	~smt:true ~seed:0 ~nrules:10 ~nineq:15 ~nvars:5 ~intrange:10 ~maxdepth:2

let _ = gen_bench "itt_int_bench3"
	~smt:true ~seed:0 ~nrules:100 ~nineq:15 ~nvars:5 ~intrange:10 ~maxdepth:2
