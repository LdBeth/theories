doc <:doc<
   @module[Itt_omega]

	This module defines the @tactic[omegaT] tactic capable of proving
   systems of inequalities.

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2004-2006 MetaPRL Group, City University of New York
   and California Institute of Technology

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

   Author: Yegor Bryukhov @email{ynb@mail.ru}
   @end[license]
   @parents
>>
extends Itt_equal
extends Itt_dfun
extends Itt_logic
extends Itt_bool
extends Itt_int_ext
extends Itt_int_arith
(*extends Itt_rat
extends Itt_rat2
*)

doc docoff

open Lm_debug
open Lm_printf

open Lm_num

open Basic_tactics

open Itt_equal
open Itt_struct
open Itt_bool

open Itt_int_base
open Itt_int_ext
open Itt_int_arith

module Term = Refiner.Refiner.Term
module TermMan = Refiner.Refiner.TermMan

let debug_omega =
   create_debug (**)
      { debug_name = "omega";
        debug_description = "Itt_omega debug messages";
        debug_value = false
      }

let debug_arith_dtactic =
   create_debug (**)
      { debug_name = "arith_dtactic";
        debug_description = "Itt_int_arith.arithT: display operations of conversion to >=";
        debug_value = false
      }

(* unused
let debug_rewrite = load_debug "rewrite"
let debug_refine = load_debug "refine"
 *)

open Omega

module Var =
struct
   type t = term
   let equal = alpha_equal
   let hash = Term_hash_code.hash_term
end

module IntRing =
struct
   type ring = num

   let ringUnit = one_num
   let ringZero = zero_num

   let print out a =
      fprintf out "(%s)" (string_of_num a)

   let isNegative = is_neg

   let isPositive = is_pos

   let abs = abs_num
   let mul = mult_num
   let add = add_num
   let sub = sub_num
   let neg = neg_num

   let gt = gt_num
   let le = le_num

   (* Euclidean division and remainder. *)
   let rem = erem_num
   let div = ediv_num

   let compare = compare_num
   let equal = eq_num

   let gcd = gcd_num

   (* unused
	let rec list_gcd_aux c = function
		hd::tl ->
			list_gcd_aux (gcd c hd) tl
	 | [] -> c

	let list_gcd = function
		[i] -> abs_num i
	 | hd::tl -> list_gcd_aux hd tl
	 | [] -> raise (Invalid_argument "list_gcd was applied to empty list")
   *)

   let term_of a = mk_number_term a

   let add_term = mk_add_term
   let mul_term = mk_mul_term
   let neg_term = mk_minus_term
   let sub_term = mk_sub_term
   let ge_term = mk_ge_term
end

module R = IntRing
(*
module AF=MakeDebugAF(R)(MakeArrayAF(R))(MakeAF(R))
*)
module AF=MakeAF(Var)(R)
(*
module AF=MakeArrayAF(R)
*)
module VI=AF.VI
open IntRing

type omegaTree =
	 Solve of (AF.vars * ring * omegaTree * AF.af * ring * omegaTree * AF.af)
 | Mul of (omegaTree * ring)
 | MulAndWeaken of (omegaTree * ring * ring)
 | Hyp of (int * int * int)

module Constraints
	(Ring: RingSig)
	(AF: AF_Sig with type ring = Ring.ring) =
struct
	module HashedAF =
	struct
		type t = Ring.ring array

		let equal a1 a2 =
         Array.for_all2 Ring.equal a1 a2

      (*
       * Since Lm.num has adopted hash safe Zarith, this should work fine.
       *)
		let hash = Hashtbl.hash
	end

	module Hash = Hashtbl.Make(HashedAF)

	let create dim size = (dim, Hash.create size)

	let length (dim, table) = Hash.length table

	let get_key dim f =
		Array.init dim (fun i -> AF.coef f (succ i))

	let neg_key key =
		Array.map (fun k -> Ring.neg k) key

	let add_aux info key constr =
		let dim, table = info in
		let tree, f = constr in
		try
			let old_tree, old_f = Hash.find table key in
			let old_const = AF.coef old_f AF.constvar in
			if Ring.compare old_const (AF.coef f AF.constvar) > 0 then
				Hash.replace table key constr
		with
			Not_found ->
				Hash.add table key constr

	let add info constr =
		let dim, table = info in
		let tree, f = constr in
		let key = get_key dim f in
		add_aux info key constr

(* unused
	let get (dim,table) key =
		Hash.find table key
*)

	let iter f (dim,table) = Hash.iter f table

	let rec of_list_aux constrs = function
		hd::tl ->
			add constrs hd;
			of_list_aux constrs tl
	 | [] ->
			constrs

	let of_list dim l =
		let constrs = create dim (List.length l) in
		of_list_aux constrs l
(*
	let append constrs (d',table') =
		Hash.iter (fun k d -> add_aux constrs k d) table';
		constrs
*)

	let append_list constrs l =
		List.iter (fun (k,d) -> add_aux constrs k d) l

	let filter_aux predicate new_constrs k d =
		if predicate k d then add new_constrs d

	let filter predicate (dim,table) =
		let new_constrs = create dim (Hash.length table) in
		Hash.iter (filter_aux predicate new_constrs) table;
		new_constrs

	exception Found of HashedAF.t * (omegaTree * AF.af)

	let find_aux predicate k d =
		if predicate k d then
			raise (Found (k, d))

	let find predicate (dim,table) =
		try
			Hash.iter (find_aux predicate) table;
			raise Not_found
		with
			Found (k,d) -> (k,d)

	let fold f (dim,table) init_val =
		Hash.fold f table init_val

end

module C=Constraints(IntRing)(AF)

(*
let ge_normC = (addrC [Subterm 1] normalizeC) thenC (addrC [Subterm 2] normalizeC)

let relNorm_aux t =
	match explode_term t with
		<<'a = 'b in 'T>> ->
			(addrC [Subterm 2] normalizeC) thenC (addrC [Subterm 3] normalizeC)
	 | _ ->
			(addrC [Subterm 1] normalizeC) thenC (addrC [Subterm 2] normalizeC)

let relNormC = termC relNorm_aux
*)
let relNormC = allSubC normalizeC
let ge_normC = relNormC

let monom2af var2index t =
	match explode_term t with
		<<'t1 *@ 't2>> ->
         if is_number_term t1 then
            let i=VI.lookup var2index t2 in
				let n = VI.length var2index in
            let f=AF.mk_var n i in
					AF.scale (dest_number t1) f
         else
            let i=VI.lookup var2index t in
				let n = VI.length var2index in
					AF.mk_var n i
	 | <<number[i:n]>> ->
			let n = VI.length var2index in
         AF.mk_number n (dest_number t)
	 | _ ->
			let i=VI.lookup var2index t in
				let n = VI.length var2index in
				AF.mk_var n i

let rec linear2af var2index t =
	match explode_term t with
		<<'t1 +@ 't2>> ->
			let f1=linear2af var2index t1 in
			let f2=linear2af var2index t2 in
				AF.add f1 f2
	 | _ ->
			monom2af var2index t

let ge2af var2index (i,t) =
	let left,right=dest_ge t in
	let f1=linear2af var2index left in
	let f2=linear2af var2index right in
	let f=AF.sub f1 f2 in
	(i, f)

let apply_rewrite p conv t =
	let es={sequent_args= <<sequent_arg>>; sequent_hyps=SeqHyp.empty; sequent_concl=t} in
	let s=mk_sequent_term es in
	let s'=Top_conversionals.apply_rewrite p (addrC concl_addr conv) s in
	TermMan.concl s'

let is_neg_number f =
	AF.isNumber f && isNegative (AF.coef f AF.constvar)

(*********************************************************************
 * OMEGA
 *********************************************************************)

interactive_rw ge_mulMonoPosit_rw 'c :
   (0 < 'c) -->
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   ('a >= 'b) <--> (('c *@ 'a) >= ('c *@ 'b))

interactive_rw ge_mulMonoPosit2_rw 'c :
   (0 < 'c) -->
   ('a in int) -->
   ('c in int) -->
   ('a >= 0) <--> (('c *@ 'a) >= 0)

let scaleC n = ge_mulMonoPosit2_rw n

interactive ge_scaleAndWeaken 'c 'd :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   [wf] sequent { <H> >- 'd in int } -->
   [aux] sequent { <H> >- 'd >= 0 } -->
   [aux] sequent { <H> >- 'd < 'c } -->
	sequent { <H> >- (('c *@ 'a) +@ 'd) >= ('c *@ 'b) } -->
   sequent { <H> >- 'a >= 'b }

interactive ge_scaleAndWeaken2 number[k:n] number[c:n] :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [aux] sequent { <H> >- number[c:n] >= 0 } -->
   [aux] sequent { <H> >- number[c:n] < number[k:n] } -->
	sequent { <H> >- ((number[k:n] *@ 'a) +@ number[c:n]) >= (number[k:n] *@ 'b) } -->
   sequent { <H> >- 'a >= 'b }

interactive ge_scaleAndWeaken3 number[k:n] number[c:n] :
   [wf] sequent { <H> >- 'a in int } -->
   [aux] sequent { <H> >- number[c:n] >= 0 } -->
   [aux] sequent { <H> >- number[c:n] < number[k:n] } -->
	sequent { <H> >- ((number[k:n] *@ 'a) +@ number[c:n]) >= 0 } -->
   sequent { <H> >- 'a >= 0 }

let scaleAndWeakenT k c = ge_scaleAndWeaken3 k c

interactive var_elim 'v :
	[wf] sequent { <H> >- 'a in int } -->
	[wf] sequent { <H> >- 'b in int } -->
	[wf] sequent { <H> >- 'v in int } -->
	[aux] sequent { <H> >- 0 < number[i:n] } -->
	[aux] sequent { <H> >- 0 < number[j:n] } -->
	sequent { <H> >- number[i:n] *@ 'v -@ 'a >= 0 } -->
	sequent { <H> >- 'b -@ number[j:n] *@ 'v >= 0 } -->
	sequent { <H> >- number[i:n] *@ 'b >= number[j:n] *@ 'a }

interactive_rw factor_out 'cleft 'tleft 'cright 'tright :
	('cleft in int) -->
	('tleft in int) -->
	('cright in int) -->
	('tright in int) -->
	('right in int) -->
	('left = 'right +@ ('cleft *@ 'tleft) -@ ('cright *@ 'tright) in int) -->
	('left >= 'right) <-->
	('cleft *@ 'tleft >= 'cright *@ 'tright)

(*
interactive_rw factor_out2 number[l:n] 'tleft number[r:n] 'tright :
	('tleft in int) -->
	('tright in int) -->
	('left = (number[l:n] *@ 'tleft) -@ (number[r:n] *@ 'tright) in int) -->
	('left >= 0) <-->
	(number[l:n] *@ 'tleft >= number[r:n] *@ 'tright)
*)

interactive var_elim2 'v number[l:n] 'tleft number[r:n] 'tright :
	[wf] sequent { <H> >- 'tleft in int } -->
	[wf] sequent { <H> >- 'tright in int } -->
	[wf] sequent { <H> >- 'v in int } -->
	[aux] sequent { <H> >- 0 < number[l:n] } -->
	[aux] sequent { <H> >- 0 < number[r:n] } -->
	sequent { <H> >- number[l:n] *@ 'v -@ 'tright >= 0 } -->
	sequent { <H> >- 'tleft -@ number[r:n] *@ 'v >= 0 } -->
	[aux] sequent { <H> >- 'left = (number[l:n] *@ 'tleft) -@ (number[r:n] *@ 'tright) in int } -->
	sequent { <H> >- 'left >= 0 }

interactive var_elim3 'v :
	[wf] sequent { <H> >- 'tleft in int } -->
	[wf] sequent { <H> >- 'tright in int } -->
	[wf] sequent { <H> >- 'v in int } -->
	[aux] sequent { <H> >- 0 < number[l:n] } -->
	[aux] sequent { <H> >- 0 < number[r:n] } -->
	sequent { <H> >- number[l:n] *@ 'v -@ 'tright >= 0 } -->
	sequent { <H> >- 'tleft -@ number[r:n] *@ 'v >= 0 } -->
	sequent { <H> >- (number[l:n] *@ 'tleft) -@ (number[r:n] *@ 'tright) >= 0 }

let var_elimT v lnum lterm rnum rterm = funT (fun p ->
	let concl' = mk_ge_term (mk_sub_term (mk_mul_term lnum lterm) (mk_mul_term rnum rterm)) <<0>> in
	if alpha_equal concl' (concl p) then
		var_elim3 v
	else
		var_elim2 v lnum lterm rnum rterm
)

let rec rev_flatten = function
   h :: t ->
      List.rev_append h (rev_flatten t)
 | [] ->
      []

let all_pairs l1 l2 =
	let pairs_lists = List.rev_map (fun x -> List.rev_map (fun y -> (y,x)) l1) l2 in
	rev_flatten pairs_lists

let norm constr =
	let tree, f = constr in
	let gcd = AF.gcd f in
	if le gcd ringUnit then
		constr
	else
		let c = rem (AF.coef f AF.constvar) gcd in
		let f' = AF.div f gcd in
		if is_zero c then
			(Mul (tree, gcd), f')
		else
			(MulAndWeaken (tree, gcd, c), f')

let omega_aux v ((c1,t1,l),(c2,t2,u)) =
	let s = (Solve (v,c1,t1,l,c2,t2,u),	AF.sub_scaled (AF.scale c1 u) c2 l) in
	norm s

let compute_metric pool key (tree,f) =
	Array.iteri (fun v m -> pool.(v) <- add m (abs (AF.coef f (succ v)))) pool

let rec min_index_aux pool result current =
	if current = Array.length pool then
		result
	else
		let current_val = pool.(current) in
		if (gt pool.(result) current_val) && (isPositive current_val) then
			min_index_aux pool current (succ current)
		else
			min_index_aux pool result (succ current)

let rec min_index pool current =
	if current = Array.length pool then
		raise (RefineError ("omegaT", StringError "failed to find a contradiction - no variables left"))
	else
		if gt pool.(current) ringZero then
			min_index_aux pool current (succ current)
		else
			min_index pool (succ current)

let pick_var pool constrs =
	Array.fill pool 0 (Array.length pool) ringZero;
	C.iter (compute_metric pool) constrs;
	let result = min_index pool 0 in
	if gt pool.(result) ringZero then
		succ result
	else
		raise (RefineError ("omegaT", StringError "failed to find a contradiction - no variables left"))

(*
let pick_var_aux key (tree,f) =
	let v = AF.any_var f in
	v<>AF.constvar

let pick_var pool constrs =
	try
		let k, (tree, f) = C.find pick_var_aux constrs in
		(*let tree, f = C.get constrs k in*)
		AF.any_var f
	with
		Not_found ->
			raise (RefineError ("omegaT", StringError "failed to find a contradiction - no variables left"))
*)

let get_bounds_aux v key constr (l,u,rest) =
	let tree, f = constr in
	let c = AF.coef f v in
	if isPositive c then
		let f' = AF.remove f v in
		(((c, tree, (AF.scale (neg ringUnit) f'))::l), u, rest)
	else
		if isNegative c then
			let f' = AF.remove f v in
			(l, ((neg c, tree, f')::u), rest)
		else
			(l, u, ((key, constr)::rest))

let get_bounds v constrs = C.fold (get_bounds_aux v) constrs ([],[],[])

(*
let print_constrs constrs =
	C.iter (fun k (tree,f) -> eprintf "%a@." AF.print f) constrs
*)

let print_constrs constrs =
	eprintf "%i constraints@." (C.length constrs)

let var_bounds (old_upper, old_lower) f v =
	let c = AF.coef f (succ v) in
	if is_neg c then
		(true, old_lower)
	else
		if is_pos c then
			(old_upper, true)
		else
			(old_upper, old_lower)

let xor a b =
	if a then
		not b
	else
		b

let rec collect_unbound_vars pool acc i =
	if i=(Array.length pool) then
		acc
	else
		let upper,lower = pool.(i) in
		let i' = succ i in
		if xor upper lower then
			collect_unbound_vars pool (i'::acc) i'
		else
			collect_unbound_vars pool acc i'

let rec no_unbound_vars f = function
	hd::tl ->
		let c = AF.coef f hd in
		if not (is_zero c) then
			begin
				if !debug_omega then
					eprintf "Unbound v%i in %a@." hd AF.print f;
				false
			end
		else
			no_unbound_vars f tl
 | [] ->	true

let remove_unbound_vars_aux pool constrs =
	Array.fill pool 0 (Array.length pool) (false,false);
	C.iter (fun key (tree,f) -> Array.iteri (fun v bounds -> pool.(v) <- var_bounds bounds f v) pool) constrs;
	let unbound_vars = collect_unbound_vars pool [] 0 in
	C.filter (fun k (tree,f) -> no_unbound_vars f unbound_vars) constrs

let remove_unbound_vars pool constrs =
	let new_constrs = remove_unbound_vars_aux pool constrs in
	(*
	if C.length new_constrs < C.length constrs then
		remove_unbound_vars pool new_constrs
	else
	*)
		new_constrs

exception OppositePair of (omegaTree * AF.af) * (omegaTree * AF.af)

let find_opposite constrs key c =
	let neg_key = C.neg_key key in
	try
		let _, opposite = C.find (fun k _ -> (C.HashedAF.equal k neg_key)) constrs in
		let tree1, f1 = c in
		let tree2, f2 = opposite in
		let constant = add (AF.coef f1 AF.constvar) (AF.coef f2 AF.constvar) in
		if isNegative constant then
			raise (OppositePair (c, opposite))
	with Not_found ->
		()

let rec omega pool pool2 constrs =
	if !debug_omega then
		print_constrs constrs;
	let constrs =
		try
			C.iter (find_opposite constrs) constrs;
			remove_unbound_vars pool constrs
		with OppositePair (a, b) ->
			if !debug_omega then
				eprintf "found opposite pair %a %a@." AF.print (snd a) AF.print (snd b);
			C.of_list (Array.length pool) [a;b]
	in
	let v = pick_var pool2 constrs in
	if !debug_omega then
		eprintf "picked %a@." AF.print_var v;
	let l, u, rest = get_bounds v constrs in
	let pairs = all_pairs l u in
   if !debug_omega then
      eprintf "generated %i pairs@." (List.length pairs);
   let new_constrs = List.rev_map (omega_aux v) pairs in
   if !debug_omega then
      eprintf "new constraints generated@.";
   match List.find_opt (fun (tree, f) -> is_neg_number f) new_constrs with
      Some e -> e
    | None ->
         if !debug_omega then
			   eprintf "no contradiction found, building new table@.";
         let new_constrs = C.of_list (Array.length pool) new_constrs in
            C.append_list new_constrs rest;
            if !debug_omega then
               eprintf "calling omega@.";
            omega pool pool2 new_constrs

interactive_rw zero_ge_to_left_rw :
   'a in int -->
   0 >= 'a <--> (-1) *@ 'a >= 0

let zero_term = <<0>>

let ge_to_ge0C t =
	if is_ge_term t then
      let a, b = dest_ge t in
         if alpha_equal b zero_term then
            idC
         else if alpha_equal a zero_term then
            zero_ge_to_left_rw
         else
		      ge_to_leftC
	else
		idC

let normalize2C =	(termC ge_to_ge0C) thenC relNormC

(*
let totaltime = ref 0.
let starttime = ref 0.

let startT = argfunT (fun i p ->
	starttime := Unix.time ();
	if !debug_omega then
		begin
			eprintf "start %i@." i;
			let i' = mk_number_term (Lm_num.num_of_int i) in
			let t = mk_equal_term <<int>> i' i' in
			assertT t
		end
	else
		idT
)

let endT = argfunT (fun i p ->
	totaltime := Unix.time() -. !starttime;
	eprintf "endT: total time spent is %f@." !totaltime;
	if !debug_omega then
		begin
			eprintf "end %i@." i;
			let i' = mk_number_term (Lm_num.num_of_int i) in
			let t = mk_equal_term <<int>> i' i' in
			assertT t
		end
	else
		idT
)
*)

let rec tree_stats h m mw s = function
	Hyp _ -> ((succ h), m, mw, s)
 | Mul (tree, gcd) -> tree_stats h (succ m) mw s tree
 | MulAndWeaken (tree, gcd, c) -> tree_stats h m (succ mw) s tree
 | Solve (v,c1,t1,l,c2,t2,u) ->
		let h1,m1,mw1,s1 = tree_stats h m mw (succ s) t1 in
		tree_stats h1 m1 mw1 s1 t2

let rec source2hyp info hyp_pos src = funT (fun p ->
match src with
 | Hyp (i, pos, len) ->
		if !debug_omega then
			eprintf "Hyp %i %i %i hyp_pos.(i)=%i@." i pos len hyp_pos.(i);
		let hyp_addr =
			if len = 0 then
				i
			else
				hyp_pos.(i) + pos
		in
      let conc = concl p in
		if alpha_equal (nth_hyp p hyp_addr) conc then
			hypothesis hyp_addr
		else if is_ge_term conc then
			(rw normalize2C hyp_addr thenMT rw relNormC 0 thenMT hypothesis hyp_addr)
      else
         (rw (normalize2C thenC simpleReduceC) hyp_addr thenMT assert_false hyp_addr)
 | Mul (tree, gcd) ->
		rw (scaleC (mk_number_term gcd)) 0 thenMT
		source2hyp info hyp_pos tree
 | MulAndWeaken (tree, gcd, c) ->
		scaleAndWeakenT (mk_number_term gcd) (mk_number_term c) thenMT
		source2hyp info hyp_pos tree
 | Solve (v,c1,t1,l,c2,t2,u) ->
		let cleft = term_of c1 in
		let tleft = AF.term_of info u in
		let cright = term_of c2 in
		let tright = AF.term_of info l in
		tryT (var_elimT (VI.restore info v) cleft tleft cright tright thenMLT
			[source2hyp info hyp_pos t1; source2hyp info hyp_pos t2])
)

let omegaAuxT info hyp_pos tree =
	source2hyp info hyp_pos tree thenMT rw ge_normC (-1)

let rec eval_hyp_pos_aux hyp_length hyp_pos count = function
	hyp::tail ->
		let count' = count + hyp_length.(hyp) in
		hyp_pos.(hyp) <- count';
		if !debug_omega then
			eprintf "hyp_pos.(%i)=%i@." hyp count';
		eval_hyp_pos_aux hyp_length hyp_pos count' tail
 | [] -> ()

let eval_hyp_pos n hyp_length used_hyps =
   let hyp_pos = Array.make (Array.length hyp_length) 0 in
   eval_hyp_pos_aux hyp_length hyp_pos n used_hyps;
   hyp_pos

let omegaCoreT info hyp_num hyp_length used_hyps tree f = funT (fun p ->
	let hyp_pos = eval_hyp_pos hyp_num hyp_length used_hyps in
   let () =
   	if !debug_omega then
	      let h,m,mw,s = tree_stats 0 0 0 0 tree in
		      eprintf "Solved (%i hyps, %i muls, %i mul&weaken, %i eliminations), reconstructing the proof@." h m mw s
   in
	match tree with
	 | Hyp i ->
			omegaAuxT info hyp_pos tree
	 | Mul _ | MulAndWeaken _ ->
			let tm = AF.term_of info f in
			assertT (mk_ge_term tm (term_of zero_num))
			thenLT [omegaAuxT info hyp_pos tree; rw ge_normC (-1)]
	 | Solve (v,c1,t1,l,c2,t2,u) ->
			let c1t = term_of c1 in
			let c2t = term_of c2 in
			assertT
				(mk_ge_term
					(mk_sub_term (mk_mul_term c1t (AF.term_of info u)) (mk_mul_term c2t (AF.term_of info l)))
					(mk_number_term zero_num))
			thenLT [omegaAuxT info hyp_pos tree; rw ge_normC (-1)]
)

type ('a, 'b) flexTree = Leaf of 'a | Node of ('b * (('a, 'b) flexTree)) list

let rec append i tac len pos l = function
	t::tail ->
		append i tac len (succ pos) ((i,t,pos,len,tac)::l) tail
 | [] -> l

let make_option tree i tac t =
	let terms = dest_xlist t in
	let len=List.length terms in
	let pos= -len in
	let option = append i tac len pos [] terms in
	(option, tree)

let options tree i tac t =
	Node (List.map (make_option tree i tac) t)

let rec hyp2ge p tree = function
	(i,t)::tail ->
		if !debug_arith_dtactic then
			eprintf "Itt_omega.hyp2ge: looking for %ith hyp %s%t" i (SimplePrint.short_string_of_term t) eflush;
		if is_ge_term t then
			let tree' = Node [([(i,t,i,0,idT)], tree)] in
			hyp2ge p tree' tail
		else begin
         if !debug_arith_dtactic then
            eprintf "Itt_omega.hyp2ge: searching ge_elim resource%t" eflush;
         match Sequent.get_resource_arg p get_ge_elim_resource (Sequent.get_pos_hyp_num p i) p with
            Some (terms, tac) ->
               let tree' = options tree i (tac i) terms in
                  hyp2ge p tree' tail
          | None ->
               if !debug_arith_dtactic then
                  eprintf "Itt_omega.hyp2ge: looking for %ith hyp %s - not found%t" i (SimplePrint.short_string_of_term t) eflush;
               hyp2ge p tree tail
      end
 | [] -> tree

let rec push2leaves f acc tree =
	let aux (data, subtree) =
		let data', acc' = f data acc in
		data', push2leaves f acc' subtree
	in
	match tree with
		Node edges ->
			Node (List.map aux edges)
	 | Leaf _ ->
			Leaf acc

let rec map_leaves f = function
	Node edges ->
		Node (List.map (fun (data,tree) -> data, map_leaves f tree) edges)
 | Leaf data ->
		Leaf (f data)

let rec smart_map_leaves f used_hyps = function
 | Node [] ->
		raise (Invalid_argument "smart_map_leaves: empty set of edges")
 |	Node ((data,_)::_ as edges) ->
		begin
			let i,_,_,_,_ = List.hd data in
			let backup = used_hyps.(i) in
			used_hyps.(i) <- false;
			let r = map_edges f used_hyps [] edges in
			if backup then
				used_hyps.(i) <- backup;
			r
		end
 | Leaf data ->
		Leaf (f data)
and
   map_edges f used_hyps mapped = function
	first::rest ->
		let data, subtree = first in
		let i,_,_,_,_ = List.hd data in
		let subtree' = smart_map_leaves f used_hyps subtree in
		if used_hyps.(i) then
			map_edges f used_hyps ((data, subtree')::mapped) rest
		else
			subtree'
 | [] ->
		Node (List.rev mapped)

(* unused
let rec leaves2list = function
	Node edges ->
		let lists = List.map (fun (data,tree) -> leaves2list tree) edges in
		List.flatten lists
 | Leaf data ->
		[data]
*)

let allhyps2ge p tree =
	hyp2ge p tree (all_hypsi p)

let all2ge p =
	let tree = allhyps2ge p (Leaf ()) in
	let tree' = push2leaves (fun data acc -> data, List.append data acc) [] tree in
	tree'

let rec count_used_hyps used_hyps hyp_length = function
	Hyp (i,pos,len) ->
		used_hyps.(i) <- true;
		hyp_length.(i) <- len;
 | Mul (tree, gcd) ->
		count_used_hyps used_hyps hyp_length tree
 | MulAndWeaken (tree, gcd, c) ->
		count_used_hyps used_hyps hyp_length tree
 | Solve (v,c1,t1,l,c2,t2,u) ->
		count_used_hyps used_hyps hyp_length t1;
		count_used_hyps used_hyps hyp_length t2

let omegaSim dim pool pool2 used_hyps hyp_length constrs =
	match constrs with
		[] ->
			raise (RefineError ("omegaT", StringError "no constraints noticed"))
	 | [coord,f] ->
			if is_neg_number f then
				begin
					let i, pos, len = coord in
					used_hyps.(i) <- true;
					hyp_length.(i) <- len;
					(Hyp coord, f)
				end
			else
				raise (RefineError ("omegaT", StringError "the only constraint noticed has no contradiction"))
	 | _::_::_ ->
			begin
				let n = succ dim in
				let constrs = List.rev_map (fun (coord,f) -> norm (Hyp coord, AF.grow n f)) constrs in
				let constrs = C.of_list dim constrs in
				let tree, f = omega pool pool2 constrs in
				count_used_hyps used_hyps hyp_length tree;
				(tree, f)
			end

let rec foldi_aux f ar acc current =
	if current = Array.length ar then
		acc
	else
		foldi_aux f ar (f current ar.(current) acc) (succ current)

let foldi f ar acc = foldi_aux f ar acc 0

let rec sim_make_sacs_aux p var2index l = function
	[] -> l
 | (i,t,pos,len,tac)::tl ->
		(match explode_term t with
		 | <<ge{'left; 'right}>> when not (alpha_equal left right) ->
				let t'=apply_rewrite p ge_normC t in
				sim_make_sacs_aux p var2index ((ge2af var2index ((i,pos,len),t'))::l) tl
		 | _ ->
				sim_make_sacs_aux p var2index l tl
		)

let sim_make_sacs p var2index constrs =
   let afs = sim_make_sacs_aux p var2index [] (*REV*)(*List.rev*) (constrs)(*REV*) in
      match List.find_opt (fun (i,f) -> is_neg_number f) afs with
        Some item -> [item]
      | None -> afs

let ge_elimT = argfunT (fun i p ->
   match Sequent.get_resource_arg p get_ge_elim_resource (Sequent.get_pos_hyp_num p i) p with
      Some (_, tac) -> tac i
    | None -> idT
)

(* unused
let rec prune_tree used_hyps = function
	Node edges ->
		let terms, subtree = List.hd edges in
		let i, term, pos, len, tac = List.hd terms in
		if used_hyps.(i) then
			let edges' = List.map (fun (data,subtree) -> (data, prune_tree used_hyps subtree)) edges in
			Node edges'
		else
			prune_tree used_hyps subtree
 | Leaf data -> Leaf data
*)

let isEmptyOrMainLabel l =
   (l="") || (List.mem l main_labels)

let count_main_goals goall =
	let aux count g =
		if isEmptyOrMainLabel (Sequent.label g) then
       succ count
    else count
	in
     List.fold_left aux 0 goall

let prefix_thenMLT =
   let rec combine tacl goall =
     match tacl, goall with
        [], [] -> []
      | t::ts, g :: gs when isEmptyOrMainLabel (Sequent.label g) ->
          t :: (combine ts gs)
      | _, g :: gs  ->
          idT :: (combine tacl gs)
      | _ ->
			raise (RefineError ("thenMLT", StringError "mismatch between number of main goals and number of"))
	in
	let combine1 tacl goall =
		if !debug_omega then
			eprintf "thenMLT: %itacs, %i goals, %i main@." (List.length tacl) (List.length goall) (count_main_goals goall);
		combine tacl goall
   in
     fun (tac:tactic) (tacl:tactic list) -> tac thenFLT (combine1 tacl)

let rec applyTreeT prefixT mainT used_hyps = function
	Node (first::rest) ->
		let data, subtree = first in
		let i,_,_,_,_ = List.hd data in
		let used_hyps' = i::used_hyps in
		prefix_thenMLT
			(prefixT i)
			((applyTreeT prefixT mainT used_hyps' subtree)::(List.map (fun (data,tree) -> applyTreeT prefixT mainT used_hyps' tree) rest))
 | Leaf data ->
		mainT (List.rev used_hyps) data
 | Node [] ->
		raise (Invalid_argument "applyTreeT: empty set of edges")

(* let total = ref 0. *)

let omegaPrepT = funT (fun p ->
   if !debug_omega then
      eprintf "omegaPrepT started@.";
   (* let start = Unix.time () in *)
   let options = all2ge p in
   let var2index = VI.create 13 in
   let option_constrs = map_leaves (sim_make_sacs p var2index) options in
   let hyp_num = succ (Sequent.hyp_count p) in
   let used_hyps = Array.make hyp_num false in
   let hyp_length = Array.make hyp_num 0 in
   let n0 = VI.length var2index in
   let pool = Array.make n0 (false,false) in
   let pool2 = Array.make n0 ringZero in
   let pruned_solutions = smart_map_leaves (omegaSim n0 pool pool2 used_hyps hyp_length) used_hyps option_constrs in
   let used_hyps = foldi (fun i v acc -> if v then i::acc else acc) used_hyps [] in
   if !debug_omega then
      begin
         eprintf "used hyps ";
         List.iter (eprintf "%i ") used_hyps;
         eprintf "@.";
      end;
   let info = VI.invert var2index in
   (* total := !total +. (Unix.time() -. start);
   if !debug_omega then
      eprintf "Total time spent in omegaPrepT is %f@." !total; *)
   let aux used_hyps (tree, f) =
      omegaCoreT info hyp_num hyp_length used_hyps tree f
   in
   onMHypsT used_hyps (rw relNormC) thenMT
   applyTreeT ge_elimT aux [] pruned_solutions
)

let normConclT = funT (fun p ->
   let conc = concl p in
      if is_equal_term conc then
         let _, a, b = dest_equal conc in
            if alpha_equal a b then rw simpleReduceC 0 else rw relNormC 0
      else
         rw simpleReduceC 0)

let omegaT =
   (*startT 2 thenMT*) (arithRelInConcl2HypT thenMT
   omegaPrepT) thenMT (rw simpleReduceC (-1) thenMT tryT (assert_false (-1))) thenT normConclT
   (*thenMT endT 2*)

let omega_intro = wrap_intro ~auto:AutoComplete ~name:"omegaT" omegaT

let resource intro += [
   << 'a < 'b >>, omega_intro;
   << 'a >= 'b >>, omega_intro;
]

(*
let getTimeT = funT (fun p ->
   eprintf "spent %f seconds in omegaPrepT@." !total;
   total := 0.;
   failT
) *)

(****************************
 * Currently I skip alternative branches only if first branch actually ignored current node constraint;
 * it actually should be done with all branches - if any branch ignored the current state constraint then we don't
 * need current node at all.
 ***************************

interactive dark_shadow_or_splinters 'c 'L 'd 'U :
   [wf] sequent { <H> >- 'c in int } -->
   [wf] sequent { <H> >- 'L in int } -->
   [wf] sequent { <H> >- 'd in int } -->
   [wf] sequent { <H> >- 'U in int } -->
   [splinters] sequent { <H>; 'c *@ 'd -@ 'c -@ 'd >= ('c *@ 'U) -@ ('d *@ 'L) >- 'C } -->
   [dark_shadow] sequent { <H>; ('c *@ 'U) -@ ('d *@ 'L) -@ ('c -@ 1) *@ ('d -@ 1) >= 0 >- 'C } -->
   sequent { <H> >- 'C }

interactive splinter_intro 'U :
   [wf] sequent { <H> >- 'c in int } -->
   [wf] sequent { <H> >- 'L in int } -->
   [wf] sequent { <H> >- 'v in int } -->
   [wf] sequent { <H> >- 'd in int } -->
   [wf] sequent { <H> >- 'U in int } -->
   sequent { <H> >- 'c *@ 'd -@ 'c -@ 'd >= ('c *@ 'U) -@ ('d *@ 'L) } -->
   sequent { <H> >- 'U >= 'd *@ 'v } -->
   sequent { <H> >- 'c *@ 'v >= 'L } -->
   sequent { <H> >- exst k: int_seg{0; ('c *@ 'd -@ 'c -@ 'd)/@ 'd}. ('c *@ 'v = 'L +@ 'k in int) }

interactive splinter_elim 'v :
   [wf] sequent { <H> >- 'c in int } -->
   [wf] sequent { <H> >- 'L in int } -->
   [wf] sequent { <H> >- 'v in int } -->
   [wf] sequent { <H> >- 'd in int } -->
   [wf] sequent { <H> >- 'U in int } -->
   sequent { <H> >- 'U >= 'd *@ 'v } -->
   sequent { <H> >- 'c *@ 'v >= 'L } -->
   sequent { <H>;
      'c *@ 'd -@ 'c -@ 'd >= ('c *@ 'U) -@ ('d *@ 'L);
      exst k: int_seg{0; ('c *@ 'd -@ 'c -@ 'd)/@ 'd}. ('c *@ 'v = 'L +@ 'k in int) >- 'C
   } -->
   sequent { <H>; 'c *@ 'd -@ 'c -@ 'd >= ('c *@ 'U) -@ ('d *@ 'L) >- 'C }

interactive exst_elim_cases :
   [wf] sequent { <H> >- 'n in int } -->
   sequent { <H> >- 'n > 0 } -->
   sequent { <H>; 'P['n -@ 1] >- 'C } -->
   sequent { <H>; exst k: int_seg{0; 'n -@ 1}. 'P['k] >- 'C } -->
   sequent { <H>; exst k: int_seg{0; 'n}. 'P['k] >- 'C }

interactive splinters_test :
   sequent {
      x: int;
      y: int;
      11 *@ 'x +@ 13 *@ 'y >= 27;
      45 >= 11 *@ 'x +@ 13 *@ 'y;
      7 *@ 'x -@ 9 *@ 'y >= -10;
      4 >= 7 *@ 'x -@ 9 *@ 'y
      >- 'C
   }
*)
