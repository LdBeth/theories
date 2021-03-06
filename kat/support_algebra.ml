extends Base_theory

open Basic_tactics
open Tactic_type
(*
open Top_conversionals
open Dtactic *)
open Refiner.Refiner.RefineError

open Term_stable
open Tactic_type.Conversionals


(* Commutative Resource *)

let extract_data tbl =
   let rw t =
      try
         slookup tbl t
      with
         Not_found ->
            raise (RefineError ("Support_algebra.extract_data", StringTermError ("Commutative resource does not know about", t)))
   in
      termC rw

let resource (term * conv,  conv) commutative =
   stable_resource_info extract_data

let symC =
 funC (fun env ->
  Sequent.get_resource_arg (env_arg env) get_commutative_resource
      )

(* Associative Resource *)

let id tbl = tbl

let resource (term * (conv * conv), (conv * conv) term_stable) associative =
   stable_resource_info id

let revAssocC =
 funC (fun env ->
   let term = (env_term env) in
         try
            let table = Sequent.get_resource_arg (env_arg env) get_associative_resource in
            let (_,revAssocC) = slookup table term in  revAssocC
         with
            Not_found ->
               raise (RefineError ("revAssocC", StringTermError ("Associative resource does not know about", term)))
      )


let assocC =
 funC (fun env ->
   let term = (env_term env) in
         try
            let table = Sequent.get_resource_arg (env_arg env) get_associative_resource in
            let (assocC,_) = slookup table term in assocC
         with
            Not_found ->
               raise (RefineError ("assocC", StringTermError ("Associative resource does not know about", term)))
      )





let subAssoc first length conv env  = (* may raise Not_found *)
   let term = (env_term env) in
   let opname = opname_of_term term  in
   let table = Sequent.get_resource_arg (env_arg env) get_associative_resource in
   let (_,revAssocC) = slookup table term
   in
   let rec sub0C length = (* invariant: sub0C always applies to an opname term *)
     if length > 1 then
        revAssocC thenC sub0C (length-1)
        orelseC
           if length = 2 then conv
           else failWithC "subAssocC: Not enough subterms (the second argument is too big)"
     else if length = 1 then
        addrC [Subterm 1] conv
     else raise (Invalid_argument ("Trying to apply subAssocC with nonpositive length"))
  in
  let rec subNC first =  termC (fun term ->
     if opname_of_term term <> opname then
        if first=0 && length=1 then conv
        else raise (RefineError ("subAssocC", StringError ("Not enough subterms")))
     else
        if first>0 then
           addrC [Subterm 2] (subNC (first -1) )
        else if first = 0 then
           sub0C length
        else raise (Invalid_argument ("Trying to apply subAssocC with negative argument"))
                               )
  in
     subNC first

let subAssocC first length conv  =
   funC (fun env ->
      try
         subAssoc first length conv env
      with Not_found ->
               raise (RefineError ("subAssocC", StringError ("subAssocC is applied to a term that associative resource does not know about")))
        )

(*
let rec addrAssocC addr conv =
   funC (fun env ->
      match  addr with
            [] -> conv |
            [n] ->  addrC [n] conv |
            n::m::rest ->
               try  subAssoc n m (addrAssocC rest conv) env
               with Not_found ->  addrC [n] (addrAssocC (m::rest) conv)
        )
            _ ->  raise (Invalid_argument ("addrAssocC is applied to an associative term. Need at least two argements for adress")) *)
