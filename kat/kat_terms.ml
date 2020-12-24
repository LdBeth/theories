doc <:doc<
   @spelling{Kleene}

   @module[Kat_terms]

   The @emph{Kleene Algebra with tests} is a two-sorted algebra

   $$
     (K, B, +, @cdot, *, 0, 1, @neg)
   $$

   where $B @subseteq K$ and

   $$
     (K, +, @cdot, *, 0, 1)
   $$

   is a Kleene algebra and

   $$
     (B, +, @cdot, @neg, 0, 1)
   $$

   is a Boolean algebra.

>>

doc <:doc<
   @parents
>>
extends Base_theory
extends Support_algebra
extends Itt_squiggle
doc docoff

open Dtactic
open Top_conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @terms
>>
declare number[n:n] (* 1 and 0 *)
declare prod{'x;'y} (*   'x * 'y  *)
declare union{'x;'y} (*   'x + 'y  *)
declare minus{'x}    (*   ~'x  *)
declare star{'x}    (*   'x^*  *)
declare bool
declare kleene

(* Less and greater *)

define le : le{'x;'y} <--> ('x + 'y) ~ 'y
define ge : ge{'x;'y} <--> le{'y;'x}
doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_star
prec prec_mul
prec prec_mul < prec_star
prec prec_neg
prec prec_neg < prec_mul
prec prec_add
prec prec_add < prec_neg

dform one_zero_df : number[n:n] =
   slot[n:n]

dform prod_df : parens :: "prec"[prec_mul] :: ('x * 'y) =
   slot["le"]{'x}  cdot slot["lt"]{'y}

dform plus_df : parens :: "prec"[prec_add] :: ('x + 'y) =
   slot["le"]{'x} `" + " slot["lt"]{'y}

dform negation_df : parens :: "prec"[prec_neg] :: (- 'a) =
   tneg slot["le"]{'a}

dform star_df : parens :: "prec"[prec_star] :: star{'a} =
   slot["le"]{'a} sup{slot["*"]}

dform bool_df : bool = mathbbB

dform kleene_df : kleene = mathbbK

dform le_df : ('x <= 'y) = 'x " " le " " 'y

dform ge_df : ('x >= 'y) = 'x " " ge " " 'y


(************************************************************************
 * WELL FORMEDNESS                                                      *
 ************************************************************************)

doc <:doc<
   @rules
>>
prim times_wf {| intro[] |}:
   sequent { <H> >- 'x in kleene} -->
   sequent { <H> >- 'y in kleene} -->
   sequent { <H> >- 'x * 'y in kleene} = it

prim plus_wf {| intro[] |}:
   sequent { <H> >- 'x in kleene} -->
   sequent { <H> >- 'y in kleene} -->
   sequent { <H> >- 'x + 'y in kleene} = it

prim star_wf {| intro[] |}:
   sequent { <H> >- 'x in kleene} -->
   sequent { <H> >- star{'x} in kleene} = it

prim neg_wf {| intro[] |}:
   sequent { <H> >- 'b in bool} -->
   sequent { <H> >- - 'b in bool} = it

prim and_wf {| intro[] |}:
   sequent { <H> >- 'b in bool} -->
   sequent { <H> >- 'c in bool} -->
   sequent { <H> >- 'b * 'c in bool} = it

prim or_wf {| intro[] |}:
   sequent { <H> >- 'b in bool} -->
   sequent { <H> >- 'c in bool} -->
   sequent { <H> >- 'b + 'c in bool} = it

prim false_wf {| intro[] |}:
   sequent { <H> >- 0 in bool} = it

prim true_wf {| intro[] |}:
   sequent { <H> >- 1 in bool} = it

prim bool_subtype_of_kleene {| intro[AutoMustComplete] |}:
   sequent { <H> >- 'b in bool} -->
   sequent { <H> >- 'b in kleene} = it

interactive zero_wf {| intro[] |}:
   sequent { <H> >- 0 in kleene}

interactive one_wf {| intro[] |}:
   sequent { <H> >- 1 in kleene}

(*****************************************************
* Associativitiy
******************************************************)
prim_rw prod_assotiative {|reduce |}: (('x * 'y) * 'z) <--> ('x * ('y * 'z))

interactive_rw rev_prod_assotiative: ('x * ('y * 'z)) <--> (('x * 'y) * 'z)

prim_rw plus_assotiative {|reduce |}: (('x + 'y) + 'z) <--> ('x + ('y + 'z))

interactive_rw rev_plus_assotiative: ('x + ('y + 'z)) <--> (('x + 'y) + 'z)

doc docoff

let resource associative +=
   [ <<'a * 'b>>, (prod_assotiative, rev_prod_assotiative);
     <<'a + 'b>>, (plus_assotiative, rev_plus_assotiative)]
