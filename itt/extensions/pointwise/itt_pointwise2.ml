doc <:doc<
 @module[Itt_pointwise2]
>>

extends Itt_equal
extends Itt_quotient
extends Itt_struct
extends Itt_tunion
extends Itt_bunion
extends Itt_pointwise
doc docoff

open Dtactic

open Itt_struct

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
  The following rules are derived only in pointwise functionality.
   They both contradict to Let rule.
>>

interactive quotientElimination2 {| elim [ThinOption thinT] |} 'H :
   [wf] sequent { <H>; a: quot x, y: 'A // 'E['x; 'y]; <J['a]> >- "type"{'T['a]} } -->
   [main] sequent { <H>; a: quot x, y: 'A // 'E['x; 'y];
             v: 'A; w: 'A; z: 'E['v; 'w]; <J['v]> >- 's['v] = 't['w] in 'T['v]
           } -->
   sequent { <H>; a: quot x, y: 'A // 'E['x; 'y]; <J['a]> >- 's['a] = 't['a] in 'T['a] }

interactive tunionElimination2 {| elim [ThinOption thinT] |} 'H :
   sequent { <H>; z: tunion{'A; y. 'B['y]};  w: 'A; x: 'B['w]; <J['x]> >- squash{'C['x]}  } -->
   sequent { <H>; x: tunion{'A; y. 'B['y]}; <J['x]> >- squash{'C['x]} }

interactive bunionElimination2 {| elim [ThinOption thinT] |} 'H :
   [main] sequent { <H>; x: 'A; <J['x]> >- squash{'C['x]} } -->
   [main] sequent { <H>; x: 'B; <J['x]> >- squash{'C['x]} } -->
   sequent { <H>; x: 'A bunion 'B; <J['x]> >- squash{'C['x]} }

doc docoff
