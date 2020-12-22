open Basic_tactics
open Term_stable

resource (term * conv,  conv) commutative

resource (term * (conv * conv), (conv * conv) term_stable) associative

topval symC : conv

topval assocC : conv
topval revAssocC : conv

topval subAssocC : int -> int -> conv -> conv
(* topval addrAssocC : int list -> conv -> conv *)
