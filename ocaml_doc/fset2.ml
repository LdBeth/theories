(*
 * Set implementation.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2000 Jason Hickey, Caltech
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)

module type EltSig =
sig
   type elt
   val compare : elt -> elt -> int
end

module type FsetSig =
sig
   type elt
   type t

   val empty : t
   val mem : elt -> t -> bool
   val insert : elt -> t -> t
end

module MakeFset (Elt : EltSig) =
struct
   type elt = Elt.elt

   type color =
      Red
    | Black

   type t =
      Node of color * t * elt * t
    | Leaf

   let empty = Leaf

   let rec mem x = function
      Leaf -> false
    | Node (_, a, y, b) ->
         let i = Elt.compare x y in
            if i < 0 then mem x a
            else if i > 0 then mem x b
            else true

   let balance = function
      Black, Node (Red, Node (Red, a, x, b), y, c), z, d ->
         Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))
    | Black, Node (Red, a, x, Node (Red, b, y, c)), z, d ->
         Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))
    | Black, a, x, Node (Red, Node (Red, b, y, c), z, d) ->
         Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))
    | Black, a, x, Node (Red, b, y, Node (Red, c, z, d)) ->
         Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))
    | a, b, c, d ->
         Node (a, b, c, d)

   let insert x s =
      let rec ins = function
         Leaf -> Node (Red, Leaf, x, Leaf)
       | Node (color, a, y, b) as s ->
            let i = Elt.compare x y in
               if i < 0 then balance (color, ins a, y, b)
               else if i > 0 then balance (color, a, y, ins b)
               else s
      in
         match ins s with  (* guaranteed to be non-empty *)
            Node (_, a, y, b) -> Node (Black, a, y, b)
          | Leaf -> raise (Invalid_argument "insert")
end

module Int =
struct
   type elt
   let compare = (-)
end

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
