type t
type w
type r
type u

val (+): t -> t -> t
val f: int -> r
val g: w -> t
val h: r -> int -> u

type odd
type even

val a: odd -> even
val b: even -> odd

module type s = sig
  type ok
  module M: sig type bad end
end

module type c = sig type t end

module M: c
