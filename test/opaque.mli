module Basic: sig

  type t
  type w
  type r
  type u

  val (+): t -> t -> t
  val f: int -> r
  val g: w -> t
  val h: r -> int -> u
end

module TwoCycle: sig
  type odd
  type even
  val a: odd -> even
  val b: even -> odd
end

module Module_types: sig
  module type s = sig
    type ok
    module M: sig type bad end
  end

  module type c = sig type t end

  module M: c

  module type r = sig type invi end
  module F: r with type invi := int
end

module Composite_1: sig
  type t1 and t2

  val f: unit -> t1 * t2

  type 'a producer = unit -> 'a
  type produced

  val x: produced producer
end

module Polyvariants: sig
  type after_or

  val f: [ `X of int | `Y of after_or ]
    -> [`W of float | `Z of after_or * char] -> after_or

  type lock1 and lock2
  val f: [ `X of lock1 | `Y of lock2 ] -> lock1 * lock2
end

module Objects: sig
  type field
  type field2

val x: int -> <x:field>
val w: <x:field2> -> field2
end

module Inner: sig
  type inner and inner_ok
  val fi: ( (unit -> inner) -> inner) -> inner
  val fi2: ( (unit -> inner_ok) -> unit) -> inner_ok
end

module Typedecl: sig
  type either_ok and either

  val either: (either_ok, bool) result -> either_ok
  val either' : (either, either) result -> either

  type ('a,'b) re = { x: 'a; y: 'b }
  type prod
  val prod: (prod, int) re -> prod
end

module Rectypes: sig
  type recursive
  val f: (recursive, recursive) result -> recursive

  type recursive_ok
  val f: (recursive_ok, recursive_ok list) result -> recursive_ok

  type 'a unregular = Leaf of 'a | Node of ('a * 'a) unregular
  type unreg
  val f: unreg unregular -> unreg

end


module Iff : sig
  type maybe_not
  val f: (maybe_not, int) result
end

module Packed: sig
  type p
  module type s = sig val x: p end
  val f: (module s) -> p
end

module Implies: sig


  type implied_ok
  val f: ((unit -> implied_ok) ->  implied_ok) -> implied_ok

end

module Classes: sig

  type m
  class c: m -> object method m:m method k: unit -> m end

  type n_ok
  class u: object method u:n_ok end
end

module Incl: sig
  module type s = sig type t end
  module M: sig include s end
end

module Fun: sig

  type e_ok
  module F: sig end -> sig val x: e_ok end

  type g
  module G: sig val x: g end -> sig val x: g end

  type h
  module H: sig val x: h end -> sig val x:h end ->  sig val x: h end

end
