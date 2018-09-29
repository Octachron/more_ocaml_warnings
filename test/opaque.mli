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

type t1 and t2

val f: unit -> t1 * t2

type 'a producer = unit -> 'a

type produced

val x: produced producer

type after_or

val f: [ `X of int | `Y of after_or ]
  -> [`W of float | `Z of after_or * char] -> after_or

type lock1 and lock2
val f: [ `X of lock1 | `Y of lock2 ] -> lock1 * lock2

type field
type field2

val x: int -> <x:field>
val w: <x:field2> -> field2

type inner and inner_ok
val fi: ( (unit -> inner) -> inner) -> inner
val fi: ( (unit -> inner_ok) -> unit) -> inner_ok

type either_ok and either

val either: (either_ok, bool) result -> either_ok
val either' : (either, either) result -> either

type ('a,'b) re = { x: 'a; y: 'b }
type prod
val prod: (prod, int) re -> prod

type recursive
val f: (recursive, recursive) result -> recursive

type recursive_ok
val f: (recursive_ok, recursive_ok list) result -> recursive_ok
