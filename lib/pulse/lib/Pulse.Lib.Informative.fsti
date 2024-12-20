module Pulse.Lib.Informative
open FStar.Ghost
open FStar.IndefiniteDescription { indefinite_description_ghost, strong_excluded_middle }
open Pulse.Lib.NonInformative
open FStar.Squash

let obs_eq (#t: Type u#a) (x y: t) =
  forall (f: t -> bool). f x == f y

val obs_eq_congr (#t: Type u#a) (#s: Type u#b) (f: t -> s) (x y: t) :
  Lemma (requires obs_eq x y) (ensures obs_eq (f x) (f y))

[@@erasable]
class fully_informative (t: Type u#a) =
  { eq_iff_obs_eq: x:t -> y:t -> Lemma (obs_eq x y <==> x == y) }

val fully_informative_intro (t: Type u#a)
  (h: (x: t -> y: t { x =!= y } -> GTot (f: (t->bool) { f x =!= f y }))) :
  fully_informative t

val fully_informative_sep (#t: Type u#a) {| fully_informative t |} (x y: t) :
  Ghost (t -> bool) (requires x =!= y) (ensures fun f -> f x =!= f y)

instance val fully_informative_eqtype (t: eqtype) : fully_informative t

instance val fully_informative_tuple2 (t: Type u#a) (s: Type u#b) {| fully_informative t |} {| fully_informative s |} : fully_informative (t & s)

val obs_eq_of_noninfo (#t: Type u#a) {| non_informative t |} (x y: t) : Lemma (obs_eq x y)

val parametricity
  (#t: Type u#a) {| non_informative t |}
  (#s: Type u#b) {| fully_informative s |}
  (f: t -> s) (x:t) (y:t) : Lemma (f x == f y)
