module Pulse.Lib.Informative
open FStar.Ghost
open FStar.IndefiniteDescription { indefinite_description_ghost, strong_excluded_middle }
open Pulse.Lib.NonInformative
open FStar.Squash

let obs_eq_congr #t #s f x y =
  introduce forall (g: s->bool). g (f x) == g (f y) with
  let h: squash (forall (h:t->bool). h x == h y) = get_proof _ in
  Classical.Sugar.forall_elim (fun z -> g (f z)) h

let fully_informative_intro t h =
  { eq_iff_obs_eq = fun (x y: t) ->
    introduce obs_eq x y /\ x =!= y ==> x == y with _.
    let f = h x y in () }

let fully_informative_sep #t x y =
  eq_iff_obs_eq x y; indefinite_description_ghost (t -> bool) fun f -> f x =!= f y

instance fully_informative_eqtype (t: eqtype) : fully_informative t =
  fully_informative_intro t fun x y z -> z = x

instance fully_informative_tuple2 (t: Type u#a) (s: Type u#b) {| fully_informative t |} {| fully_informative s |} : fully_informative (t & s) =
  fully_informative_intro (t & s) fun x y ->
    if strong_excluded_middle (x._1 == y._1) then
      let g = fully_informative_sep x._2 y._2 in
      (fun (z:t&s) -> g z._2)
    else
      let f = fully_informative_sep x._1 y._1 in
      (fun (z:t&s) -> f z._1)

assume val ghost_irrelevance (f: erased bool -> bool) : Lemma (f false == f true)

let obs_eq_of_noninfo (#t: Type u#a) {| non_informative t |} (x y: t) : Lemma (obs_eq x y) =
  introduce forall (f: t->bool). f x == f y with
  ghost_irrelevance fun b -> f (reveal (if b then x else y))

let parametricity f x y =
  obs_eq_of_noninfo x y;
  eq_iff_obs_eq (f x) (f y);
  obs_eq_congr f x y
