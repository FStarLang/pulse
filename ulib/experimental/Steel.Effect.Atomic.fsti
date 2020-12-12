(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)


module Steel.Effect.Atomic
open FStar.PCM
open Steel.Memory
include Steel.Effect.Common

#set-options "--warn_error -330"  //turn off the experimental feature warning

val observability : Type0
val has_eq_observability (_:unit) : Lemma (hasEq observability)
val observable : observability
val unobservable : observability

let obs_at_most_one o1 o2 =
  o1==unobservable \/ o2==unobservable

let join_obs (o1:observability) (o2:observability) =
  has_eq_observability();
  if observable = o1 || observable = o2
  then observable
  else unobservable

val atomic_repr (a:Type u#a)
   (opened_invariants:inames)
   (g:observability)
   (pre:slprop u#1)
   (post:a -> slprop u#1)
  : Type u#(max a 2)

val return (a:Type u#a)
   (x:a)
   (opened_invariants:inames)
   (#[@@ framing_implicit] p:a -> slprop u#1)
  : atomic_repr a opened_invariants unobservable (return_pre (p x)) (return_post p)

val bind (a:Type u#a) (b:Type u#b)
   (opened_invariants:inames)
   (o1:observability)
   (o2:observability)
   (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
   (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
   (#[@@ framing_implicit] post:post_t b)
   (#[@@ framing_implicit] p1:squash (can_be_split_forall post_f pre_g))
   (#[@@ framing_implicit] p2:squash (can_be_split_post post_g post))
   (f:atomic_repr a opened_invariants o1 pre_f post_f)
   (g:(x:a -> atomic_repr b opened_invariants o2 (pre_g x) (post_g x)))
  : Pure (atomic_repr b opened_invariants (join_obs o1 o2) pre_f post)
         (requires obs_at_most_one o1 o2)
         (ensures fun _ -> True)

val subcomp (a:Type)
  (opened_invariants:inames)
  (o1:observability)
  (o2:observability)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:pre_t) (#[@@ framing_implicit] post_g:post_t a)
  (#[@@ framing_implicit] p1:squash (can_be_split pre_g pre_f))
  (#[@@ framing_implicit] p2:squash (can_be_split_forall post_f post_g))
  (f:atomic_repr a opened_invariants o1 pre_f post_f)
: Pure (atomic_repr a opened_invariants o2 pre_g post_g)
       (requires o1 == observable ==> o2 == observable)
       (ensures fun _ -> True)

// let if_then_else (a:Type)
//   (opened_invariants:inames)
//   (o:observability)
//   (#[@@framing_implicit] pre:pre_t) (#[@@framing_implicit] post:post_t a)
//   (f:atomic_repr a opened_invariants o pre post)
//   (g:atomic_repr a opened_invariants o pre post)
//   (p:Type0)
//   : Type
//   = atomic_repr a opened_invariants o pre post

[@@allow_informative_binders]
total
reifiable reflectable
layered_effect {
  SteelAtomicF : a:Type
              -> opened_invariants:inames
              -> o:observability
              -> pre:slprop u#1
              -> post:(a -> slprop u#1)
              -> Effect
  with
  repr = atomic_repr;
  return = return;
  bind = bind;
  subcomp = subcomp
  // if_then_else = if_then_else
}

[@@allow_informative_binders]
total
reifiable reflectable
new_effect SteelAtomic = SteelAtomicF

val bind_steela_steela (a:Type) (b:Type)
  (opened_invariants:inames)
  (o1:observability)
  (o2:observability)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
  (#[@@ framing_implicit] frame_f:slprop) (#[@@ framing_implicit] frame_g:a -> slprop)
  (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] p:squash (can_be_split_forall
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (#[@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:atomic_repr a opened_invariants o1 pre_f post_f)
  (g:(x:a -> atomic_repr b opened_invariants o2 (pre_g x) (post_g x)))
: Pure (atomic_repr b opened_invariants (join_obs o1 o2)
    (pre_f `star` frame_f)
    post)
    (requires obs_at_most_one o1 o2)
    (ensures fun _ -> True)

polymonadic_bind (SteelAtomic, SteelAtomic) |> SteelAtomicF = bind_steela_steela

val bind_steela_steelaf (a:Type) (b:Type)
  (opened_invariants:inames)
  (o1:observability)
  (o2:observability)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
  (#[@@ framing_implicit] frame_f:slprop)
  (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] p:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
  (#[@@ framing_implicit] p2:squash (can_be_split_post post_g post))
  (f:atomic_repr a opened_invariants o1 pre_f post_f)
  (g:(x:a -> atomic_repr b opened_invariants o2 (pre_g x) (post_g x)))
: Pure (atomic_repr b opened_invariants (join_obs o1 o2)
         (pre_f `star` frame_f)
         post)
       (requires obs_at_most_one o1 o2)
       (ensures fun _ -> True)

polymonadic_bind (SteelAtomic, SteelAtomicF) |> SteelAtomicF = bind_steela_steelaf

val bind_steelaf_steela (a:Type) (b:Type)
  (opened_invariants:inames)
  (o1:observability)
  (o2:observability)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
  (#[@@ framing_implicit] frame_g:a -> slprop)
  (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] p:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g x)))
  (#[@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:atomic_repr a opened_invariants o1 pre_f post_f)
  (g:(x:a -> atomic_repr b opened_invariants o2 (pre_g x) (post_g x)))
: Pure (atomic_repr b opened_invariants (join_obs o1 o2)
        pre_f
        post)
    (requires obs_at_most_one o1 o2)
    (ensures fun _ -> True)

polymonadic_bind (SteelAtomicF, SteelAtomic) |> SteelAtomicF = bind_steelaf_steela

val bind_pure_steela_ (a:Type) (b:Type)
  (opened_invariants:inames)
  (o:observability)
  (wp:pure_wp a)
  (#[@@ framing_implicit] pre:pre_t) (#[@@ framing_implicit] post:post_t b)
  (f:eqtype_as_type unit -> PURE a wp) (g:(x:a -> atomic_repr b opened_invariants o pre post))
: Pure (atomic_repr b opened_invariants o
    pre
    post)
  (requires wp (fun _ -> True))
  (ensures fun _ -> True)

polymonadic_bind (PURE, SteelAtomicF) |> SteelAtomicF = bind_pure_steela_

polymonadic_bind (PURE, SteelAtomic) |> SteelAtomic = bind_pure_steela_

polymonadic_subcomp SteelAtomicF <: SteelAtomic = subcomp

(***** Bind and Subcomp relation with Steel.Atomic *****)

unfold
let bind_req_atomicf_steelf (#a:Type) (#pre_f:pre_t) (#post_f:post_t a) (req_g:(x:a -> req_t (post_f x)))
: req_t pre_f
= fun _ -> forall (x:a) h1. req_g x h1

unfold
let bind_ens_atomicf_steelf (#a:Type) (#b:Type)
  (#pre_f:pre_t)
  (#pre_g:a -> pre_t)
  (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (post:post_t b)
  (_:squash (can_be_split_post post_g post))
: ens_t pre_f b post
= fun _ y h2 -> exists x h1. (ens_g x) h1 y h2

val bind_steelatomicf_steelf (a:Type) (b:Type)
  (is_ghost:observability)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
  (#[@@ framing_implicit] req_g:(x:a -> req_t (pre_g x)))
  (#[@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] p1:squash (can_be_split_forall post_f pre_g))
  (#[@@ framing_implicit] p2:squash (can_be_split_post post_g post))
  (f:atomic_repr a Set.empty is_ghost pre_f post_f)
  (g:(x:a -> Steel.Effect.repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Steel.Effect.repr b pre_f post
    (bind_req_atomicf_steelf req_g)
    (bind_ens_atomicf_steelf ens_g post p2)

polymonadic_bind (SteelAtomicF, Steel.Effect.SteelF) |> Steel.Effect.SteelF = bind_steelatomicf_steelf


unfold
let bind_steelatomic_steelf_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:slprop)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
: req_t (pre_f `star` frame_f)
= fun m0 ->
  (forall (x:a) (m1:hmem (post_f x `star` frame_f)). (req_g x) m1)

unfold
let bind_steelatomic_steelf_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_f:slprop)
  (post:post_t b)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
  (_: squash (can_be_split_post post_g post))
: ens_t (pre_f `star` frame_f) b post
= fun m0 y m2 ->
  (exists (x:a) (m1:hmem (post_f x `star` frame_f)). (ens_g x) m1 y m2)

val bind_steelatomic_steelf (a:Type) (b:Type)
  (o:observability)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
  (#[@@ framing_implicit] req_g:(x:a -> req_t (pre_g x)))
  (#[@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@ framing_implicit] frame_f:slprop)
  (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] p:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
  (#[@@ framing_implicit] p2: squash (can_be_split_post post_g post))
  (f:atomic_repr a Set.empty o pre_f post_f)
  (g:(x:a -> Steel.Effect.repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Steel.Effect.repr b
    (pre_f `star` frame_f)
    post
    (bind_steelatomic_steelf_req req_g frame_f p)
    (bind_steelatomic_steelf_ens ens_g frame_f post p p2)


polymonadic_bind (SteelAtomic, Steel.Effect.SteelF) |> Steel.Effect.SteelF = bind_steelatomic_steelf


unfold
let bind_steelatomic_steel_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:slprop) (frame_g:a -> slprop)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
: req_t (pre_f `star` frame_f)
= fun m0 ->
  (forall (x:a) (m1:hmem (post_f x `star` frame_f)). (req_g x) m1)

unfold
let bind_steelatomic_steel_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_f:slprop) (frame_g:a -> slprop)
  (post:post_t b)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (_:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
: ens_t (pre_f `star` frame_f) b post
= fun m0 y m2 ->
  (exists (x:a) (m1:hmem (post_f x `star` frame_f)).  (ens_g x) m1 y m2)

val bind_steelatomic_steel (a:Type) (b:Type)
  (o:observability)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
  (#[@@ framing_implicit] req_g:(x:a -> req_t (pre_g x)))
  (#[@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@ framing_implicit] frame_f:slprop) (#[@@ framing_implicit] frame_g:a -> slprop)
  (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] p:squash (can_be_split_forall
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (#[@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:atomic_repr a Set.empty o pre_f post_f)
  (g:(x:a -> Steel.Effect.repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Steel.Effect.repr b
    (pre_f `star` frame_f)
    post
    (bind_steelatomic_steel_req req_g frame_f frame_g p)
    (bind_steelatomic_steel_ens ens_g frame_f frame_g post p p2)

polymonadic_bind (SteelAtomic, Steel.Effect.Steel) |> Steel.Effect.SteelF =
  bind_steelatomic_steel


unfold
let subcomp_req_atomic_steel (a:Type) (pre_f:pre_t) : req_t pre_f = fun _ -> True

unfold
let subcomp_ens_atomic_steel (#a:Type) (pre_f:pre_t) (post_f:post_t a)
: ens_t pre_f a post_f
= fun _ _ _ -> True


val subcomp_atomic_steel (a:Type)
  (#[@@framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a) (is_ghost:observability)
  (f:atomic_repr a Set.empty is_ghost pre_f post_f)
: Steel.Effect.repr a pre_f post_f (subcomp_req_atomic_steel a pre_f) (subcomp_ens_atomic_steel pre_f post_f)

polymonadic_subcomp SteelAtomic <: Steel.Effect.Steel = subcomp_atomic_steel
polymonadic_subcomp SteelAtomicF <: Steel.Effect.Steel = subcomp_atomic_steel


val lift_atomic_to_steelT (#a:Type)
                          (#o:observability)
                          (#fp:slprop)
                          (#fp':a -> slprop)
                          ($f:unit -> SteelAtomic a Set.empty o fp fp')
  : Steel.Effect.SteelT a fp fp'

[@@warn_on_use "as_atomic_action is a trusted primitive"]
val as_atomic_action (#a:Type u#a)
                     (#opened_invariants:inames)
                     (#o:observability)
                     (#fp:slprop)
                     (#fp': a -> slprop)
                     (f:action_except a opened_invariants fp fp')
  : SteelAtomic a opened_invariants o fp fp'

val new_invariant (opened_invariants:inames) (p:slprop)
  : SteelAtomic (inv p) opened_invariants unobservable p (fun _ -> emp)

let set_add i o : inames = Set.union (Set.singleton i) o
val with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#opened_invariants:inames)
                   (#o:observability)
                   (#p:slprop)
                   (i:inv p{not (i `Set.mem` opened_invariants)})
                   ($f:unit -> SteelAtomic a (set_add i opened_invariants) o
                                         (p `star` fp)
                                         (fun x -> p `star` fp' x))
  : SteelAtomic a opened_invariants o fp fp'

val frame (#a:Type)
          (#opened_invariants:inames)
          (#o:observability)
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:unit -> SteelAtomic a opened_invariants o pre post)
  : SteelAtomic a opened_invariants o
                (pre `star` frame)
                (fun x -> post x `star` frame)

val change_slprop (#opened_invariants:inames)
                  (p q:slprop)
                  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelAtomic unit opened_invariants unobservable p (fun _ -> q)

// Some utilities
let return_atomic #a #opened_invariants #p (x:a)
  : SteelAtomic a opened_invariants unobservable (p x) p
  = SteelAtomic?.reflect (return a x opened_invariants #p)

val h_assert_atomic (#opened_invariants:_) (p:slprop)
  : SteelAtomic unit opened_invariants unobservable p (fun _ -> p)

val h_intro_emp_l (#opened_invariants:_) (p:slprop)
  : SteelAtomic unit opened_invariants unobservable p (fun _ -> emp `star` p)

val h_elim_emp_l (#opened_invariants:_) (p:slprop)
  : SteelAtomic unit opened_invariants unobservable (emp `star` p) (fun _ -> p)

val intro_pure (#opened_invariants:_) (#p:slprop) (q:prop { q })
  : SteelAtomic unit opened_invariants unobservable p (fun _ -> p `star` pure q)

val h_commute (#opened_invariants:_) (p q:slprop)
  : SteelAtomic unit opened_invariants unobservable (p `star` q) (fun _ -> q `star` p)

val h_assoc_left (#opened_invariants:_) (p q r:slprop)
  : SteelAtomic unit opened_invariants unobservable ((p `star` q) `star` r) (fun _ -> p `star` (q `star` r))

val h_assoc_right (#opened_invariants:_) (p q r:slprop)
  : SteelAtomic unit opened_invariants unobservable (p `star` (q `star` r)) (fun _ -> (p `star` q) `star` r)

val intro_h_exists (#a:Type) (#opened_invariants:_) (x:a) (p:a -> slprop)
  : SteelAtomic unit opened_invariants unobservable (p x) (fun _ -> h_exists p)

val intro_h_exists_erased (#a:Type) (#opened_invariants:_) (x:Ghost.erased a) (p:a -> slprop)
  : SteelAtomic unit opened_invariants unobservable (p x) (fun _ -> h_exists p)

val h_affine (#opened_invariants:_) (p q:slprop)
  : SteelAtomic unit opened_invariants unobservable (p `star` q) (fun _ -> p)

(* Witnessing an existential can only be done for frame-monotonic properties.
 * Most PCMs we use have a witness-invariant pts_to, which means this
 * condition is usually trivial and can be hidden from programs. *)
val witness_h_exists (#a:Type) (#opened_invariants:_) (#p:a -> slprop) (_:squash (is_frame_monotonic p))
  : SteelAtomic (Ghost.erased a) opened_invariants unobservable
                (h_exists p) (fun x -> p x)

module U = FStar.Universe

val lift_h_exists_atomic (#a:_) (#u:_) (p:a -> slprop)
  : SteelAtomic unit u unobservable
                (h_exists p)
                (fun _a -> h_exists #(U.raise_t a) (U.lift_dom p))

val h_exists_cong_atomic (#a:_) (#u:_) (p:a -> slprop) (q:a -> slprop {forall x. equiv (p x) (q x) })
  : SteelAtomic unit u unobservable
                (h_exists p)
                (fun _ -> h_exists q)

val elim_pure (#uses:_) (p:prop)
  : SteelAtomic (_:unit{p}) uses unobservable
                (pure p)
                (fun _ -> emp)
