(*
   Copyright 2023 Microsoft Research

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

module Pulse.Lib.HigherArray
#lang-pulse
open Pulse.Main
open FStar.Tactics.V2
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
module SZ = FStar.SizeT
module Seq = FStar.Seq
open FStar.PCM
module Frac = Pulse.Lib.PCM.Fraction
module PM = Pulse.Lib.PCM.Map
open Pulse.Lib.PCM.Array
module PA = Pulse.Lib.PCM.Array


/// An abstract type to represent a base array (whole allocation
/// unit), exposed for proof purposes only
[@@erasable]
noeq type base_t : Type0 = {
  base_len: base_len:nat { SZ.fits base_len };
  base_ref: base_ref:core_pcm_ref {
    base_ref == null_core_pcm_ref ==> base_len == 0
  };
}

noeq
type array' : Type0 = {
  base_len: base_len:Ghost.erased nat { SZ.fits base_len };
  base_ref: base_ref:core_pcm_ref {
    base_ref == null_core_pcm_ref ==> base_len == hide 0
  };
  offset: offset: nat { offset <= base_len };
  length: length:Ghost.erased nat {offset + length <= base_len };
}
let array elt = array'

let null_array' : array' = { base_len = 0; base_ref = null_core_pcm_ref; offset = 0; length = 0 }

let length (#elt: Type) (a: array elt) = a.length
let base_of #t (a: array t) : base_t = { base_len = a.base_len; base_ref = a.base_ref }
let offset_of #t (a: array t) : GTot nat = a.offset

let is_full_array (#elt: Type) (a: array elt) : Tot prop =
  length a == reveal a.base_len

let null (#a: Type u#1) : array a = null_array'
let is_null a = is_null_core_pcm_ref a.base_ref

let lptr_of #elt (a: array elt) : pcm_ref (PA.pcm elt a.base_len) =
  a.base_ref

let mk_carrier_f #elt (off: nat) (len: nat) (f: perm) (v: Seq.seq elt) (mask: nat -> bool) :
    index_t len -> Pulse.Lib.PCM.Fraction.fractional elt = fun i ->
  if off <= i && i < off + Seq.length v && mask (i - off) then
    Some (Seq.index v (i - off), f)
  else
    None

let mk_carrier #elt (off: nat) (len: nat) (f: perm) (v: Seq.seq elt) (mask: nat -> bool) : carrier elt len =
  Map.map_literal #(index_t len) #(Pulse.Lib.PCM.Fraction.fractional elt) (mk_carrier_f off len f v mask)

irreducible let pull_mask (f: nat -> prop) (len: nat) : Ghost (nat -> bool) (requires True)
    (ensures fun res -> forall i. res i <==> i >= len \/ f i) =
  let s = Seq.init_ghost len fun i -> IndefiniteDescription.strong_excluded_middle (f i) in
  fun i -> if i < len then Seq.index s i else true

let mk_carrier' #t (a: array t) (f: perm) (v: Seq.seq t) (mask: nat -> prop) : GTot (carrier t a.base_len) =
  mk_carrier a.offset a.base_len f v (pull_mask mask a.length)

let mask_nonempty (mask: nat -> prop) (len: nat) : prop =
  exists i. mask i /\ i < len

// workaround for https://github.com/FStarLang/pulse/issues/430
let squash' (t: Type u#1) = squash t

let pts_to_mask #t ([@@@mkey] a: array t) (#[full_default()] f: perm) (v: erased (Seq.seq t)) (mask: nat -> prop) : slprop =
  pcm_pts_to (lptr_of a) (mk_carrier' a f v mask) **
  pure (Seq.length v == reveal a.length /\ (mask_nonempty mask a.length ==> f <=. 1.0R) /\ squash' t)

let pts_to_mask_timeless _ _ _ _ = ()

ghost
fn pts_to_mask_props #t (a:array t) (#p:perm) (#x:Seq.seq t) #mask
  preserves pts_to_mask a #p x mask
  ensures pure (length a == Seq.length x)
  ensures pure (mask_nonempty mask (length a) ==> p <=. 1.0R)
  ensures pure (~(is_null a))
  ensures pure (squash' t)
{
  unfold pts_to_mask a #p x mask;
  pts_to_not_null _ _;
  fold pts_to_mask a #p x mask;
}

ghost
fn pts_to_mask_len #t (a:array t) (#p:perm) (#x:Seq.seq t) #mask
  preserves pts_to_mask a #p x mask
  ensures pure (length a == Seq.length x)
{
  pts_to_mask_props a;
}

ghost
fn pts_to_mask_not_null #a #p (r:array a) (#v:Seq.seq a) #mask
  preserves pts_to_mask r #p v mask
  ensures pure (not (is_null r))
{
  pts_to_mask_props r;
}

ghost fn mask_vext #t (arr: array t) #f #v v' #mask
  requires pts_to_mask arr #f v mask
  requires pure (Seq.length v' == Seq.length v /\
    (forall (i: nat). mask i /\ i < Seq.length v ==> Seq.index v i == Seq.index v' i))
  ensures pts_to_mask arr #f v' mask
{
  unfold pts_to_mask arr #f v mask;
  assert pure (mk_carrier' arr f v mask `Map.equal` mk_carrier' arr f v' mask);
  fold pts_to_mask arr #f v' mask;
}

ghost fn mask_mext #t (arr: array t) #f #v #mask (mask': nat -> prop)
  requires pts_to_mask arr #f v mask
  requires pure (forall (i: nat). i < Seq.length v ==> (mask i <==> mask' i))
  ensures pts_to_mask arr #f v mask'
{
  unfold pts_to_mask arr #f v mask;
  assert pure (mk_carrier' arr f v mask `Map.equal` mk_carrier' arr f v mask');
  fold pts_to_mask arr #f v mask';
}

ghost fn mask_ext #t (arr: array t) #f #v #mask v' (mask': nat -> prop)
  requires pts_to_mask arr #f v mask
  requires pure (forall (i: nat). i < Seq.length v ==> (mask i <==> mask' i))
  requires pure (Seq.length v' == Seq.length v /\
    (forall (i: nat). mask i /\ i < Seq.length v ==> Seq.index v i == Seq.index v' i))
  ensures pts_to_mask arr #f v' mask'
{
  mask_vext arr v';
  mask_mext arr mask';
}

let get_mask_idx (m: nat->prop) (l: nat) : GTot (i: nat { mask_nonempty m l ==> i < l /\ m i }) =
  if IndefiniteDescription.strong_excluded_middle (mask_nonempty m l) then
    IndefiniteDescription.indefinite_description_ghost nat fun i -> i < l /\ m i
  else
    0

ghost fn pcm_rw #t
    (a1: array t) p1 s1 m1
    (a2: array t) p2 s2 m2
  requires pts_to_mask #t a1 #p1 s1 m1
  requires pure (
    a1.base_len == a2.base_len /\
    a1.base_ref == a2.base_ref /\
    reveal a2.length == Seq.length s2 /\
    mk_carrier' a1 p1 s1 m1 `Map.equal` mk_carrier' a2 p2 s2 m2
  )
  ensures pts_to_mask #t a2 #p2 s2 m2
{
  unfold pts_to_mask a1 #p1 s1 m1;
  rewrite each lptr_of a1 as lptr_of a2;
  let i = get_mask_idx m2 (length a2);
  assert pure (mask_nonempty m2 (length a2) ==>
    Map.sel (mk_carrier' a2 p2 s2 m2) (i + a2.offset) == Some (Seq.index s2 i, p2));
  fold pts_to_mask a2 #p2 s2 m2;
}

ghost fn pcm_share #t
    (a: array t) p s m
    (a1: array t) p1 s1 m1
    (a2: array t) p2 s2 m2
  requires pts_to_mask a #p s m
  requires pure (Seq.length s1 == a1.length)
  requires pure (Seq.length s2 == a2.length)
  requires pure (
    a1.base_len == a.base_len /\ a2.base_len == a.base_len /\
    a1.base_ref == a.base_ref /\ a2.base_ref == a.base_ref /\
    composable (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2) /\
    compose (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2)
      `Map.equal` mk_carrier' a p s m
  )
  ensures pts_to_mask a1 #p1 s1 m1
  ensures pts_to_mask a2 #p2 s2 m2
{
  unfold pts_to_mask a #p s m;
  Pulse.Lib.Core.share (lptr_of a) (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2);
  rewrite
    pcm_pts_to (lptr_of a) (mk_carrier' a1 p1 s1 m1) as
    pcm_pts_to (lptr_of a1) (mk_carrier' a1 p1 s1 m1);
  rewrite
    pcm_pts_to (lptr_of a) (mk_carrier' a2 p2 s2 m2) as
    pcm_pts_to (lptr_of a2) (mk_carrier' a2 p2 s2 m2);
  let i1 = get_mask_idx m1 (length a1);
  let i2 = get_mask_idx m2 (length a2);
  assert pure (mask_nonempty m1 (length a1) ==>
    Some? (Map.sel (mk_carrier' a p s m) (i1 + a1.offset)));
  fold pts_to_mask a1 #p1 s1 m1;
  assert pure (mask_nonempty m2 (length a2) ==>
    Some? (Map.sel (mk_carrier' a p s m) (i2 + a2.offset)));
  fold pts_to_mask a2 #p2 s2 m2;
}

ghost fn pcm_gather #t
    (a: array t) p s m
    (a1: array t) p1 s1 m1
    (a2: array t) p2 s2 m2
  requires pure (Seq.length s == a.length)
  requires pure (
    a1.base_len == a.base_len /\ a2.base_len == a.base_len /\
    a1.base_ref == a.base_ref /\ a2.base_ref == a.base_ref /\
    (composable (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2) ==>
    compose (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2)
      `Map.equal` mk_carrier' a p s m)
  )
  requires pts_to_mask a1 #p1 s1 m1
  requires pts_to_mask a2 #p2 s2 m2
  ensures pts_to_mask a #p s m
  ensures pure (
    a1.base_len == a.base_len /\ a2.base_len == a.base_len /\
    a1.base_ref == a.base_ref /\ a2.base_ref == a.base_ref /\
    composable (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2) /\
    compose (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2)
      `Map.equal` mk_carrier' a p s m
  )
{
  unfold pts_to_mask a1 #p1 s1 m1;
  unfold pts_to_mask a2 #p2 s2 m2;
  rewrite
    pcm_pts_to (lptr_of a1) (mk_carrier' a1 p1 s1 m1) as
    pcm_pts_to (lptr_of a) (mk_carrier' a1 p1 s1 m1);
  rewrite
    pcm_pts_to (lptr_of a2) (mk_carrier' a2 p2 s2 m2) as
    pcm_pts_to (lptr_of a) (mk_carrier' a2 p2 s2 m2);
  Pulse.Lib.Core.gather (lptr_of a) (mk_carrier' a1 p1 s1 m1) (mk_carrier' a2 p2 s2 m2);
  let i = get_mask_idx m (length a);
  assert pure (mask_nonempty m a.length ==>
    Map.sel (mk_carrier' a p s m) (i + a.offset) == Some (Seq.index s i, p));
  fold pts_to_mask a #p s m;
}

ghost
fn mask_share #a (arr:array a) (#s: Seq.seq a) #p #mask
  requires pts_to_mask arr #p s mask
  ensures pts_to_mask arr #(p /. 2.0R) s mask
  ensures pts_to_mask arr #(p /. 2.0R) s mask
{
  pts_to_mask_props arr;
  pcm_share
    arr p s mask
    arr (p /. 2.0R) s mask
    arr (p /. 2.0R) s mask;
}

[@@allow_ambiguous]
ghost fn mask_gather #t (arr: array t) #p1 #p2 #s1 #s2 #mask1 #mask2
  requires pts_to_mask arr #p1 s1 mask1
  requires pts_to_mask arr #p2 s2 mask2
  requires pure (forall i. mask1 i <==> mask2 i)
  ensures exists* (v: Seq.seq t). pts_to_mask arr #(p1 +. p2) v mask1 **
    pure ((Seq.length v == Seq.length s1 /\ Seq.length v == Seq.length s2) /\
      (forall (i: nat). i < Seq.length v /\ mask1 i ==> Seq.index v i == Seq.index s1 i /\ Seq.index v i == Seq.index s2 i))
{
  mask_mext arr #p2 #s2 mask1;
  pts_to_mask_props arr #p1 #s1 #mask1;
  pts_to_mask_props arr #p2 #s2 #mask1;
  pcm_gather
    arr (p1 +. p2) s1 mask1
    arr p1 s1 mask1
    arr p2 s2 mask1;
  assert pure (forall (i: nat). (i < Seq.length s1 /\ mask1 i) ==>
    Map.sel (mk_carrier' arr p1 s1 mask1) (i + arr.offset) == Some (Seq.index s1 i, p1));
}

ghost fn split_mask #t (arr: array t) #f #v #mask (pred: nat -> prop)
  requires pts_to_mask arr #f v mask
  ensures pts_to_mask arr #f v (mask_isect mask pred)
  ensures pts_to_mask arr #f v (mask_diff mask pred)
{
  pts_to_mask_props arr;
  pcm_share
    arr f v mask
    arr f v (mask_isect mask pred)
    arr f v (mask_diff mask pred);
}

let mix #t (v1: Seq.seq t) (v2: Seq.seq t { Seq.length v1 == Seq.length v2 }) (mask: nat -> prop) :
    GTot (res: Seq.seq t { Seq.length res == Seq.length v1 /\
      (forall (i: nat). i < Seq.length res ==>
        (mask i ==> Seq.index res i == Seq.index v1 i) /\
        (~(mask i) ==> Seq.index res i == Seq.index v2 i)) }) =
  Seq.init_ghost (Seq.length v1) fun i ->
    if IndefiniteDescription.strong_excluded_middle (mask i) then Seq.index v1 i else Seq.index v2 i

[@@allow_ambiguous]
ghost fn join_mask #t (arr: array t) #f #v1 #v2 #mask1 #mask2
  requires pts_to_mask arr #f v1 mask1
  requires pts_to_mask arr #f v2 mask2
  requires pure (forall i. ~(mask1 i /\ mask2 i))
  ensures exists* (v: Seq.seq t).
    pts_to_mask arr #f v (fun i -> mask1 i \/ mask2 i) **
    pure (Seq.length v == Seq.length v1 /\ Seq.length v == Seq.length v2 /\
      (forall (i: nat). i < Seq.length v ==>
        (mask1 i ==> Seq.index v i == Seq.index v1 i) /\
        (mask2 i ==> Seq.index v i == Seq.index v2 i)))
{
  pts_to_mask_props arr #f #v1 #mask1;
  pts_to_mask_props arr #f #v2 #mask2;
  let v = mix v1 v2 mask1;
  with mask. assert pure (mask == (fun i -> mask1 i \/ mask2 i));
  pcm_gather
    arr f v mask
    arr f v1 mask1
    arr f v2 mask2;
}

[@@allow_ambiguous]
ghost fn join_mask' #t (arr: array t) #f (#v: erased (Seq.seq t)) #mask1 #mask2
  requires pts_to_mask arr #f v mask1
  requires pts_to_mask arr #f v mask2
  requires pure (forall i. ~(mask1 i /\ mask2 i))
  ensures pts_to_mask arr #f v (fun i -> mask1 i \/ mask2 i)
{
  join_mask arr #f #v #v #mask1 #mask2;
  mask_vext arr v;
}

[@@allow_ambiguous]
ghost
fn pts_to_mask_injective_eq #a #p0 #p1 #s0 #s1 #mask0 #mask1 (arr:array a)
  preserves pts_to_mask arr #p0 s0 mask0
  preserves pts_to_mask arr #p1 s1 mask1
  ensures pure (Seq.length s0 == Seq.length s1 /\
    (forall (i: nat). i < Seq.length s0 /\ mask0 i /\ mask1 i ==>
      Seq.index s0 i == Seq.index s1 i))
{
  unfold pts_to_mask arr #p0 s0 mask0;
  unfold pts_to_mask arr #p1 s1 mask1;
  Pulse.Lib.Core.gather (lptr_of arr) (mk_carrier' arr p0 s0 mask0) (mk_carrier' arr p1 s1 mask1);
  Pulse.Lib.Core.share (lptr_of arr) (mk_carrier' arr p0 s0 mask0) (mk_carrier' arr p1 s1 mask1);
  assert pure (forall (i: nat). i < Seq.length s0 /\ mask0 i ==>
    Map.sel (mk_carrier' arr p0 s0 mask0) (i + arr.offset) == Some (Seq.index s0 i, p0));
  fold pts_to_mask arr #p0 s0 mask0;
  fold pts_to_mask arr #p1 s1 mask1;
}

fn mask_read #t (a: array t) (i: SZ.t) #p (#s: erased (Seq.seq t) { SZ.v i < Seq.length s }) #mask
  preserves pts_to_mask a #p s mask
  requires pure (mask (SZ.v i))
  returns res: t
  ensures pure (res == Seq.index s (SZ.v i))
{
  unfold pts_to_mask a #p s mask;
  with w. assert pcm_pts_to (lptr_of a) w;
  let v = Pulse.Lib.Core.read (lptr_of a) w (fun _ -> w);
  fold pts_to_mask a #p s mask;
  fst (Some?.v (FStar.Map.sel v (a.offset + SZ.v i)));
}

fn mask_write #t (a: array t) (i: SZ.t) (v: t) (#s: erased (Seq.seq t) { SZ.v i < Seq.length s }) #mask
  requires pts_to_mask a s mask
  requires pure (mask (SZ.v i))
  ensures pts_to_mask a (Seq.upd s (SZ.v i) v) mask
{
  unfold pts_to_mask a s mask;
  with w. assert (pcm_pts_to (lptr_of a) w);
  Pulse.Lib.Core.write (lptr_of a) w _
      (PM.lift_frame_preserving_upd
        _ _
        (Frac.mk_frame_preserving_upd
          (Seq.index s (SZ.v i))
          v
        )
        _ (a.offset + SZ.v i));
  assert pure (
    Map.upd (mk_carrier' a 1.0R s mask) (a.offset + SZ.v i) (Some (v, 1.0R))
    `Map.equal`
    mk_carrier' a 1.0R (Seq.upd s (SZ.v i) v) mask
  );
  fold pts_to_mask a (Seq.upd s (SZ.v i) v) mask;
}

let sub_impl #t (arr: array t) (i: nat) (j: erased nat { i <= j /\ j <= length arr }) : array t =
  { arr with offset = arr.offset + i; length = j - i }

let gsub #t (arr: array t) (i: nat) (j: nat { i <= j /\ j <= length arr }) : GTot (array t) =
  sub_impl arr i j

ghost fn gsub_intro #t (arr: array t) #f #mask (i j: nat) (#v: erased (Seq.seq t) { i <= j /\ j <= Seq.length v })
  requires pts_to_mask arr #f v mask
  requires pure (forall (k: nat). mask k ==> i <= k /\ k < j)
  returns _: squash (length arr == Seq.length v)
  ensures pts_to_mask (gsub arr i j) #f (Seq.slice v i j) (fun k -> mask (k + i))
{
  pts_to_mask_props arr;
  pcm_rw
    arr f v mask
    (gsub arr i j) f (Seq.slice v i j) (fun k -> mask (k + i));
  ()
}

let elim_squash (t: Type u#1 { squash' t }) : GTot t =
  let h : squash (squash' t) = () in
  let h : squash t = IndefiniteDescription.elim_squash h in
  IndefiniteDescription.elim_squash h

ghost fn gsub_elim #t (arr: array t) #f (#mask: nat->prop) (i j: nat)
    (#v: erased (Seq.seq t) { i <= j /\ j <= length arr })
  requires pts_to_mask (gsub arr i j) #f v mask
  returns _: squash (j - i == Seq.length v)
  ensures exists* v'.
    pts_to_mask arr #f v' (fun k -> i <= k /\ k < j /\ mask (k - i)) **
    pure (Seq.length v' == length arr /\ (forall (k:nat). k < j - i ==> Seq.index v k == Seq.index v' (k + i)))
{
  pts_to_mask_props (gsub arr i j);
  let dummy = elim_squash t;
  let v' = Seq.init_ghost (length arr) (fun k ->
    if i <= k && k < j then Seq.index v (k - i) else dummy);
  pcm_rw
    (gsub arr i j) f v mask
    arr f v' (fun k -> i <= k /\ k < j /\ mask (k - i));
  ()
}

unobservable
fn sub #t (arr: array t) #f #mask (i: SZ.t) (j: SZ.t)
    (#v: erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length (reveal v) })
  requires pts_to_mask arr #f v mask
  returns sub: (sub: array t { length arr == Seq.length (reveal v) })
  ensures rewrites_to sub (gsub arr (SZ.v i) (SZ.v j))
  ensures pts_to_mask sub #f (Seq.slice v (SZ.v i) (SZ.v j)) (fun k -> mask (k + SZ.v i))
  ensures pts_to_mask arr #f v (fun k -> mask k /\ ~(SZ.v i <= k /\ k < SZ.v j))
{
  let pred = (fun k -> SZ.v i <= k /\ k < SZ.v j);
  pts_to_mask_props arr;
  split_mask arr pred;
  gsub_intro arr #f #(mask_isect mask pred) (SZ.v i) (SZ.v j);
  mask_mext (gsub arr (SZ.v i) (SZ.v j)) (fun k -> mask (k + SZ.v i));
  rewrite each gsub arr (SZ.v i) (SZ.v j) as sub_impl arr (SZ.v i) (SZ.v j);
  sub_impl arr (SZ.v i) (SZ.v j)
}

[@@allow_ambiguous]
ghost fn return_sub #t (arr sub: array t) #f (#v #vsub: erased (Seq.seq t)) #mask #masksub (#i: nat) (#j: nat { i <= j /\ j <= length arr })
  requires pts_to_mask arr #f v mask
  requires pts_to_mask (gsub arr i j) #f vsub masksub
  requires pure (forall (k: nat). i <= k /\ k < j ==> ~(mask k))
  ensures exists* v'. pts_to_mask arr #f v' (fun k -> mask k \/ (i <= k /\ k < j /\ masksub (k - i)))
    ** pure (Seq.length v == Seq.length v' /\ i + Seq.length vsub == j /\ j <= Seq.length v /\
      (forall (k: nat). k < Seq.length v' ==>
      Seq.index v' k == (if i <= k && k < j then Seq.index vsub (k - i) else Seq.index v k)))
{
  gsub_elim arr i j;
  join_mask arr;
  let v' = Seq.init_ghost (Seq.length v) (fun k -> 
    if i <= k && k < j then Seq.index vsub (k - i) else Seq.index v k);
  mask_ext arr v' (fun k -> mask k \/ (i <= k /\ k < j /\ masksub (k - i)));
}

let pts_to (#elt: Type u#1) (a: array elt) (#p: perm) (s: Seq.seq elt) : Tot slprop =
  pts_to_mask a #p s fun i -> True

ghost fn to_mask #t (arr: array t) #f #v
  requires arr |-> Frac f v
  ensures pts_to_mask arr #f v (fun _ -> True)
{
  unfold pts_to arr #f v;
}

ghost fn from_mask #t (arr: array t) #f #v #mask
  requires pts_to_mask arr #f v mask
  requires pure (forall i. mask i)
  ensures arr |-> Frac f v
{
  mask_mext arr (fun _ -> True);
  fold pts_to arr #f v;
}

let pts_to_timeless _ _ _ = ()

ghost
fn pts_to_len
  (#elt: Type u#1)
  (a:array elt)
  (#p:perm)
  (#x:Seq.seq elt)
  requires pts_to a #p x
  ensures pts_to a #p x ** pure (length a == Seq.length x)
{
  unfold pts_to a #p x;
  pts_to_mask_len a;
  fold pts_to a #p x;
}

ghost
fn pts_to_not_null (#a:_) (#p:_) (r:array a) (#v:Seq.seq a)
  preserves r |-> Frac p v
  ensures  pure (not (is_null #a r))
{
  unfold pts_to r #p v;
  pts_to_mask_not_null _;
  fold pts_to r #p v;
}

let intro_squash #t (x: t) : squash' t = ()

fn alloc
    (#elt: Type u#1)
    (x: elt)
    (n: SZ.t)
  returns a:array elt
ensures 
  pts_to a (Seq.create (SZ.v n) x) **
  pure (length a == SZ.v n /\ is_full_array a)
{
  let v = mk_carrier 0 (SZ.v n) 1.0R (Seq.create (SZ.v n) x) (fun _ -> true);
  FStar.PCM.compatible_refl (PA.pcm elt (SZ.v n)) v;
  let b = Pulse.Lib.Core.alloc #_ #(PA.pcm elt (SZ.v n)) v;
  Pulse.Lib.Core.pts_to_not_null b _;
  let arr: array elt = { base_ref = b; base_len = SZ.v n; length = SZ.v n; offset = 0 };
  rewrite each b as lptr_of arr;
  assert pure (v `Map.equal` mk_carrier' arr 1.0R (Seq.create (SZ.v n) x) (fun _ -> l_True));
  intro_squash x;
  fold pts_to_mask arr (Seq.create (SZ.v n) x) (fun _ -> l_True);
  fold pts_to arr (Seq.create (SZ.v n) x);
  arr
}

fn read
    (#t: Type)
    (a: array t)
    (i: SZ.t)
    (#p: perm)
    (#s: Ghost.erased (Seq.seq t){SZ.v i < Seq.length s})
  preserves pts_to a #p s
  returns res:t
  ensures pure (res == Seq.index s (SZ.v i))
{
  unfold pts_to a #p s;
  let res = mask_read a i;
  fold pts_to a #p s;
  res
}

let op_Array_Access = read

fn write
    (#t: Type)
    (a: array t)
    (i: SZ.t)
    (v: t)
    (#s: Ghost.erased (Seq.seq t) {SZ.v i < Seq.length s})
  requires pts_to a s
  ensures pts_to a (Seq.upd s (SZ.v i) v)
{
  unfold pts_to a #1.0R s;
  mask_write a i v;
  fold pts_to a #1.0R (Seq.upd s (SZ.v i) v);
}

let op_Array_Assignment = write

fn free
    (#elt: Type)
    (a: array elt)
    (#s: Ghost.erased (Seq.seq elt))
  requires pts_to a s
  requires pure (is_full_array a)
{
  unfold pts_to a #1.0R s;
  unfold pts_to_mask a #1.0R s (fun _ -> True);
  with w. assert (pcm_pts_to (lptr_of a) w);
  drop_ (pcm_pts_to (lptr_of a) _)
}

ghost
fn share
  (#elt:Type)
  (arr:array elt)
  (#s:Ghost.erased (Seq.seq elt))
  (#p:perm)
  requires pts_to arr #p s
  ensures pts_to arr #(p /. 2.0R) s ** pts_to arr #(p /. 2.0R) s
{
  unfold pts_to arr #p s;
  mask_share arr;
  fold pts_to arr #(p /. 2.0R) s;
  fold pts_to arr #(p /. 2.0R) s;
}

[@@allow_ambiguous]
ghost
fn gather
  (#a:Type)
  (arr:array a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
  requires pts_to arr #p0 s0 ** pts_to arr #p1 s1
  ensures pts_to arr #(p0 +. p1) s0 ** pure (s0 == s1)
{
  unfold pts_to arr #p0 s0;
  unfold pts_to arr #p1 s1;
  mask_gather arr;
  with v. assert pts_to_mask arr #(p0 +. p1) v (fun _ -> True);
  assert pure (v `Seq.equal` s1 /\ v `Seq.equal` s0);
  fold pts_to arr #(p0 +. p1) s0;
}

[@@allow_ambiguous]
ghost
fn pts_to_injective_eq
    (#a:Type)
    (#p0 #p1:perm)
    (#s0 #s1:Seq.seq a)
    (arr:array a)
  preserves pts_to arr #p0 s0
  preserves pts_to arr #p1 s1
  ensures pure (s0 == s1)
{
  unfold pts_to arr #p0 s0;
  unfold pts_to arr #p1 s1;
  pts_to_mask_injective_eq arr;
  assert pure (Seq.equal s0 s1);
  fold pts_to arr #p0 s0;
  fold pts_to arr #p1 s1;
}

ghost
fn pts_to_perm_bound (#a:_) (#p:_) (arr: array a) (#s:Seq.seq a)
  preserves pts_to arr #p s
  requires pure (Seq.length s > 0)
  ensures pure (p <=. 1.0R)
{
  unfold pts_to arr #p s;
  pts_to_mask_props arr;
  fold pts_to arr #p s;
}

open Pulse.Lib.WithPure

let pts_to_range
  (#a:Type)
  ([@@@mkey] x:array a)
  (i j : nat)
  (#[exact (`1.0R)] p:perm)
  (s : Seq.seq a)
: slprop
= with_pure (i <= j /\ j <= length x) fun _ -> pts_to (gsub x i j) #p s

ghost fn fold_pts_to_range #a (x: array a) (i: nat) (j: nat { i <= j /\ j <= length x }) #p s #mask
  requires pts_to_mask (gsub x i j) #p s mask
  requires pure (forall (k: nat). k < j - i ==> mask k)
  ensures pts_to_range x i j #p s
{
  pts_to_mask_props (gsub x i j);
  mask_mext (gsub x i j) (fun _ -> True);
  fold pts_to (gsub x i j) #p s;
  intro_with_pure (i <= j /\ j <= length x) (fun _ -> pts_to (gsub x i j) #p s) ();
  fold pts_to_range x i j #p s;
}

ghost fn unfold_pts_to_range #a (x: array a) (i j: nat) #p s
  requires pts_to_range x i j #p s
  returns _: squash (i <= j /\ j <= length x)
  ensures pts_to_mask (gsub x i j) #p s (fun _ -> True)
{
  unfold pts_to_range x i j #p s;
  elim_with_pure (i <= j /\ j <= length x) (fun _ -> pts_to (gsub x i j) #p s);
  unfold pts_to (gsub x i j) #p s;
}

let pts_to_range_timeless (#a:Type) (x:array a) (i j : nat) (p:perm) (s:Seq.seq a)
  : Lemma (timeless (pts_to_range x i j #p s))
          [SMTPat (timeless (pts_to_range x i j #p s))]
  = ()

ghost
fn pts_to_range_prop
  (#elt: Type)
  (a: array elt)
  (#i #j: nat)
  (#p: perm)
  (#s: Seq.seq elt)
  requires pts_to_range a i j #p s
  ensures pts_to_range a i j #p s ** pure (
      (i <= j /\ j <= length a /\ Seq.length s == j - i)
    )
{
  unfold_pts_to_range a i j #p s;
  pts_to_mask_len (gsub a i j);
  fold_pts_to_range a i j #p s;
}

ghost
fn pts_to_range_intro
  (#elt: Type)
  (a: array elt)
  (p: perm)
  (s: Seq.seq elt)
  requires pts_to a #p s
  ensures pts_to_range a 0 (length a) #p s
{
  unfold pts_to a #p s;
  rewrite each a as gsub a 0 (length a);
  fold_pts_to_range a 0 (length a) #p s;
}

ghost
fn pts_to_range_elim
  (#elt: Type)
  (a: array elt)
  (p: perm)
  (s: Seq.seq elt)
  requires pts_to_range a 0 (length a) #p s
  ensures pts_to a #p s
{
  unfold_pts_to_range a 0 (length a) #p s;
  rewrite each gsub a 0 (length a) as a;
  fold pts_to a #p s;
}

ghost
fn pts_to_range_split
  (#elt: Type)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s: Seq.seq elt)
requires
  pts_to_range a i j #p s **
  pure (i <= m /\ m <= j)
ensures
  exists* s1 s2.
    pts_to_range a i m #p s1 **
    pts_to_range a m j #p s2 **
    pure (
      i <= m /\ m <= j /\ j <= length a /\
      eq2 #int (Seq.length s) (j - i) /\
      s1 == Seq.slice s 0 (m - i) /\
      s2 == Seq.slice s (m - i) (Seq.length s) /\
      s == Seq.append s1 s2
    )
{
  unfold_pts_to_range _ _ _ _;
  pts_to_mask_props (gsub a i j);
  let s1 = Seq.slice s 0 (m - i);
  let s2 = Seq.slice s (m - i) (Seq.length s);
  pcm_share
    (gsub a i j) p s (fun _ -> True)
    (gsub a i m) p s1 (fun _ -> True)
    (gsub a m j) p s2 (fun _ -> True);
  fold_pts_to_range a i m #p s1;
  fold_pts_to_range a m j #p s2;
  assert pure (s `Seq.equal` Seq.append s1 s2);
}

let adjacent (#elt: Type) (a1 a2: array elt) : Tot prop =
  base_of a1 == base_of a2 /\
  offset_of a1 + length a1 == offset_of a2

let merge (#elt: Type) (a1: array elt) (a2:array elt { adjacent a1 a2 }) : array elt
= { a1 with length = a1.length + a2.length }

ghost
fn pts_to_range_join
  (#elt: Type)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s1 #s2: Seq.seq elt)
requires
  pts_to_range a i m #p s1 ** pts_to_range a m j #p s2
  ensures pts_to_range a i j #p (s1 `Seq.append` s2)
{
  unfold_pts_to_range a i m #p s1;
  unfold_pts_to_range a m j #p s2;
  gsub_elim a i m;
  gsub_elim a m j;
  join_mask a;
  gsub_intro a i j;
  mask_ext (gsub a i j) (Seq.append s1 s2) (fun _ -> True);
  fold_pts_to_range a i j #p (Seq.append s1 s2);
}

fn pts_to_range_index
  (#t: Type)
  (a: array t)
  (i: SZ.t)
  (#l: Ghost.erased nat{l <= SZ.v i})
  (#r: Ghost.erased nat{SZ.v i < r})
  (#s: Ghost.erased (Seq.seq t))
  (#p: perm)
  requires pts_to_range a l r #p s
  returns res:t
  ensures
    pts_to_range a l r #p s **
    pure (eq2 #int (Seq.length s) (r - l) /\
          res == Seq.index s (SZ.v i - l))
{
  unfold_pts_to_range a l r #p s;
  gsub_elim a l r;
  let res = mask_read a i;
  gsub_intro a l r;
  mask_vext (gsub a l r) s;
  fold_pts_to_range a l r #p s;
  res
}

fn pts_to_range_upd
  (#t: Type)
  (a: array t)
  (i: SZ.t)
  (v: t)
  (#l: Ghost.erased nat{l <= SZ.v i})
  (#r: Ghost.erased nat{SZ.v i < r})
  (#s0: Ghost.erased (Seq.seq t))
  requires pts_to_range a l r #1.0R s0
  ensures
    exists* s.
      pts_to_range a l r s **
      pure (
          eq2 #int (Seq.length s0) (r - l) /\
          s == Seq.upd s0 (SZ.v i - l) v
      )
{
  unfold_pts_to_range a l r #1.0R s0;
  gsub_elim a l r;
  mask_write a i v;
  gsub_intro a l r;
  let s = hide (Seq.upd s0 (SZ.v i - l) v);
  mask_vext (gsub a l r) s;
  fold_pts_to_range a l r #1.0R s;
}

ghost
fn pts_to_range_share
  (#a:Type)
  (arr:array a)
  (#l #r: nat)
  (#s:Seq.seq a)
  (#p:perm)
      requires pts_to_range arr l r #p s
      ensures pts_to_range arr l r #(p /. 2.0R) s ** pts_to_range arr l r #(p /. 2.0R) s
{
  unfold_pts_to_range arr l r #p s;
  mask_share (gsub arr l r);
  fold_pts_to_range arr l r s;
  fold_pts_to_range arr l r s;
}

ghost
fn pts_to_range_gather
  (#a:Type)
  (arr:array a)
  (#l #r: nat)
  (#s0 #s1: Seq.seq a)
  (#p0 #p1:perm)
      requires pts_to_range arr l r #p0 s0 ** pts_to_range arr l r #p1 s1
      ensures pts_to_range arr l r #(p0 +. p1) s0 ** pure (s0 == s1)
{
  unfold_pts_to_range arr l r s0;
  unfold_pts_to_range arr l r s1;
  mask_gather (gsub arr l r);
  with s. assert pts_to_mask (gsub arr l r) #(p0 +. p1) s (fun _ -> True);
  fold_pts_to_range arr l r s;
  assert pure (Seq.equal s s0 /\ Seq.equal s s1);
}
