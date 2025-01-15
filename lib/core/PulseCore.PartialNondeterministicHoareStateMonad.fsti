(*
   Copyright 2024 Microsoft Research

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

module PulseCore.PartialNondeterministicHoareStateMonad
open FStar.Ghost
type level = n:erased nat & (unit -> Dv (k:nat { k == reveal n }))
let mk_level (n:nat) : level = (| hide n, ((fun () -> n) <: unit -> Dv (k:nat{k == reveal n})) |)

open PulseCore.HoareStateMonad
module NST = PulseCore.NondeterministicHoareStateMonad
let req_t (s:Type) = s -> prop
let ens_t (s:Type) (a:Type) = s -> a -> s -> prop

val pnst
    (#s:Type u#s)
    (a:Type u#a)
    (pre:req_t s)
    (post:ens_t s a)
: Type0

val repr #s #a #pre #post (f:pnst #s a pre post) :
  s0:s { pre s0 } ->
  (nat -> bool) ->
  nat ->
  Dv (res:(a & s & nat) {
    post s0 res._1 res._2
  })


val lift #s #a #pre #post (f:NST.nst a pre post) : pnst #s a pre post

val return (#s:Type u#s)
           (#a:Type u#a)
           (x:a)
: pnst #s a (fun _ -> True) (fun s0 v s1 -> x == v /\ s0 == s1)           

val bind
      (#s:Type u#s)
      (#a:Type u#a)
      (#b:Type u#b)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:a -> req_t s)
      (#ens_g:a -> ens_t s b)
      (f:pnst a req_f ens_f)
      (g:(x:a -> Dv (pnst b (req_g x) (ens_g x))))
: pnst b
  (fun s0 -> req_f s0 /\ (forall x s1. ens_f s0 x s1 ==> (req_g x) s1))
  (fun s0 r s2 -> req_f s0 /\ (exists x s1. ens_f s0 x s1 /\ (req_g x) s1 /\ (ens_g x) s1 r s2))

val weaken
      (#s:Type u#s)
      (#a:Type u#a)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:req_t s)
      (#ens_g:ens_t s a)
      (f:pnst a req_f ens_f)
    : Pure (pnst a req_g ens_g)
      (requires
        (forall s. req_g s ==> req_f s) /\
        (forall s0 x s1. (req_g s0 /\ ens_f s0 x s1) ==> ens_g s0 x s1))
      (ensures fun _ -> True)