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

module Pulse.Lib.HigherAnchoredReference

open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
open FStar.Preorder
open Pulse.Lib.FractionalAnchoredPreorder

module U32 = FStar.UInt32
module T = FStar.Tactics

val ref ([@@@unused]a:Type u#1) (p : preorder a) (anc : anchor_rel p) : Type u#0

val pts_to_anchored
  (#a:Type) (#p:_) (#anc:_)
  (r:ref a p anc)
  (#[T.exact (`full_perm)] p:perm)
  (n:a) : vprop

val pts_to
  (#a:Type) (#p:_) (#anc:_)
  (r:ref a p anc)
  (#[T.exact (`full_perm)] p:perm)
  (n:a) : vprop

val anchored
  (#a:Type) (#p:_) (#anc:_)
  (r:ref a p anc)
  (n:a) : vprop

val alloc (#a:Type) (x:a) (#p:_) (#anc:anchor_rel p)
  : stt_ghost (ref a p anc) (pure (anc x x)) (fun r -> pts_to_anchored r x)

val read (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#f:perm) (#v:erased a)
  : stt_ghost (w:a{p v w})
        (pts_to r #f v)
        (fun w -> pts_to r #f w)

val write (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#f:perm) (#v:erased a) (w : erased a)
  : stt_ghost unit
        (pts_to r #f v ** pure (p v w /\ (forall anchor. anc anchor v -> anc anchor w)))
        (fun _ -> pts_to r #f w)
