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

module Pulse.Lib.AnchoredReference

open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
open FStar.Preorder
open Pulse.Lib.FractionalAnchoredPreorder
open Pulse.Class.Duplicable

module U32 = FStar.UInt32
module T = FStar.Tactics

[@@erasable]
val ref ([@@@unused]a:Type u#0) (p : preorder a) (anc : anchor_rel p) : Type u#0

instance val ref_non_informative (a:Type0) (p : preorder a) (anc : anchor_rel p)
  : NonInformative.non_informative (ref a p anc)

val pts_to_full
  (#a:Type) (#p:_) (#anc:_)
  (r:ref a p anc)
  (#[T.exact (`1.0R)] p:perm)
  (n:a) : vprop

val pts_to
  (#a:Type) (#p:_) (#anc:_)
  (r:ref a p anc)
  (#[T.exact (`1.0R)] p:perm)
  (n:a) : vprop

val is_small_pts_to
  (#a:Type) (#p:_) (#anc:_)
  (r:ref a p anc)
  (#p:perm)
  (n:a) :
  Lemma (is_small (pts_to r #p n))
        [SMTPat (pts_to r #p n)]

val anchored
  (#a:Type)
  (#p:_)
  (#anc:_)
  (r:ref a p anc)
  (n:a) : (v:vprop{is_small v})

val alloc (#a:Type) (x:a) (#p:_) (#anc:anchor_rel p)
  : stt_ghost (ref a p anc) emp_inames (pure (anc x x)) (fun r -> pts_to_full r x)

val read (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#f:perm) (#v:erased a)
  : stt_ghost (w:a{p v w})
        emp_inames
        (pts_to r #f v)
        (fun w -> pts_to r #f w)

val read' (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#f:perm) (#v:erased a)
  : stt_ghost (erased (w:a{p v w}))
        emp_inames
        (pts_to r #f v)
        (fun w -> pts_to r #f w)

val read_full' (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#f:perm) (#v:erased a)
  : stt_ghost (erased (w:a{p v w}))
        emp_inames
        (pts_to_full r #f v)
        (fun w -> pts_to_full r #f w)

val write (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#v:erased a) (w : erased a)
  : stt_ghost unit
        emp_inames
        (pts_to r v ** pure (p v w /\ (forall anchor. anc anchor v ==> anc anchor w)))
        (fun _ -> pts_to r w)

val write_full (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#v:erased a) (w : erased a)
  : stt_ghost unit
        emp_inames
        (pts_to_full r v ** pure (p v w /\ True))
        (fun _ -> pts_to_full r w)

val drop_anchor (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) (#v:a)
  : stt_ghost unit
        emp_inames
        (pts_to_full r v)
        (fun _ -> pts_to r v ** anchored r v)

val lift_anchor (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) (#v:a) (va:a)
  : stt_ghost unit
        emp_inames
        (pts_to r v ** anchored r va)
        (fun _ -> pts_to_full r v ** pure (anc va v /\ True))

val recall_anchor (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) (#v:a) (va:a) (#f:perm)
  : stt_ghost unit
        emp_inames
        (pts_to r #f v ** anchored r va)
        (fun _ -> pts_to r #f v ** anchored r va ** pure (anc va v))

val snapshot (#a:Type) (#p:_) (#anc:_) (r : ref a p anc) (v:a)
  : boxable

instance val dup_snapshot
  (#t:Type u#0)
  (#pre : preorder t)
  (#anc : anchor_rel pre)
  (r : ref t pre anc)
  (v : t)
: duplicable (snapshot r v)

val take_snapshot (#a:Type) (#p:_) (#f:perm) (#anc:anchor_rel p) (r : ref a p anc) (#v:a)
  : stt_ghost unit
        emp_inames
        (pts_to r #f v)
        (fun _ -> pts_to r #f v ** snapshot r v)

val take_snapshot' (#a:Type) (#p:_) (#f:perm) (#anc:anchor_rel p) (r : ref a p anc) (#v:a)
  : stt_ghost unit
        emp_inames
        (pts_to_full r #f v)
        (fun _ -> pts_to_full r #f v ** snapshot r v)

val recall_snapshot (#a:Type) (#p:_) (#anc:anchor_rel p) (r : ref a p anc) (#v0 #v:a)
  : stt_ghost unit
        emp_inames
        (pts_to r v ** snapshot r v0)
        (fun _ -> pts_to r v ** snapshot r v0 ** pure (p v0 v /\ True))
