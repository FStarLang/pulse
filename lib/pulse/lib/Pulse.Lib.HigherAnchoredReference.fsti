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

[@@erasable]
val ref ([@@@unused]a:Type u#1) (p : preorder a) (anc : anchor_rel p)
: Type u#0

instance val ref_non_informative (a:Type u#1) (p : preorder a) (anc : anchor_rel p)
: NonInformative.non_informative (ref a p anc)

val owns 
  (#a:Type) (#p:_) (#anc:_)
  (r:ref a p anc)
  (#[T.exact (`full_perm)] f:perm)
  (n:a)
  (with_anchor:bool)
: vprop

val anchored
  (#[@@@equate_by_smt]a:Type)
  (#[@@@equate_by_smt]p:_)
  (#[@@@equate_by_smt]anc:_)
  ([@@@equate_by_smt] r:ref a p anc)
  ([@@@equate_by_smt] n:a) 
: v:vprop{is_small v}

val snapshot (#a:Type) (#p:_) (#anc:_) (r : ref a p anc) (v:a)
: v:vprop{is_small v}

let pts_to_full
  (#a:Type) (#p:_) (#anc:_)
  (r:ref a p anc)
  (#[T.exact (`full_perm)] f:perm)
  (n:a)
: vprop
= owns r #f n true

let pts_to
  (#a:Type) (#p:_) (#anc:_)
  (r:ref a p anc)
  (#[T.exact (`full_perm)] f:perm)
  (n:a)
: vprop
= owns r #f n false

val is_small_pts_to
  (#a:Type) (#p:_) (#anc:_)
  (r:ref a p anc)
  (#p:perm)
  (n:a)
  (with_anchor:bool)
: Lemma (is_small (owns r #p n with_anchor))
        [SMTPat (owns r #p n with_anchor)]


val alloc (#a:Type) (x:a) (#p:_) (#anc:anchor_rel p)
: stt_ghost (ref a p anc)
    (pure (anc x x))
    (fun r -> pts_to_full r x)

val read (#a:Type) (#p:_) (#anc:_) (#b:_) (r:ref a p anc) (#f:perm) (#v:erased a)
: stt_ghost (w:a{p v w})
    (owns r #f v b)
    (fun w -> owns r #f w b)

val read' (#a:Type) (#p:_) (#anc:_) (#b:_) (r:ref a p anc) (#f:perm) (#v:erased a)
: stt_ghost (erased (w:a{p v w}))
    (owns r #f v b)
    (fun w -> owns r #f w b)

val write (#a:Type) (#p:_) (#anc:_) (#b:_) (r:ref a p anc) (#v:erased a) (w : erased a)
: stt_ghost unit
    (owns r v b ** pure (p v w /\ (forall anchor. anc anchor v ==> anc anchor w)))
    (fun _ -> owns r w b)

val write_full (#a:Type) (#p:_) (#anc:_) (r:ref a p anc) (#v:erased a) (w : erased a)
: stt_ghost unit
    (pts_to_full r v ** pure (p v w /\ True))
    (fun _ -> pts_to_full r w)

val drop_anchor (#a:Type) (#p:_) (#anc:_) (#f:_) (r : ref a p anc) (#v:a)
: stt_ghost unit
    (owns r #f v true)
    (fun _ -> owns r #f v false ** anchored r v)

val share (#a:Type) (#p:_) (#anc:_) (#f #g:_) (r : ref a p anc) (#v:a)
: stt_ghost unit
    (pts_to r #(sum_perm f g) v)
    (fun _ -> pts_to r #f v ** pts_to r #g v)

val gather (#a:Type) (#p:_) (#anc:_) (#f #g:_) (r : ref a p anc) (#v #u:a)
: stt_ghost unit
    (pts_to r #f v ** pts_to r #g u)
    (fun _ -> pts_to r #(sum_perm f g) v ** pure (v == u))

val lift_anchor (#a:Type) (#p:_) (#anc:_) (r : ref a p anc) (#v:a) (va:a)
: stt_ghost unit
    (pts_to r v ** anchored r va)
    (fun _ -> pts_to_full r v ** pure (anc va v /\ True))

val recall_anchor (#a:Type) (#p:_) (#anc:_) (r : ref a p anc) (#v:a) (va:a) (#f:perm)
: stt_ghost unit
    (pts_to r #f v ** anchored r va)
    (fun _ -> pts_to r #f v ** anchored r va ** pure (anc va v))

val take_snapshot (#a:Type) (#p:_) (#f:perm) (#b:_) (#anc:anchor_rel p) (r : ref a p anc) (#v:a)
: stt_ghost unit
    (owns r #f v b)
    (fun _ -> owns r #f v b ** snapshot r v)

val recall_snapshot (#a:Type) (#p:_) (#f:perm) (#b:_) (#anc:anchor_rel p)
      (r : ref a p anc) (#v0 #v:a)
: stt_ghost unit
    (owns r #f v b ** snapshot r v0)
    (fun _ -> owns r #f v b ** snapshot r v0 ** pure (p v0 v /\ True))
