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

module Pulse.Lib.CancellableInvariant
#lang-pulse

open Pulse.Lib.Pervasives

[@@ erasable]
val cinv : Type0

instance val non_informative_cinv
  : NonInformative.non_informative cinv

val cinv_vp ([@@@mkey] c:cinv) (v:slprop) : slprop

val active ([@@@mkey] c:cinv) (p:perm) : slprop

val active_timeless (c:cinv) (p:perm)
  : Lemma (timeless (active c p))
          [SMTPat (timeless (active c p))]

val iname_of (c:cinv) : GTot iname

ghost
fn new_cancellable_invariant (v:slprop)
  requires v
  returns  c : cinv
  ensures  inv (iname_of c) (cinv_vp c v) ** active c 1.0R

val unpacked (c:cinv) (v:slprop) : slprop

ghost
fn unpack_cinv_vp (#p:perm) (#v:slprop) (c:cinv)
  requires cinv_vp c v ** active c p
  ensures  v ** unpacked c v ** active c p

ghost
fn pack_cinv_vp (#v:slprop) (c:cinv)
  requires v ** unpacked c v
  ensures  cinv_vp c v

ghost
fn share (#p:perm) (c:cinv)
  requires active c p
  ensures  active c (p /. 2.0R) ** active c (p /. 2.0R)

[@@allow_ambiguous]
ghost
fn gather (#p1 #p2 :perm) (c:cinv)
  requires active c p1 ** active c p2
  ensures  active c (p1 +. p2)

ghost
fn cancel (#v:slprop) (c:cinv)
  requires inv (iname_of c) (cinv_vp c v) ** active c 1.0R ** later_credit 1
  opens add_inv emp_inames (iname_of c)
  ensures v
