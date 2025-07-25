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

module Pulse.Lib.GhostReference
#lang-pulse
open Pulse.Lib.Core
open Pulse.Main
module H = Pulse.Lib.HigherGhostReference
module U = Pulse.Lib.Raise
let ref a = H.ref (U.raise_t a)

instance non_informative_gref (a:Type0) : NonInformative.non_informative (ref a) = {
  reveal = (fun x -> Ghost.reveal x) <: NonInformative.revealer (ref a);
}

let pts_to
    (#a:Type u#0)
    ([@@@mkey] r:ref a)
    (#[exact (`1.0R)] p:perm)
    (v:a)
  = H.pts_to r #p (U.raise_val v)

let pts_to_timeless r p x = H.pts_to_timeless r p (U.raise_val x)


ghost
fn alloc (#a:Type u#0) (v:a)
  requires emp
  returns r:ref a
  ensures pts_to r v
{
  let r = H.alloc (U.raise_val v);
  fold (pts_to r #1.0R v);
  r
}



ghost
fn read (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  preserves pts_to r #p n
  returns x:erased a
  ensures rewrites_to x n
{
  unfold (pts_to r #p n);
  let k = H.( !r );
  fold (pts_to r #p n);
  hide (U.downgrade_val (reveal k))
}

let ( ! ) #a = read #a

ghost
fn write (#a:Type) (r:ref a) (x:erased a) (#n:erased a)
  requires pts_to r #1.0R n
  ensures pts_to r #1.0R x
{
  unfold (pts_to r #1.0R n);
  H.(r := (U.raise_val x));
  fold (pts_to r #1.0R x)
}

let ( := ) = write

ghost
fn free #a (r:ref a) (#n:erased a)
  requires pts_to r #1.0R n
  ensures emp
{
  unfold (pts_to r #1.0R n);
  H.free r;
}



ghost
fn share (#a:Type) (r:ref a) (#v:erased a) (#p:perm)
  requires pts_to r #p v
  ensures pts_to r #(p /. 2.0R) v ** pts_to r #(p /. 2.0R) v
{
  unfold pts_to r #p v;
  H.share r;
  fold pts_to r #(p /. 2.0R) v;
  fold pts_to r #(p /. 2.0R) v
}



ghost
fn raise_inj (a:Type u#0) (x0 x1:a)
  requires pure (U.raise_val u#0 u#1 x0 == U.raise_val u#0 u#1 x1)
  ensures pure (x0 == x1)
{
  assert pure (U.downgrade_val (U.raise_val u#0 u#1 x0) == x0);
  assert pure (U.downgrade_val (U.raise_val u#0 u#1 x1) == x1);
}



ghost
fn gather (#a:Type) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  requires pts_to r #p0 x0 ** pts_to r #p1 x1
  ensures pts_to r #(p0 +. p1) x0 ** pure (x0 == x1)
{
  unfold pts_to r #p0 x0;
  unfold pts_to r #p1 x1;
  H.gather r;
  fold (pts_to r #(p1 +. p0) x0);
  raise_inj a x0 x1;
}




ghost
fn pts_to_injective_eq
  (#a:Type0)
  (#p #q:perm)
  (#v0 #v1:a)
  (r:ref a)
requires
  pts_to r #p v0 ** pts_to r #q v1
ensures
  pts_to r #p v0 ** pts_to r #q v1 ** pure (v0 == v1)
{
  unfold pts_to r #p v0;
  unfold pts_to r #q v1;
  H.pts_to_injective_eq r;
  fold pts_to r #p v0;
  fold pts_to r #q v1;
  raise_inj _ v0 v1;
}



ghost
fn pts_to_perm_bound (#a:_) (#p:_) (r:ref a) (#v:a)
  requires pts_to r #p v
  ensures pts_to r #p v ** pure (p <=. 1.0R)
{
  unfold pts_to r #p v;
  H.pts_to_perm_bound r;
  fold pts_to r #p v;
}

