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

module Pulse.Lib.HigherReference
#lang-pulse
open Pulse.Lib.Core
open Pulse.Main
open FStar.PCM
open Pulse.Lib.PCM.Fraction

let ref (a:Type u#1) = pcm_ref (pcm_frac #a)

let null (#a:Type u#1) : ref a = null_core_pcm_ref

let is_null #a (r : ref a)
  : b:bool{b <==> r == null #a}
= is_null_core_pcm_ref r

let pts_to (#a:Type) (r:ref a) (#[T.exact (`1.0R)] p:perm) (n:a)
= pcm_pts_to r (Some (n, p)) ** pure (perm_ok p)
let pts_to_timeless _ _ _ = ()

fn alloc' (#a:Type u#1) (x:a)
  requires emp
  returns r:ref a
  ensures pts_to r x
{
  full_values_compatible x;
  let r = Pulse.Lib.Core.alloc #_ #(pcm_frac #a) (Some (x, 1.0R));
  fold (pts_to r #1.0R x);
  r
}

let alloc = alloc'

let read_compat (#a:Type u#1) (x:fractional a)
                (v:fractional a { compatible pcm_frac x v })
  : GTot (y:fractional a { compatible pcm_frac y v /\
                           FStar.PCM.frame_compatible pcm_frac x v y })
  = x


fn read (#a:Type u#1) (r:ref a) (#n:erased a) (#p:perm)
  preserves r |-> Frac p n
  returns  x : a
  ensures  rewrites_to x n
{
  unfold pts_to r #p n;
  with w. assert (pcm_pts_to r w);
  let x = Pulse.Lib.Core.read r w (fun _ -> w);
  assert pure (compatible pcm_frac w x);
  assert (pcm_pts_to r w);
  fold (pts_to r #p n);
  fst (Some?.v x)
}

let ( ! ) #a = read #a

fn write (#a:Type u#1) (r:ref a) (x:a) (#n:erased a)
  requires r |-> n
  ensures  r |-> x
{
  unfold pts_to r #1.0R n;
  with w. assert (pcm_pts_to r w);
  Pulse.Lib.Core.write r _ _ (mk_frame_preserving_upd n x);
  fold pts_to r #1.0R x;
}

let ( := ) #a = write #a


fn free #a (r:ref a) (#n:erased a)
  requires pts_to r #1.0R n
  ensures emp
{
  unfold pts_to r #1.0R n;
  with w. assert (pcm_pts_to r w);
  Pulse.Lib.Core.write r _ _ (mk_frame_preserving_upd_none n);
  Pulse.Lib.Core.drop_ _;
}

ghost
fn share #a (r:ref a) (#v:erased a) (#p:perm)
  requires pts_to r #p v
  ensures pts_to r #(p /. 2.0R) v ** pts_to r #(p /. 2.0R) v
{
  unfold pts_to r #p v;
  rewrite pcm_pts_to r (Some (reveal v, p))
      as  pcm_pts_to r (Some (reveal v, p /. 2.0R) `op pcm_frac` Some(reveal v, p /. 2.0R));
  Pulse.Lib.Core.share r (Some (reveal v, p /. 2.0R)) _; //writing an underscore for the first arg also causes a crash
  fold (pts_to r #(p /. 2.0R) v);
  fold (pts_to r #(p /. 2.0R) v);
}

ghost
fn gather #a (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  requires pts_to r #p0 x0 ** pts_to r #p1 x1
  ensures pts_to r #(p0 +. p1) x0 ** pure (x0 == x1)
{ 
  unfold pts_to r #p0 x0;
  unfold pts_to r #p1 x1;
  Pulse.Lib.Core.gather r (Some (reveal x0, p0)) (Some (reveal x1, p1));
  fold (pts_to r #(p0 +. p1) x0)
}

fn free_with_frame #a (r:ref a) (frame:slprop)
  requires frame ** (exists* (x:a). pts_to r x)
  ensures frame
{
  free r;
}


(* this is universe-polymorphic in ret_t; so can't define it in Pulse yet *)
let with_local
    (#a:Type u#1)
    (init:a)
    (#pre:slprop)
    (#ret_t:Type u#a)
    (#post:ret_t -> slprop) 
    (body: (r:ref a -> stt ret_t (pre ** pts_to r init) (fun v -> post v ** (exists* (x:a). pts_to r x))))
= let m1
    : stt (ref a) (emp ** pre) (fun r -> pts_to r init ** pre)
    = frame_stt pre (alloc init)
  in
  let pf_post : slprop_post_equiv (fun r -> pts_to r init ** pre) (fun r -> pre ** pts_to r init)
    = intro_slprop_post_equiv _ _ (fun r -> slprop_equiv_comm (pts_to r #1.0R init) pre)
  in
  let m1 
    : stt (ref a) pre (fun r -> pre ** pts_to r init)
    = sub_stt _ _ (slprop_equiv_unit pre) pf_post m1
  in
  let body (r:ref a)
    : stt ret_t (pre ** pts_to r init) post
    = bind_stt (body r) (fun v -> bind_stt (free_with_frame #a r (post v)) (fun _ -> return_stt_noeq v post))
  in
  bind_stt m1 body
  

ghost
fn pts_to_injective_eq
    (#a:Type)
    (#p0 #p1:perm)
    (#v0 #v1:a)
    (r:ref a)
  requires pts_to r #p0 v0 ** pts_to r #p1 v1
  ensures pts_to r #p0 v0 ** pts_to r #p1 v1 ** pure (v0 == v1)
{
  unfold pts_to r #p0 v0;
  unfold pts_to r #p1 v1;
  Pulse.Lib.Core.gather r (Some (v0, p0)) (Some (v1, p1));
  Pulse.Lib.Core.share r (Some (v0, p0)) (Some (v1, p1));
  fold pts_to r #p0 v0;
  fold pts_to r #p1 v1;
}


ghost
fn pts_to_perm_bound (#a:_) (#p:_) (r:ref a) (#v:a)
  requires pts_to r #p v
  ensures pts_to r #p v ** pure (p <=. 1.0R)
{
  unfold pts_to r #p v;
  fold pts_to r #p v;
}

ghost
fn pts_to_not_null (#a:_) (#p:_) (r:ref a) (#v:a)
  preserves r |-> Frac p v
  ensures  pure (not (is_null #a r))
{
  unfold pts_to r #p v;
  pts_to_not_null r _;
  fold pts_to r #p v;
}
