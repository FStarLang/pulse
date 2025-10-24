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

module GR = Pulse.Lib.GhostReference

noeq
type cinv = {
  i:iname;
  r:GR.ref bool;
}

instance non_informative_cinv = {
  reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer cinv;
}

let placeless_tag p (inst: placeless p) = emp
let somewhere v = exists* l inst. placeless_tag v inst ** on l v

ghost fn somewhere_intro v {| inst: placeless v |}
  requires v
  ensures somewhere v
{
  loc_get ();
  on_intro v;
  fold placeless_tag v inst;
  fold somewhere v;
  drop_ (loc _);
}

ghost fn somewhere_elim v
  requires somewhere v
  returns inst: placeless v
  ensures v
{
  unfold somewhere v; with l inst. _;
  let inst = inst;
  loc_get (); with l0. assert loc l0;
  inst l l0;
  on_elim v;
  drop_ (loc l0);
  unfold placeless_tag v inst;
  inst
}

let cinv_vp_aux (r:GR.ref bool) (v:slprop) :slprop =
  exists* (b:bool). pts_to r #0.5R b **
                    somewhere (cond b v emp)

irreducible instance placeless_cond c a b {| da: placeless a, db: placeless b |} :
    placeless (cond c a b) =
  if c then da else db

let cinv_vp c v = cinv_vp_aux c.r v

let active c p = pts_to c.r #(p /. 2.0R) true

let placeless_active c p = Tactics.Typeclasses.solve

let active_timeless p c = ()

let iname_of c = c.i


ghost
fn new_cancellable_invariant (v:slprop) {| inst: placeless v |}
  requires v
  opens []
  returns c:cinv
  ensures inv (iname_of c) (cinv_vp c v) ** active c 1.0R
{
  let r = GR.alloc true;
  rewrite v as cond true v emp;
  somewhere_intro (cond true v emp) #_;
  GR.share r;
  fold (cinv_vp_aux r v);
  let i = new_invariant (cinv_vp_aux r v) #_;
  let c = {i;r};
  rewrite (inv i (cinv_vp_aux r v)) as (inv (iname_of c) (cinv_vp c v));
  with _p _v. rewrite (pts_to r #_p _v) as (active c 1.0R);
  c
}


let unpacked c v = exists* inst. pts_to c.r #0.5R true ** placeless_tag v inst

ghost
fn unpack_cinv_vp (#p:perm) (#v:slprop) (c:cinv)
  requires cinv_vp c v ** active c p
  ensures v ** unpacked c v ** active c p
  opens []
{
  unfold cinv_vp;
  unfold cinv_vp_aux;
  with b. assert somewhere (cond b v emp);
  let inst = somewhere_elim (cond b v emp);
  assert (pts_to c.r #0.5R b ** (cond b v emp));
  unfold active;
  GR.pts_to_injective_eq c.r;
  rewrite cond b v emp as v;
  fold (active c p);
  fold placeless_tag v inst;
  fold (unpacked c v)
}



ghost
fn pack_cinv_vp (#v:slprop) (c:cinv)
  requires v ** unpacked c v
  ensures cinv_vp c v
  opens []
{
  unfold unpacked;
  with inst. assert placeless_tag v inst; let inst = inst;
  drop_ (placeless_tag v inst);
  rewrite v as cond true v emp;
  somewhere_intro (cond true v emp) #_;
  fold (cinv_vp_aux c.r v);
  fold (cinv_vp c v)
}



ghost
fn share (#p:perm) (c:cinv)
  requires active c p
  ensures active c (p /. 2.0R) ** active c (p /. 2.0R)
  opens []
{
  unfold active;
  GR.share c.r;
  fold active;
  fold active
}



ghost
fn gather (#p1 #p2:perm) (c:cinv)
  requires active c p1 ** active c p2
  ensures active c (p1 +. p2)
{
  unfold (active c p1);
  unfold (active c p2);
  GR.gather c.r #_ #_ #(p1 /. 2.0R) #(p2 /. 2.0R);
  fold active c (p1 +. p2);
}



ghost
fn cancel_ (#v:slprop) (c:cinv)
  requires cinv_vp c v **
         active c 1.0R
  ensures cinv_vp c v ** v
  opens []
{
  unfold cinv_vp;
  unfold cinv_vp_aux;
  with b. assert somewhere (cond b v emp);
  let inst = somewhere_elim (cond b v emp);
  // with b. assert (pts_to c.r #0.5R b ** (if b then v else emp));
  unfold active;
  GR.pts_to_injective_eq c.r;
  rewrite cond b v emp as v;
  GR.gather c.r;
  GR.(c.r := false);
  GR.share c.r;
  rewrite emp as (cond false v emp);
  somewhere_intro (cond false v emp) #_;
  fold (cinv_vp_aux c.r v);
  fold (cinv_vp c v);
  drop_ (pts_to c.r #0.5R _)
}



ghost
fn cancel (#v:slprop) (c:cinv)
  requires inv (iname_of c) (cinv_vp c v) ** active c 1.0R
    ** later_credit 1 // Maybe we could hide the credit in active
  ensures v
  opens [iname_of c]
{
  with_invariants (iname_of c)
    returns _:unit
    ensures later (cinv_vp c v) ** v
    opens [iname_of c] {
    later_elim _;
    cancel_ c;
    later_intro (cinv_vp c v);
  };
  drop_ (inv (iname_of c) _)
}

