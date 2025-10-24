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

module Pulse.Lib.SpinLock
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.CancellableInvariant

module U32 = FStar.UInt32
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module CInv = Pulse.Lib.CancellableInvariant
  
instance assume_box_is_atomic (r: B.box U32.t) i :
    is_sync (pts_to r #1.0R i) =
  admit ()

let lock_inv_aux l' (r:B.box U32.t) (gr:GR.ref U32.t) (v:slprop) : slprop  =
  exists* i p. pts_to r #1.0R i **
               pts_to gr #p i **
               on (process_of l') (if i = 0ul then v else emp) **
               pure ((i == 0ul ==> p == 1.0R) /\
                     (i =!= 0ul ==> p == 0.5R)) 

let is_send_if (i: U32.t) (v: slprop) (inst: is_send v) : is_send (if i = 0ul then v else emp) =
  if i = 0ul then inst else is_send_placeless emp #placeless_emp

instance is_sync_lock_inv_aux l' r gr v : is_sync (lock_inv_aux l' r gr v) =
  Tactics.Typeclasses.solve

let lock_inv l' (r:B.box U32.t) (gr:GR.ref U32.t) (v:slprop) : slprop =
  on l' <| lock_inv_aux l' r gr v

[@@CAbstractStruct]
noeq
type lock = {
  r : B.box U32.t;
  gr : GR.ref U32.t;
  i : cinv;
}

let is_send_tag v (inst: is_send v) = emp

let lock_alive l #p v =
  exists* l' inst. in_same_process l' ** is_send_tag v inst **
  inv (iname_of l.i) (cinv_vp l.i (lock_inv l' l.r l.gr v)) ** active l.i p

instance is_sync_lock_alive = Tactics.Typeclasses.solve

let lock_acquired l = pts_to l.gr #0.5R 1ul


fn new_lock (v:slprop) {| inst: is_send v |}
  requires v
  returns l:lock
  ensures lock_alive l v
{
  let gr = GR.alloc 0ul;
  rewrite v as (if 0ul = 0ul then v else emp);
  loc_get (); with l'. assert loc l';
  let r = B.alloc 0ul;
  unsafe_attest_released v #_ #l';
  fold (lock_inv_aux l' r gr v);
  on_intro (lock_inv_aux l' r gr v);
  fold (lock_inv l' r gr v);
  let i = new_cancellable_invariant (lock_inv l' r gr v) #_;
  let l = { r; gr; i };
  rewrite each r as l.r;
  rewrite each gr as l.gr;
  rewrite each i as l.i;
  fold in_same_process l';
  fold is_send_tag v inst;
  fold (lock_alive l #1.0R v);
  l
}

fn rec acquire (#v:slprop) (#p:perm) (l:lock)
  preserves lock_alive l #p v
  ensures v ** lock_acquired l
{
  unfold (lock_alive l #p v);
  later_credit_buy 1;
  with l'. assert in_same_process l';
  unfold in_same_process l'; with l0. assert loc l0; loc_dup l0; fold in_same_process l';
  with inst. assert is_send_tag v inst;
  let b =
    with_invariants (CInv.iname_of l.i)
      returns b:bool
      ensures later (cinv_vp l.i (lock_inv l' l.r l.gr v)) **
              active l.i p **
              in_same_process l' ** loc l0 ** is_send_tag v inst **
              (if b then v ** pts_to l.gr #0.5R 1ul else emp) {
      later_elim _;
      unpack_cinv_vp l.i;
      unfold lock_inv;
      is_sync_elim_on (lock_inv_aux l' l.r l.gr v) #_;
      unfold lock_inv_aux;
      with i. assert (pts_to l.r i);
      let b = cas_box l.r 0ul 1ul;
      if b {
        unsafe_attest_acquired (if i = 0ul then v else emp) #(is_send_if i v inst) #l0;
        elim_cond_true _ _ _;
        rewrite each i as 0ul;
        GR.(l.gr := 1ul);
        GR.share l.gr;
        on_intro emp; placeless_emp _ (process_of l');
        fold (lock_inv_aux l' l.r l.gr v);
        is_sync_intro_on (lock_inv_aux l' l.r l.gr v) _;
        fold (lock_inv l' l.r l.gr v);
        pack_cinv_vp l.i;
        assert (cinv_vp l.i (lock_inv l' l.r l.gr v) **
                active l.i p **
                pts_to l.gr #0.5R 1ul **
                v);
        let b = true;
        rewrite (v ** pts_to l.gr #0.5R 1ul)
             as (if b then v ** pts_to l.gr #0.5R 1ul else emp);
        later_intro (CInv.cinv_vp l.i (lock_inv l' l.r l.gr v));
        b
      } else {
        elim_cond_false _ _ _;
        fold (lock_inv_aux l' l.r l.gr v);
        is_sync_intro_on (lock_inv_aux l' l.r l.gr v) _;
        fold (lock_inv l' l.r l.gr v);
        pack_cinv_vp l.i;
        assert (cinv_vp l.i (lock_inv l' l.r l.gr v) **
                active l.i p);
        let b = false;
        rewrite emp as
                (if b then v ** pts_to l.gr #0.5R 1ul else emp);
        later_intro (CInv.cinv_vp l.i (lock_inv l' l.r l.gr v));
        b
      }
    };

  drop_ (loc l0);
  if b {
    fold (lock_alive l #p v);
    fold (lock_acquired l)
  } else {
    fold (lock_alive l #p v);
    acquire l
  }
}



fn release (#v:slprop) (#p:perm) (l:lock)
  preserves lock_alive l #p v
  requires lock_acquired l ** v
{
  unfold (lock_alive l #p v);
  unfold (lock_acquired l);
  with l'. assert in_same_process l';
  with inst. assert is_send_tag v inst;

  later_credit_buy 1;
  with_invariants (CInv.iname_of l.i)
    returns _:unit
    ensures later (cinv_vp l.i (lock_inv l' l.r l.gr v)) **
            in_same_process l' ** is_send_tag v inst **
            active l.i p {
    unfold in_same_process l'; with l0. assert loc l0; loc_dup l0; fold in_same_process l';
    later_elim _;
    unpack_cinv_vp l.i;
    unfold (lock_inv l' l.r l.gr v);
    is_sync_elim_on (lock_inv_aux l' l.r l.gr v) #_;
    unfold (lock_inv_aux l' l.r l.gr v);
    GR.pts_to_injective_eq l.gr;
    GR.gather l.gr;
    with i. assert (pts_to l.gr i);
    rewrite on (process_of l') (if (i = 0ul) then v else emp) as on (process_of l') emp;
    placeless_emp (process_of l') l0; on_elim emp;
    GR.(l.gr := 0ul);
    write_atomic_box l.r 0ul;
    unsafe_attest_released v #inst #l0;
    fold (lock_inv_aux l' l.r l.gr v);
    is_sync_intro_on (lock_inv_aux l' l.r l.gr v) _;
    fold (lock_inv l' l.r l.gr v);
    pack_cinv_vp l.i;
    later_intro (cinv_vp l.i (lock_inv l' l.r l.gr v));
    drop_ (loc l0);
  };

  fold (lock_alive l #p v)
}



ghost
fn share (#v:slprop) (#p:perm) (l:lock)
  requires lock_alive l #p v
  ensures lock_alive l #(p /. 2.0R) v ** lock_alive l #(p /. 2.0R) v
{
  unfold (lock_alive l #p v);
  with l'. assert in_same_process l';
  with inst. assert is_send_tag v inst;
  CInv.share l.i;
  dup (in_same_process l') ();
  fold is_send_tag v inst;
  dup_inv (CInv.iname_of l.i) (cinv_vp l.i (lock_inv l' l.r l.gr v));  // make this arg implicit
  fold (lock_alive l #(p /. 2.0R) v);
  fold (lock_alive l #(p /. 2.0R) v)
} 



ghost
fn gather (#v:slprop) (#p1 #p2 :perm) (l:lock)
  requires lock_alive l #p1 v ** lock_alive l #p2 v
  ensures lock_alive l #(p1 +. p2) v
{
  unfold (lock_alive l #p1 v);
  drop_ (in_same_process _ ** is_send_tag v _ ** inv (iname_of l.i) _);
  unfold (lock_alive l #p2 v);
  CInv.gather #p1 #p2 l.i;
  fold (lock_alive l #(p1 +. p2) v);
} 


fn free (#v:slprop) (l:lock)
  requires lock_alive l #1.0R v
  requires lock_acquired l
{
  unfold (lock_alive l #1.0R v);
  with l'. assert in_same_process l';
  with inst. assert is_send_tag v inst;
  unfold (lock_acquired l);
  later_credit_buy 1;
  cancel l.i;
  unfold (lock_inv l' l.r l.gr v);
  is_sync_elim_on (lock_inv_aux l' l.r l.gr v) #_;
  unfold (lock_inv_aux l' l.r l.gr v); with i. _;
  B.free l.r;
  GR.gather l.gr;
  GR.free l.gr;
  rewrite on (process_of l') (if (i = 0ul) then v else emp) as on (process_of l') emp;
  drop_ (on (process_of l') emp);
  drop_ (in_same_process l' ** is_send_tag v inst);
  ()
}



ghost
fn lock_alive_inj
  (l:lock) (#p1 #p2 :perm) (#v1 #v2 :slprop)
  requires lock_alive l #p1 v1 ** lock_alive l #p2 v2
  ensures  lock_alive l #p1 v1 ** lock_alive l #p2 v1
{
  unfold (lock_alive l #p2 v2);
  drop_ (inv _ _);
  drop_ (is_send_tag v2 _);
  drop_ (in_same_process _);
  unfold (lock_alive l #p1 v1);
  with inst. assert is_send_tag v1 inst;
  with l1. assert in_same_process l1;
  dup_inv (CInv.iname_of l.i) (CInv.cinv_vp l.i (lock_inv _ l.r l.gr v1));
  dup (is_send_tag v1 inst) ();
  dup (in_same_process l1) ();
  fold (lock_alive l #p1 v1);
  fold (lock_alive l #p2 v1);
  // TODO: we could also prove from, but that requires a significant amount of congruence lemmas about equiv
  // invariant_name_identifies_invariant (CInv.iname_of l.i) (CInv.iname_of l.i);
}
