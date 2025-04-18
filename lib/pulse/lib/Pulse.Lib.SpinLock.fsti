(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at


   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.SpinLock
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module T = FStar.Tactics.V2

val lock : Type0

val lock_alive
      ([@@@mkey] l:lock)
      (#[T.exact (`1.0R)] p:perm)
      (v:slprop)
  : slprop

val lock_acquired (l:lock) : slprop

val new_lock (v:slprop)
  : stt lock v (fun l -> lock_alive l v)

val acquire (#v:slprop) (#p:perm) (l:lock)
  : stt unit (lock_alive l #p v) (fun _ -> v ** lock_alive l #p v ** lock_acquired l)

val release (#v:slprop) (#p:perm) (l:lock)
  : stt unit (lock_alive l #p v ** lock_acquired l ** v) (fun _ -> lock_alive l #p v)

val share (#v:slprop) (#p:perm) (l:lock)
  : stt_ghost unit emp_inames
      (lock_alive l #p v)
      (fun _ -> lock_alive l #(p /. 2.0R) v ** lock_alive l #(p /. 2.0R) v)

[@@allow_ambiguous]
val gather (#v:slprop) (#p1 #p2:perm) (l:lock)
  : stt_ghost unit emp_inames
      (lock_alive l #p1 v ** lock_alive l #p2 v)
      (fun _ -> lock_alive l #(p1 +. p2) v)

val free (#v:slprop) (l:lock)
  : stt unit (lock_alive l #1.0R v ** lock_acquired l) (fun _ -> emp)

(* A given lock is associated to a single slprop, roughly.
I'm not sure if we can prove v1 == v2 here. *)
val lock_alive_inj (l:lock) (#p1 #p2 : perm) (#v1 #v2 : slprop)
  : stt_ghost unit emp_inames
              (lock_alive l #p1 v1 ** lock_alive l #p2 v2)
              (fun _ -> lock_alive l #p1 v1 ** lock_alive l #p2 v1)

val iname_of (l:lock) : iname
val iname_v_of (l:lock) (v:slprop) : slprop
val lock_active (#[T.exact (`1.0R)] p:perm) (l:lock) : v:slprop { timeless v }

val share_lock_active (#p:perm) (l:lock)
  : stt_ghost unit emp_inames
      (requires lock_active #p l)
      (ensures fun _ -> lock_active #(p /. 2.0R) l ** lock_active #(p /. 2.0R) l)

val gather_lock_active (#p1 #p2:perm) (l:lock)
  : stt_ghost unit emp_inames
      (requires lock_active #p1 l ** lock_active #p2 l)
      (ensures fun _ -> lock_active #(p1 +. p2) l)

val elim_inv_and_active_into_alive (l:lock) (v:slprop) (#p:perm)
  : stt_ghost unit emp_inames
      (requires emp)
      (ensures fun _ -> (inv (iname_of l) (iname_v_of l v) ** lock_active #p l) @==> lock_alive l #p v)

val elim_alive_into_inv_and_active (l:lock) (v:slprop) (#p:perm)
  : stt_ghost unit emp_inames
      (requires emp)
      (ensures fun _ -> lock_alive l #p v @==> (inv (iname_of l) (iname_v_of l v) ** lock_active #p l))
