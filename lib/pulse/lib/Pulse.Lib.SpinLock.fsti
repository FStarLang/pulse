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

open Pulse.Lib.Pervasives
open Pulse.Lib.Stick
open Pulse.Class.Duplicable

module T = FStar.Tactics.V2

val lock : Type0

val lock_alive
      ([@@@equate_strict] l:lock)
      (#[T.exact (`1.0R)] p:perm)
      (v:vprop)
  : vprop

(* Like lock_alive, but only relates the lock to the vprop, without
claiming any permission on it. This is freely duplicable. The lock
can even be deallocated while holding this. Internally, it just
stores the relation between the lock's invariant and v. *)
val lock_alive0 (l:lock) (v:vprop) : vprop

instance val dup_lock_alive0 (l : lock) (v : vprop)
  : duplicable (lock_alive0 l v)

val lock_acquired (l:lock) : vprop

val new_lock (v:vprop { is_big v })
  : stt lock v (fun l -> lock_alive l v)

val acquire (#v:vprop) (#p:perm) (l:lock)
  : stt unit (lock_alive l #p v) (fun _ -> v ** lock_alive l #p v ** lock_acquired l)

val release (#v:vprop) (#p:perm) (l:lock)
  : stt unit (lock_alive l #p v ** lock_acquired l ** v) (fun _ -> lock_alive l #p v)

val share (#v:vprop) (#p:perm) (l:lock)
  : stt_ghost unit emp_inames
      (lock_alive l #p v)
      (fun _ -> lock_alive l #(p /. 2.0R) v ** lock_alive l #(p /. 2.0R) v)

val share2 (#v:vprop) (l:lock)
  : stt_ghost unit emp_inames
      (lock_alive l v)
      (fun _ -> lock_alive l #0.5R v ** lock_alive l #0.5R v)

[@@allow_ambiguous]
val gather (#v:vprop) (#p1 #p2:perm) (l:lock)
  : stt_ghost unit emp_inames
      (lock_alive l #p1 v ** lock_alive l #p2 v)
      (fun _ -> lock_alive l #(p1 +. p2) v)

[@@allow_ambiguous]
val gather2 (#v:vprop) (l:lock)
  : stt_ghost unit emp_inames
      (lock_alive l #0.5R v ** lock_alive l #0.5R v)
      (fun _ -> lock_alive l v)

val free (#v:vprop) (l:lock)
  : stt unit (lock_alive l #1.0R v ** lock_acquired l) (fun _ -> emp)

(* A given lock is associated to a single vprop, roughly.
I'm not sure if we can prove v1 == v2 here. *)
val lock_alive_inj (l:lock) (#p1 #p2 : perm) (#v1 #v2 : vprop)
  : stt_ghost unit emp_inames
              (lock_alive l #p1 v1 ** lock_alive l #p2 v2)
              (fun _ -> lock_alive l #p1 v1 ** lock_alive l #p2 v1)

val iref_of (l:lock) : iref
val iref_v_of (l:lock) (v:vprop) : vprop
val lock_active (#[T.exact (`1.0R)] p:perm) (l:lock) : v:vprop { is_small v }

val share_lock_active (#p:perm) (l:lock)
  : stt_ghost unit emp_inames
      (requires lock_active #p l)
      (ensures fun _ -> lock_active #(p /. 2.0R) l ** lock_active #(p /. 2.0R) l)

val gather_lock_active (#p1 #p2:perm) (l:lock)
  : stt_ghost unit emp_inames
      (requires lock_active #p1 l ** lock_active #p2 l)
      (ensures fun _ -> lock_active #(p1 +. p2) l)

val elim_inv_and_active_into_alive (l:lock) (v:vprop) (#p:perm)
  : stt_ghost unit emp_inames
      (requires emp)
      (ensures fun _ -> (inv (iref_of l) (iref_v_of l v) ** lock_active #p l) @==> lock_alive l #p v)

val elim_alive_into_inv_and_active (l:lock) (v:vprop) (#p:perm)
  : stt_ghost unit emp_inames
      (requires emp)
      (ensures fun _ -> lock_alive l #p v @==> (inv (iref_of l) (iref_v_of l v) ** lock_active #p l))

val lock_alive0_inj_l (l:lock) (#p1 : perm) (#v1 #v2 : vprop)
  : stt_ghost unit emp_inames
              (lock_alive l #p1 v1 ** lock_alive0 l v2)
              (fun _ -> lock_alive l #p1 v1 ** lock_alive0 l v1)

val lock_alive0_inj_r (l:lock) (#p1 : perm) (#v1 #v2 : vprop)
  : stt_ghost unit emp_inames
              (lock_alive l #p1 v1 ** lock_alive0 l v2)
              (fun _ -> lock_alive l #p1 v2 ** lock_alive0 l v2)

val lock_alive0_inj_both (l:lock) (#v1 #v2 : vprop)
  : stt_ghost unit emp_inames
              (lock_alive0 l v1 ** lock_alive0 l v2)
              (fun _ -> lock_alive0 l v2 ** lock_alive0 l v2)

val get_lock_alive0 (l:lock) (#p:perm) (#v:vprop)
  : stt_ghost unit emp_inames
              (lock_alive l #p v)
              (fun _ -> lock_alive l #p v ** lock_alive0 l v)
