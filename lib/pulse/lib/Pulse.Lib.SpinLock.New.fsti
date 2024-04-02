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

module Pulse.Lib.SpinLock.New
open Pulse.Lib.Core
open PulseCore.FractionalPermission
module T = FStar.Tactics

val lock : Type u#0

val lock_alive
  (lk : lock)
  (#[T.exact (`full_perm)] f:perm)
  (p : vprop)
  : vprop

val lock_taken
  (lk : lock)
  (#[T.exact (`full_perm)] f:perm)
  (p : vprop)
  : vprop

val new_lock
        (p:vprop)
  : stt lock
        (requires p)
        (ensures fun lk -> lock_alive lk p)
        
val share (#p:vprop)
        (l:lock)
        (#f:perm)
  : stt_ghost unit
            (requires lock_alive l #f p)
            (ensures fun _ -> lock_alive l #(half_perm f) p ** lock_alive l #(half_perm f) p)

(* Maybe this could be heterogenous in the vprops and provide an equality?
Is that useful? *)
val gather (#p:vprop)
        (l:lock)
        (#f1 #f2:perm)
  : stt_ghost unit
            (requires lock_alive l #f1 p ** lock_alive l #f2 p)
            (ensures fun _ -> lock_alive l #(sum_perm f1 f2) p)

val acquire
        (#p:vprop)
        (l:lock)
        (#f:perm)
  : stt unit 
        (requires lock_alive l #f p)
        (ensures  fun _ -> lock_taken l #f p ** p)

val release
        (#p:vprop)
        (l:lock)
        (#f:perm)
  : stt unit
        (requires lock_taken l #f p ** p)
        (ensures fun _ -> lock_alive l #f p)

val free_lock
        (#p:vprop)
        (l:lock)
  : stt unit
        (requires lock_alive l #full_perm p ** p)
        (ensures fun _ -> p)
