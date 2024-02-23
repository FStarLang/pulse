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

module Pulse.Lib.GhostMonotonicReference

open Pulse.Lib.Core
open PulseCore.Observability
open PulseCore.FractionalPermission
open FStar.Ghost
open FStar.Preorder
module U32 = FStar.UInt32
module T = FStar.Tactics

// FIXME: should mark `a` unused
[@@erasable]
val ref (a:Type u#0) (p:preorder a): Type u#0

val ref_non_informative (a:Type0) (p:preorder a) : non_informative_witness (ref a p)

val pts_to (#a:Type) (#p:preorder a) (r:ref a p) (#[T.exact (`full_perm)] p:perm) (n:a) : vprop

val alloc (#a:Type) (#p:preorder a) (x:a)
  : stt_ghost (ref a p) emp (fun r -> pts_to r x)

val ( ! ) (#a:Type) (#p:preorder a) (r:ref a p) (#n:erased a) (#p:perm)
  : stt_ghost (erased a)
        (pts_to r #p n)
        (fun x -> pts_to r #p n ** pure (n == x))

val ( := ) (#a:Type) (#p:preorder a) (r:ref a p) (x:a) (#v:erased a) (_ : squash (p v x))
  : stt_ghost unit
        (pts_to r v)
        (fun _ -> pts_to r x)

val free (#a:Type) (#p:preorder a) (r:ref a p) (#n:erased a)
  : stt_ghost unit (pts_to r n) (fun _ -> emp)

(* The monotonic ops *)

(* Redefining from 'predicate' upwards since the definitions in
FStar.Preorder are in Type instead of prop. *)

let predicate (a:Type) = a -> prop

let stable (#a:Type) (p:preorder a) (f:predicate a) : prop
  = forall (x y : a). p x y ==> f x ==> f y

val witnessed (#a:Type) (#p:preorder a) (r:ref a p) (f : predicate a)
  : Type0

val witness (#a:_) (#p:_) (#f:perm) (r : ref a p)
    (fact : predicate a{stable p fact})
    (v : erased a{fact v})
    : stt_atomic (witnessed r fact)
                 #Unobservable
                 emp_inames
                 (pts_to r #f v)
                 (fun _ -> pts_to r #f v)
                
val recall (#a:_) (#p:_) (r : ref a p)
    (#f:perm)
    (fact : predicate a)
    (w : witnessed r fact)
    (v : erased a)
    : stt_atomic unit
                 #Unobservable
                 emp_inames
                 (pts_to r #f v)
                 (fun _ -> pts_to r #f v ** pure (fact v))

val share (#a:Type) (#p:preorder a) (r:ref a p) (#v:erased a) (#p:perm)
  : stt_ghost unit
      (pts_to r #p v)
      (fun _ ->
       pts_to r #(half_perm p) v **
       pts_to r #(half_perm p) v)

val gather (#a:Type) (#p:preorder a) (r:ref a p) (#x0 #x1:erased a) (#p0 #p1:perm)
  : stt_ghost unit
      (pts_to r #p0 x0 ** pts_to r #p1 x1)
      (fun _ -> pts_to r #(sum_perm p0 p1) x0 ** pure (x0 == x1))

(* Share/gather specialized to half permission *)
val share2 (#a:Type) (#p:preorder a) (r:ref a p) (#v:erased a)
  : stt_ghost unit
      (pts_to r v)
      (fun _ -> pts_to r #one_half v ** pts_to r #one_half v)

val gather2 (#a:Type) (#p:preorder a) (r:ref a p) (#x0 #x1:erased a)
  : stt_ghost unit
      (pts_to r #one_half x0 ** pts_to r #one_half x1)
      (fun _ -> pts_to r x0 ** pure (x0 == x1))

val with_local
  (#a:Type u#0)
  (#p:preorder a)
  (init:a)
  (#pre:vprop)
  (#ret_t:Type)
  (#post:ret_t -> vprop)
  (body:(r:ref a p) -> stt_ghost ret_t (pre ** pts_to r init)
                               (fun v -> post v ** (exists* (x:a). pts_to r x)))
  : stt_ghost ret_t pre post

val pts_to_injective_eq (#a:_)
                        (#pp:preorder a)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:ref a pp)
  : stt_ghost unit
      (pts_to r #p v0 ** pts_to r #q v1)
      (fun _ -> pts_to r #p v0 ** pts_to r #q v1 ** pure (v0 == v1))

val pts_to_perm_bound (#a:_) (#p:preorder a) (#f:perm) (r:ref a p) (#v:a)
  : stt_ghost unit
      (pts_to r #f v)
      (fun _ -> pts_to r #f v ** pure (f `lesser_equal_perm` full_perm))
