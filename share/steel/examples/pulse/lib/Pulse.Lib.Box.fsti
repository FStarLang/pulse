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

module Pulse.Lib.Box

open FStar.Ghost
open Steel.FractionalPermission

open Pulse.Lib.Core

module U32 = FStar.UInt32
module T = FStar.Tactics.V2

module R = Pulse.Lib.Reference

val box ([@@@strictly_positive] a:Type0) : Type0

val pts_to (#a:Type0) (b:box a) (#[T.exact (`full_perm)]p:perm) (v:a) : vprop

val alloc (#a:Type0) (x:a)
  : stt (box a) emp (fun b -> pts_to b x)
  
val ( ! ) (#a:Type0) (b:box a) (#v:erased a) (#p:perm)
  : stt a
      (pts_to b #p v)
      (fun x -> pts_to b #p x ** pure (eq2 #a (reveal v) x))

val ( := ) (#a:Type0) (b:box a) (x:a) (#v:erased a)
  : stt unit
      (pts_to b v) 
      (fun _ -> pts_to b (hide x))

val free (#a:Type0) (b:box a) (#v:erased a)
  : stt unit (pts_to b v) (fun _ -> emp)

// val share (#a:Type) #inames (r:ref a) (#v:erased a) (#p:perm)
//   : stt_ghost unit inames
//       (pts_to r #p v)
//       (fun _ ->
//        pts_to r #(half_perm p) v **
//        pts_to r #(half_perm p) v)

// val gather (#a:Type) #inames (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
//   : stt_ghost unit inames
//       (pts_to r #p0 x0 ** pts_to r #p1 x1)
//       (fun _ -> pts_to r #(sum_perm p0 p1) x0 ** pure (x0 == x1))

// (* Share/gather specialized to half permission *)
// val share2 (#a:Type) #inames (r:ref a) (#v:erased a)
//   : stt_ghost unit inames
//       (pts_to r v)
//       (fun _ -> pts_to r #one_half v ** pts_to r #one_half v)

// val gather2 (#a:Type) #inames (r:ref a) (#x0 #x1:erased a)
//   : stt_ghost unit inames
//       (pts_to r #one_half x0 ** pts_to r #one_half x1)
//       (fun _ -> pts_to r x0 ** pure (x0 == x1))

// val read_atomic (r:ref U32.t) (#n:erased U32.t) (#p:perm)
//   : stt_atomic U32.t emp_inames
//     (pts_to r #p n)
//     (fun x -> pts_to r #p n ** pure (reveal n == x))

// val write_atomic (r:ref U32.t) (x:U32.t) (#n:erased U32.t)
//   : stt_atomic unit emp_inames
//         (pts_to r n) 
//         (fun _ -> pts_to r (hide x))

// val with_local
//   (#a:Type0)
//   (init:a)
//   (#pre:vprop)
//   (#ret_t:Type)
//   (#post:ret_t -> vprop)
//   (body:(r:ref a) -> stt ret_t (pre ** pts_to r init)
//                               (fun v -> post v ** exists_ (pts_to r)))
//   : stt ret_t pre post


// val pts_to_injective_eq (#a:_)
//                         (#p #q:_)
//                         (#v0 #v1:a)
//                         (r:ref a)
//   : stt_ghost unit emp_inames
//       (pts_to r #p v0 ** pts_to r #q v1)
//       (fun _ -> pts_to r #p v0 ** pts_to r #q v0 ** pure (v0 == v1))

val box_to_ref  (#a:Type0) (b:box a) : R.ref a

val to_ref_pts_to (#a:Type0) (b:box a) (#p:perm) (#v:a)
  : stt_ghost unit emp_inames (pts_to b #p v) (fun _ -> R.pts_to (box_to_ref b) #p v)

val to_box_pts_to (#a:Type0) (b:box a) (#p:perm) (#v:a)
  : stt_ghost unit emp_inames (R.pts_to (box_to_ref b) #p v) (fun _ -> pts_to b #p v)
