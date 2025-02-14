(*
   Copyright 2024 Microsoft Research

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

module Pulse.Lib.ConstArrayPtr
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
module SZ = FStar.SizeT
module A = Pulse.Lib.Array
module AP = Pulse.Lib.ArrayPtr
module Trade = Pulse.Lib.Trade

(*
The `ConstArrayPtr.ptr t` type in this module cannot be extracted to Rust
because of the `split` operation, which assumes that the same pointer
can point to either the large subarray or its sub-subarray, depending on the permission.
Rust slices have the length baked in, so they cannot support this operation
without modifying the pointer.

Use `Pulse.Lib.Slice.slice` instead when possible.
*)

val ptr ([@@@strictly_positive] elt: Type0) : Type0

val base #t (p: ptr t) : GTot (A.array t)
val offset #t (p: ptr t) : GTot nat

instance val has_pts_to_array_ptr (t: Type) : has_pts_to (ptr t) (Seq.seq t)

val pts_to_timeless (#a:Type) (x:ptr a) (p:perm) (s:Seq.seq a)
  : Lemma (timeless (pts_to x #p s))
          [SMTPat (timeless (pts_to x #p s))]

val from_arrayptr (#t: Type) (a: AP.ptr t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) : stt (ptr t)
    (pts_to a #p v)
    (fun s -> pts_to s #p v ** Trade.trade (pts_to s #p v) (pts_to a #p v))

val is_from_array (#t: Type) (s: ptr t) (sz: nat) (a: A.array t) : slprop

val from_array (#t: Type) (a: A.array t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) : stt (ptr t)
    (A.pts_to a #p v)
    (fun s -> pts_to s #p v ** is_from_array s (Seq.length v) a)

val to_array (#t: Type) (s: ptr t) (a: array t) (#p: perm) (#v: Seq.seq t) : stt_ghost unit emp_inames
    (pts_to s #p v ** is_from_array s (Seq.length v) a)
    (fun _ -> A.pts_to a #p v)

(* Written x.(i) *)
val op_Array_Access
        (#t: Type)
        (a: ptr t)
        (i: SZ.t)
        (#p: perm)
        (#s: Ghost.erased (Seq.seq t))
  : stt t
        (requires
            pts_to a #p s ** pure (SZ.v i < Seq.length s))
        (ensures fun res ->
            pts_to a #p s **
            pure (
              SZ.v i < Seq.length s /\
              res == Seq.index s (SZ.v i)))

val share
  (#a:Type)
  (arr:ptr a)
  (#s:Ghost.erased (Seq.seq a))
  (#p:perm)
: stt_ghost unit emp_inames
      (requires pts_to arr #p s)
      (ensures fun _ -> pts_to arr #(p /. 2.0R) s ** pts_to arr #(p /. 2.0R) s)

[@@allow_ambiguous]
val gather
  (#a:Type)
  (arr:ptr a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
: stt_ghost unit emp_inames
      (requires pts_to arr #p0 s0 ** pts_to arr #p1 s1 ** pure (Seq.length s0 == Seq.length s1))
      (ensures fun _ -> pts_to arr #(p0 +. p1) s0 ** pure (s0 == s1))


let adjacent #t (a: ptr t) (sz: nat) (b: ptr t) : prop =
  base a == base b /\ offset a + sz == offset b

val split (#t: Type) (s: ptr t) (#p: perm) (i: SZ.t)
  (#v: Ghost.erased (Seq.seq t) { SZ.v i <= Seq.length v })
  : stt (ptr t)
    (requires pts_to s #p v)
    (ensures fun s' ->
        pts_to s #p (Seq.slice v 0 (SZ.v i)) **
        pts_to s' #p (Seq.slice v (SZ.v i) (Seq.length v)) **
        pure (adjacent s (SZ.v i) s')
    )

val ghost_split (#t: Type) (s: ptr t) (#p: perm) (i: SZ.t)
  (#v: Ghost.erased (Seq.seq t) { SZ.v i <= Seq.length v })
  : stt_ghost (erased (ptr t)) []
    (requires pts_to s #p v)
    (ensures fun s' ->
        pts_to s #p (Seq.slice v 0 (SZ.v i)) **
        pts_to (reveal s') #p (Seq.slice v (SZ.v i) (Seq.length v)) **
        pure (adjacent s (SZ.v i) s')
    )

val join (#t: Type) (s1: ptr t) (#p: perm) (#v1: Seq.seq t) (s2: ptr t) (#v2: Seq.seq t) : stt_ghost unit emp_inames
    (pts_to s1 #p v1 ** pts_to s2 #p v2 ** pure (adjacent s1 (Seq.length v1) s2))
    (fun _ -> pts_to s1 #p (Seq.append v1 v2))
