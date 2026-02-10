(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.Vector

#lang-pulse

open Pulse.Lib.Pervasives
module Seq = FStar.Seq
module SZ = FStar.SizeT
module A = Pulse.Lib.Array
module Box = Pulse.Lib.Box
open Pulse.Lib.Box

/// Internal representation
noeq
type vector_internal (t:Type0) = {
  arr_box:     box (A.array t);
  size_box:    box SZ.t;
  cap_box:     box SZ.t;
  default_val: t;
}

let vector t = vector_internal t

/// The is_vector predicate
let is_vector #t (v:vector t) (s:Seq.seq t) (cap:SZ.t) : slprop =
  exists* (arr:A.array t) (buf:Seq.seq t) (sz:SZ.t) (cap_sz:SZ.t).
    pts_to v.arr_box arr **
    pts_to v.size_box sz **
    pts_to v.cap_box cap_sz **
    A.pts_to arr buf **
    pure (
      SZ.v sz == Seq.length s /\
      SZ.v cap_sz == A.length arr /\
      cap_sz == cap /\
      SZ.v sz <= SZ.v cap /\
      SZ.v cap > 0 /\
      A.is_full_array arr /\
      Seq.length buf == SZ.v cap /\
      s `Seq.equal` Seq.slice buf 0 (SZ.v sz)
    )

/// Create
#push-options "--warn_error -288"
fn create (#t:Type0) (default:t) (n:SZ.t{SZ.v n > 0})
  returns v:vector t
  ensures is_vector v (Seq.create (SZ.v n) default) n
{
  let arr = A.alloc default n;
  A.pts_to_len arr;
  let arr_box : box (A.array t) = alloc arr;
  let n' : SZ.t = n;
  let size_box : box SZ.t = alloc n';
  let cap_box : box SZ.t = alloc n';

  let v : vector_internal t = Mkvector_internal #t arr_box size_box cap_box default;

  rewrite (pts_to arr_box arr) as (pts_to v.arr_box arr);
  rewrite (pts_to size_box n') as (pts_to v.size_box n');
  rewrite (pts_to cap_box n') as (pts_to v.cap_box n');

  fold (is_vector v (Seq.create (SZ.v n) default) n);
  v
}
#pop-options

/// Read element at index
fn at (#t:Type0) (v:vector t) (i:SZ.t)
  (#s:erased (Seq.seq t){SZ.v i < Seq.length s}) (#cap:erased SZ.t)
  preserves is_vector v s cap
  returns x:t
  ensures pure (x == Seq.index s (SZ.v i))
{
  unfold (is_vector v s cap);
  with arr buf sz cap_sz. _;

  let current_arr = !v.arr_box;
  rewrite (A.pts_to arr buf) as (A.pts_to current_arr buf);

  A.pts_to_len current_arr;
  let x = A.op_Array_Access current_arr i;

  rewrite (A.pts_to current_arr buf) as (A.pts_to arr buf);
  fold (is_vector v s cap);
  x
}

/// Write element at index
fn set (#t:Type0) (v:vector t) (i:SZ.t) (x:t)
  (#s:erased (Seq.seq t){SZ.v i < Seq.length s}) (#cap:erased SZ.t)
  requires is_vector v s cap
  ensures is_vector v (Seq.upd s (SZ.v i) x) cap
{
  unfold (is_vector v s cap);
  with arr buf sz cap_sz. _;

  let current_arr = !v.arr_box;
  rewrite (A.pts_to arr buf) as (A.pts_to current_arr buf);

  A.pts_to_len current_arr;
  A.op_Array_Assignment current_arr i x;
  with buf'. assert (A.pts_to current_arr buf');

  rewrite (A.pts_to current_arr buf') as (A.pts_to arr buf');
  fold (is_vector v (Seq.upd s (SZ.v i) x) cap)
}

/// Get current size
fn size (#t:Type0) (v:vector t) (#s:erased (Seq.seq t)) (#cap:erased SZ.t)
  preserves is_vector v s cap
  returns n:SZ.t
  ensures pure (SZ.v n == Seq.length s)
{
  unfold (is_vector v s cap);
  with arr buf sz cap_sz. _;
  let n = !v.size_box;
  fold (is_vector v s cap);
  n
}

/// Get current capacity
fn capacity (#t:Type0) (v:vector t) (#s:erased (Seq.seq t)) (#cap:erased SZ.t)
  preserves is_vector v s cap
  returns n:SZ.t
  ensures pure (n == reveal cap)
{
  unfold (is_vector v s cap);
  with arr buf sz cap_sz. _;
  let n = !v.cap_box;
  fold (is_vector v s cap);
  n
}

/// Push back — append element, double capacity if full
#push-options "--warn_error -288 --z3rlimit_factor 4"
fn push_back (#t:Type0) (v:vector t) (x:t)
  (#s:erased (Seq.seq t)) (#cap:erased SZ.t)
  requires is_vector v s cap **
           pure (Seq.length s < SZ.v cap \/ SZ.fits (SZ.v cap + SZ.v cap))
  ensures exists* (cap':SZ.t).
    is_vector v (Seq.snoc s x) cap' **
    pure (SZ.v cap' >= Seq.length s + 1 /\ SZ.v cap' > 0)
{
  unfold (is_vector v s cap);
  with arr buf sz cap_sz. _;

  let current_sz = !v.size_box;
  let current_cap = !v.cap_box;
  let current_arr = !v.arr_box;
  rewrite (A.pts_to arr buf) as (A.pts_to current_arr buf);
  A.pts_to_len current_arr;

  if SZ.lt current_sz current_cap
  {
    // No resize needed — just insert at position size
    A.op_Array_Assignment current_arr current_sz x;
    with buf'. assert (A.pts_to current_arr buf');
    ( := ) v.size_box (SZ.add current_sz 1sz);

    rewrite (A.pts_to current_arr buf') as (A.pts_to arr buf');
    fold (is_vector v (Seq.snoc s x) cap);
    ()
  }
  else
  {
    // Resize: allocate double, copy, write new element, free old
    let new_cap = SZ.add current_cap current_cap;
    let new_arr = A.alloc v.default_val new_cap;
    A.pts_to_len new_arr;

    let _sq = A.memcpy_l current_cap current_arr new_arr;

    A.op_Array_Assignment new_arr current_sz x;
    with buf'. assert (A.pts_to new_arr buf');

    A.free current_arr;

    ( := ) v.arr_box new_arr;
    ( := ) v.size_box (SZ.add current_sz 1sz);
    ( := ) v.cap_box new_cap;

    rewrite (A.pts_to new_arr buf') as (A.pts_to (reveal (hide new_arr)) buf');
    fold (is_vector v (Seq.snoc s x) new_cap);
    ()
  }
}
#pop-options

/// Pop back — remove last element, halve capacity when size == floor(cap/2)
#push-options "--warn_error -288 --z3rlimit_factor 4"
fn pop_back (#t:Type0) (v:vector t)
  (#s:erased (Seq.seq t){Seq.length s > 0}) (#cap:erased SZ.t)
  requires is_vector v s cap
  returns x:t
  ensures exists* (cap':SZ.t).
    is_vector v (Seq.slice s 0 (Seq.length s - 1)) cap' **
    pure (x == Seq.index s (Seq.length s - 1) /\
          SZ.v cap' >= Seq.length s - 1 /\ SZ.v cap' > 0)
{
  unfold (is_vector v s cap);
  with arr buf sz cap_sz. _;

  let current_sz = !v.size_box;
  let current_cap = !v.cap_box;
  let current_arr = !v.arr_box;
  rewrite (A.pts_to arr buf) as (A.pts_to current_arr buf);
  A.pts_to_len current_arr;

  let last_idx = SZ.sub current_sz 1sz;
  let x = A.op_Array_Access current_arr last_idx;

  let new_sz = last_idx;
  let half_cap = SZ.div current_cap 2sz;
  let should_shrink = SZ.gt half_cap 0sz && SZ.eq new_sz half_cap;

  if should_shrink
  {
    // Shrink: allocate half, copy surviving elements, free old
    let new_arr = A.alloc v.default_val half_cap;
    A.pts_to_len new_arr;

    let _sq = A.memcpy_l new_sz current_arr new_arr;

    A.free current_arr;

    ( := ) v.arr_box new_arr;
    ( := ) v.size_box new_sz;
    ( := ) v.cap_box half_cap;

    with buf_new. assert (A.pts_to new_arr buf_new);
    rewrite (A.pts_to new_arr buf_new) as (A.pts_to (reveal (hide new_arr)) buf_new);
    fold (is_vector v (Seq.slice s 0 (Seq.length s - 1)) half_cap);
    x
  }
  else
  {
    // No shrink — just decrement size
    ( := ) v.size_box new_sz;

    rewrite (A.pts_to current_arr buf) as (A.pts_to arr buf);
    fold (is_vector v (Seq.slice s 0 (Seq.length s - 1)) cap);
    x
  }
}
#pop-options

/// Resize
#push-options "--warn_error -288 --z3rlimit_factor 4"
fn resize (#t:Type0) (v:vector t) (new_size:SZ.t{SZ.v new_size > 0})
  (#s:erased (Seq.seq t)) (#cap:erased SZ.t)
  requires is_vector v s cap
  ensures exists* (s':Seq.seq t) (cap':SZ.t).
    is_vector v s' cap' **
    pure (Seq.length s' == SZ.v new_size /\
          SZ.v cap' >= SZ.v new_size /\ SZ.v cap' > 0 /\
          (forall (i:nat). i < Seq.length s /\ i < SZ.v new_size ==>
            Seq.index s' i == Seq.index s i))
{
  unfold (is_vector v s cap);
  with arr buf sz cap_sz. _;

  let current_sz = !v.size_box;
  let current_cap = !v.cap_box;
  let current_arr = !v.arr_box;
  rewrite (A.pts_to arr buf) as (A.pts_to current_arr buf);
  A.pts_to_len current_arr;

  if SZ.lte new_size current_cap
  {
    ( := ) v.size_box new_size;
    rewrite (A.pts_to current_arr buf) as (A.pts_to arr buf);
    fold (is_vector v (Seq.slice buf 0 (SZ.v new_size)) cap);
    ()
  }
  else
  {
    let new_arr = A.alloc v.default_val new_size;
    A.pts_to_len new_arr;
    let _sq = A.memcpy_l current_sz current_arr new_arr;
    A.free current_arr;
    ( := ) v.arr_box new_arr;
    ( := ) v.size_box new_size;
    ( := ) v.cap_box new_size;
    with buf'. assert (A.pts_to new_arr buf');
    rewrite (A.pts_to new_arr buf') as (A.pts_to (reveal (hide new_arr)) buf');
    fold (is_vector v (Seq.slice buf' 0 (SZ.v new_size)) new_size);
    ()
  }
}
#pop-options

/// Free
#push-options "--warn_error -288"
fn free (#t:Type0) (v:vector t) (#s:erased (Seq.seq t)) (#cap:erased SZ.t)
  requires is_vector v s cap
{
  unfold (is_vector v s cap);
  with arr buf sz cap_sz. _;

  let current_arr = !v.arr_box;
  rewrite (A.pts_to arr buf) as (A.pts_to current_arr buf);

  A.free current_arr;
  Box.free v.arr_box;
  Box.free v.size_box;
  Box.free v.cap_box;
  ()
}
#pop-options
