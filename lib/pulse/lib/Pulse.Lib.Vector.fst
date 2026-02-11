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
  arr:         A.array t;
  sz:          SZ.t;
  cap:         SZ.t;
  default_val: t;
}

let vector t = box (vector_internal t)

/// The is_vector predicate
let is_vector #t (v:vector t) (s:Seq.seq t) (cap:SZ.t) : slprop =
  exists* (vi:vector_internal t) (buf:Seq.seq t).
    pts_to v vi **
    A.pts_to vi.arr buf **
    pure (
      SZ.v vi.sz == Seq.length s /\
      SZ.v vi.cap == A.length vi.arr /\
      vi.cap == cap /\
      SZ.v vi.sz <= SZ.v vi.cap /\
      SZ.v vi.cap > 0 /\
      A.is_full_array vi.arr /\
      Seq.length buf == SZ.v vi.cap /\
      s `Seq.equal` Seq.slice buf 0 (SZ.v vi.sz)
    )

/// Create
#push-options "--warn_error -288"
fn create (#t:Type0) (default:t) (n:SZ.t{SZ.v n > 0})
  returns v:vector t
  ensures is_vector v (Seq.create (SZ.v n) default) n
{
  let arr = A.alloc default n;
  A.pts_to_len arr;
  let n' : SZ.t = n;
  let vi = Mkvector_internal #t arr n' n' default;
  let v = alloc vi;
  rewrite (A.pts_to arr (Seq.create (SZ.v n) default))
       as (A.pts_to vi.arr (Seq.create (SZ.v n) default));
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
  with vi buf. _;

  let vi_val = !v;
  rewrite (A.pts_to vi.arr buf) as (A.pts_to vi_val.arr buf);

  A.pts_to_len vi_val.arr;
  let x = A.op_Array_Access vi_val.arr i;

  rewrite (A.pts_to vi_val.arr buf) as (A.pts_to vi.arr buf);
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
  with vi buf. _;

  let vi_val = !v;
  rewrite (A.pts_to vi.arr buf) as (A.pts_to vi_val.arr buf);

  A.pts_to_len vi_val.arr;
  A.op_Array_Assignment vi_val.arr i x;
  with buf'. assert (A.pts_to vi_val.arr buf');

  rewrite (A.pts_to vi_val.arr buf') as (A.pts_to vi.arr buf');
  fold (is_vector v (Seq.upd s (SZ.v i) x) cap)
}

/// Get current size
fn size (#t:Type0) (v:vector t) (#s:erased (Seq.seq t)) (#cap:erased SZ.t)
  preserves is_vector v s cap
  returns n:SZ.t
  ensures pure (SZ.v n == Seq.length s)
{
  unfold (is_vector v s cap);
  with vi buf. _;
  let vi_val = !v;
  fold (is_vector v s cap);
  vi_val.sz
}

/// Get current capacity
fn capacity (#t:Type0) (v:vector t) (#s:erased (Seq.seq t)) (#cap:erased SZ.t)
  preserves is_vector v s cap
  returns n:SZ.t
  ensures pure (n == reveal cap)
{
  unfold (is_vector v s cap);
  with vi buf. _;
  let vi_val = !v;
  fold (is_vector v s cap);
  vi_val.cap
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
  with vi buf. _;

  let vi_val = !v;
  rewrite (A.pts_to vi.arr buf) as (A.pts_to vi_val.arr buf);
  A.pts_to_len vi_val.arr;

  if SZ.lt vi_val.sz vi_val.cap
  {
    // No resize needed — just insert at position size
    A.op_Array_Assignment vi_val.arr vi_val.sz x;
    with buf'. assert (A.pts_to vi_val.arr buf');
    let new_vi = Mkvector_internal #t vi_val.arr (SZ.add vi_val.sz 1sz) vi_val.cap vi_val.default_val;
    ( := ) v new_vi;

    rewrite (A.pts_to vi_val.arr buf') as (A.pts_to new_vi.arr buf');
    fold (is_vector v (Seq.snoc s x) cap);
    ()
  }
  else
  {
    // Resize: allocate double, copy, write new element, free old
    let new_cap = SZ.add vi_val.cap vi_val.cap;
    let new_arr = A.alloc vi_val.default_val new_cap;
    A.pts_to_len new_arr;

    let _sq = A.memcpy_l vi_val.cap vi_val.arr new_arr;

    A.op_Array_Assignment new_arr vi_val.sz x;
    with buf'. assert (A.pts_to new_arr buf');

    A.free vi_val.arr;

    let new_vi = Mkvector_internal #t new_arr (SZ.add vi_val.sz 1sz) new_cap vi_val.default_val;
    ( := ) v new_vi;

    rewrite (A.pts_to new_arr buf') as (A.pts_to new_vi.arr buf');
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
  with vi buf. _;

  let vi_val = !v;
  rewrite (A.pts_to vi.arr buf) as (A.pts_to vi_val.arr buf);
  A.pts_to_len vi_val.arr;

  let last_idx = SZ.sub vi_val.sz 1sz;
  let x = A.op_Array_Access vi_val.arr last_idx;

  let new_sz = last_idx;
  let half_cap = SZ.div vi_val.cap 2sz;
  let should_shrink = SZ.gt half_cap 0sz && SZ.eq new_sz half_cap;

  if should_shrink
  {
    // Shrink: allocate half, copy surviving elements, free old
    let new_arr = A.alloc vi_val.default_val half_cap;
    A.pts_to_len new_arr;

    let _sq = A.memcpy_l new_sz vi_val.arr new_arr;

    A.free vi_val.arr;

    let new_vi = Mkvector_internal #t new_arr new_sz half_cap vi_val.default_val;
    ( := ) v new_vi;

    with buf_new. assert (A.pts_to new_arr buf_new);
    rewrite (A.pts_to new_arr buf_new) as (A.pts_to new_vi.arr buf_new);
    fold (is_vector v (Seq.slice s 0 (Seq.length s - 1)) half_cap);
    x
  }
  else
  {
    // No shrink — just decrement size
    let new_vi = Mkvector_internal #t vi_val.arr new_sz vi_val.cap vi_val.default_val;
    ( := ) v new_vi;

    rewrite (A.pts_to vi_val.arr buf) as (A.pts_to new_vi.arr buf);
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
  with vi buf. _;

  let vi_val = !v;
  rewrite (A.pts_to vi.arr buf) as (A.pts_to vi_val.arr buf);
  A.pts_to_len vi_val.arr;

  if SZ.lte new_size vi_val.cap
  {
    let ns : SZ.t = new_size;
    let new_vi = Mkvector_internal #t vi_val.arr ns vi_val.cap vi_val.default_val;
    ( := ) v new_vi;
    rewrite (A.pts_to vi_val.arr buf) as (A.pts_to new_vi.arr buf);
    fold (is_vector v (Seq.slice buf 0 (SZ.v new_size)) cap);
    ()
  }
  else
  {
    let new_arr = A.alloc vi_val.default_val new_size;
    A.pts_to_len new_arr;
    let _sq = A.memcpy_l vi_val.sz vi_val.arr new_arr;
    A.free vi_val.arr;
    let ns : SZ.t = new_size;
    let new_vi = Mkvector_internal #t new_arr ns ns vi_val.default_val;
    ( := ) v new_vi;
    with buf'. assert (A.pts_to new_arr buf');
    rewrite (A.pts_to new_arr buf') as (A.pts_to new_vi.arr buf');
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
  with vi buf. _;

  let vi_val = !v;
  rewrite (A.pts_to vi.arr buf) as (A.pts_to vi_val.arr buf);

  A.free vi_val.arr;
  Box.free v;
  ()
}
#pop-options
