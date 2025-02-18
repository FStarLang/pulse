module Pulse.Lib.ConstArrayPtr
#lang-pulse

module Trade = Pulse.Lib.Trade.Util

let ptr a = AP.ptr a

let base p = AP.base p
let offset p = AP.offset p

let has_pts_to_array_ptr t = AP.has_pts_to_array_ptr t

let pts_to_timeless x p s = ()

fn from_arrayptr
  (#t: Type)
  (a: AP.ptr t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq t))
requires
  pts_to a #p v
returns s: ptr t
ensures
  pts_to s #p v ** Trade.trade (pts_to s #p v) (pts_to a #p v)
{
  let s : ptr t = a;
  Trade.rewrite_with_trade (pts_to a #p v) (pts_to s #p v);
  s
}

let is_from_array #t s sz a = AP.is_from_array #t s sz a

let from_array #t a #p #v = AP.from_array #t a #p #v

let to_array #t s a #p #v = AP.to_array #t s a #p #v

let op_Array_Access #t a i #p #s = AP.op_Array_Access #t a i #p #s

let share #a arr #s #p = AP.share #a arr #s #p

let gather #a arr #s0 #s1 #p0 #p1 = AP.gather #a arr #s0 #s1 #p0 #p1

let split #t s #p i #v = AP.split #t s #p i #v

let ghost_split #t s #p i #v = AP.ghost_split #t s #p i #v

let join #t s1 #p #v1 s2 #v2 = AP.join #t s1 #p #v1 s2 #v2

module R = Pulse.Lib.Reference

fn memcpy
    (#t:Type0) (#p0:perm)
    (src:ptr t) (idx_src: SZ.t)
    (dst:ptr t) (idx_dst: SZ.t)
    (len: SZ.t)
    (#s0:Ghost.erased (Seq.seq t) { SZ.v idx_src + SZ.v len <= Seq.length s0 })
    (#s1:Ghost.erased (Seq.seq t) { SZ.v idx_dst + SZ.v len <= Seq.length s1 })
  requires pts_to src #p0 s0 ** pts_to dst s1
  ensures pts_to src #p0 s0 **
    pts_to dst (Seq.slice s0 0 (SZ.v len) `Seq.append` Seq.slice s1 (SZ.v len) (Seq.length s1))
{
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
    invariant b. exists* s1' vi.
      R.pts_to i vi **
      pts_to src #p0 s0 **
      pts_to dst s1' **
      pure (b == SZ.lt vi len /\ SZ.lte vi len /\
        Seq.length s1' == Seq.length s1 /\
        forall (j:nat). j < Seq.length s1' ==>
          Seq.index s1' j == (if j < SZ.v vi then Seq.index s0 j else Seq.index s1 j))
  {
    let vi = !i;
    let x = src.(vi);
    AP.op_Array_Assignment dst vi x;
    i := SZ.add vi 1sz;
  };
  with s1'. assert pts_to dst s1';
  assert pure (s1' `Seq.equal`
    (Seq.slice s0 0 (SZ.v len) `Seq.append` Seq.slice s1 (SZ.v len) (Seq.length s1)))
}
