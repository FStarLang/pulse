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
