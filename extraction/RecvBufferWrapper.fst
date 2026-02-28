module RecvBufferWrapper

#lang-pulse
open Pulse.Lib.Pervasives
open FStar.SizeT
module SZ = FStar.SizeT
module Seq = FStar.Seq
module A = Pulse.Lib.Array
module CB = Pulse.Lib.CircularBuffer
module Spec = Pulse.Lib.CircularBuffer.Spec
open Pulse.Lib.CircularBuffer.Spec
module GT = Pulse.Lib.CircularBuffer.GapTrack
module Pow2 = Pulse.Lib.CircularBuffer.Pow2
module RM = Pulse.Lib.RangeVec
module RMSpec = Pulse.Lib.RangeMap.Spec
open Pulse.Lib.Trade

type byte = Spec.byte

/// Re-export circular_buffer and range_vec_t types
let circular_buffer = CB.circular_buffer
let range_vec_t = RM.range_vec_t
let write_result = CB.write_result

/// Re-export read_view
let read_view = CB.read_view

fn create
  (alloc_len: SZ.t{SZ.v alloc_len > 0})
  (virt_len: SZ.t{SZ.v virt_len > 0})
  requires pure (
    Pow2.is_pow2 (SZ.v alloc_len) /\
    Pow2.is_pow2 (SZ.v virt_len) /\
    SZ.v alloc_len <= SZ.v virt_len /\
    SZ.v alloc_len <= Spec.cb_max_length /\
    SZ.v virt_len <= CB.pow2_63)
  returns res : (circular_buffer & range_vec_t)
  ensures exists* st.
    CB.is_circular_buffer (fst res) (snd res) st **
    pure (Spec.cb_wf st /\
          st.base_offset == 0 /\
          st.alloc_length == SZ.v alloc_len /\
          st.virtual_length == SZ.v virt_len /\
          GT.contiguous_prefix_length st.contents == 0)
{
  CB.create alloc_len virt_len
}

fn free
  (cb: circular_buffer)
  (rm: range_vec_t)
  (#st: erased Spec.cb_state)
  requires CB.is_circular_buffer cb rm st
  ensures emp
{
  CB.free cb rm
}

fn read_length
  (cb: circular_buffer) (rm: range_vec_t)
  (#st: erased Spec.cb_state)
  requires CB.is_circular_buffer cb rm st
  returns n : SZ.t
  ensures CB.is_circular_buffer cb rm st **
          pure (SZ.v n == GT.contiguous_prefix_length st.contents)
{
  CB.read_length cb rm
}

fn get_total_length
  (cb: circular_buffer) (rm: range_vec_t)
  (#st: erased Spec.cb_state)
  requires CB.is_circular_buffer cb rm st
  returns n: SZ.t
  ensures CB.is_circular_buffer cb rm st **
          pure (SZ.v n <= st.base_offset + st.alloc_length)
{
  CB.get_total_length cb rm
}

fn get_alloc_length
  (cb: circular_buffer)
  (rm: range_vec_t)
  (#st: erased Spec.cb_state)
  requires CB.is_circular_buffer cb rm st ** pure (Spec.cb_wf st)
  returns n : SZ.t
  ensures CB.is_circular_buffer cb rm st ** pure (SZ.v n == st.alloc_length)
{
  CB.get_alloc_length cb rm
}

fn drain
  (cb: circular_buffer)
  (rm: range_vec_t)
  (n: SZ.t)
  (#st: erased Spec.cb_state)
  requires
    CB.is_circular_buffer cb rm st **
    pure (Spec.cb_wf st /\ SZ.v n <= st.alloc_length /\
          SZ.v n <= GT.contiguous_prefix_length st.contents /\
          SZ.fits (st.base_offset + SZ.v n))
  returns no_more_data: bool
  ensures
    CB.is_circular_buffer cb rm (Spec.drain_result st (SZ.v n)) **
    pure (no_more_data == (GT.contiguous_prefix_length st.contents = SZ.v n))
{
  CB.drain cb rm n
}

fn write_buffer
  (cb: circular_buffer) (rm: range_vec_t)
  (abs_offset: SZ.t) (src: A.array byte) (write_len: SZ.t)
  (#p: perm)
  (#src_data: erased (Seq.seq byte))
  (#st: erased Spec.cb_state)
  requires
    CB.is_circular_buffer cb rm st **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st /\
          SZ.v write_len == Seq.length src_data /\
          SZ.v write_len == A.length src /\
          SZ.v write_len > 0 /\
          SZ.v abs_offset + SZ.v write_len <= st.base_offset + st.virtual_length /\
          SZ.fits (SZ.v abs_offset + SZ.v write_len))
  returns wr: write_result
  ensures exists* st'.
    CB.is_circular_buffer cb rm st' **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st' /\
          st'.base_offset == st.base_offset /\
          st'.virtual_length == st.virtual_length /\
          (not wr.wrote ==> st'.alloc_length == st.alloc_length /\
                            st'.read_start == st.read_start /\
                            st'.contents == st.contents) /\
          (wr.wrote ==> st'.alloc_length >= st.alloc_length /\
                        GT.contiguous_prefix_length st'.contents >=
                          GT.contiguous_prefix_length st.contents))
{
  CB.write_buffer cb rm abs_offset src write_len
}

fn read_buffer
  (cb: circular_buffer)
  (rm: range_vec_t)
  (dst: A.array byte)
  (read_len: SZ.t)
  (#dst_data: erased (Seq.seq byte))
  (#st: erased Spec.cb_state)
  requires
    CB.is_circular_buffer cb rm st **
    A.pts_to dst dst_data **
    pure (Spec.cb_wf st /\
          SZ.v read_len <= GT.contiguous_prefix_length st.contents /\
          SZ.v read_len <= st.alloc_length /\
          SZ.v read_len <= A.length dst /\
          A.is_full_array dst)
  ensures exists* (dst_data': Seq.seq byte).
    CB.is_circular_buffer cb rm st **
    A.pts_to dst dst_data' **
    pure (Spec.cb_wf st /\
          SZ.v read_len <= Seq.length st.contents /\
          SZ.v read_len <= Seq.length dst_data' /\
          Seq.length dst_data' == Seq.length dst_data /\
          (forall (i:nat{i < SZ.v read_len}).
            Some? (Seq.index st.contents i) /\
            Seq.index dst_data' i == Some?.v (Seq.index st.contents i)))
{
  CB.read_buffer cb rm dst read_len
}

fn resize
  (cb: circular_buffer) (rm: range_vec_t) (new_al: SZ.t{SZ.v new_al > 0})
  (#st: erased Spec.cb_state)
  requires CB.is_circular_buffer cb rm st **
    pure (Spec.cb_wf st /\ Pow2.is_pow2 (SZ.v new_al) /\
          SZ.v new_al >= st.alloc_length /\
          SZ.v new_al <= st.virtual_length /\
          SZ.v new_al <= Spec.cb_max_length /\
          SZ.v new_al <= CB.pow2_63)
  ensures CB.is_circular_buffer cb rm (Spec.resize_result st (SZ.v new_al))
{
  CB.resize cb rm new_al
}

fn set_virtual_length
  (cb: circular_buffer) (rm: range_vec_t) (new_vl: SZ.t{SZ.v new_vl > 0})
  (#st: erased Spec.cb_state)
  requires CB.is_circular_buffer cb rm st **
    pure (Spec.cb_wf st /\
          Pow2.is_pow2 (SZ.v new_vl) /\
          SZ.v new_vl >= st.virtual_length /\
          SZ.v new_vl <= CB.pow2_63)
  ensures CB.is_circular_buffer cb rm ({ st with virtual_length = SZ.v new_vl })
{
  CB.set_virtual_length cb rm new_vl
}

fn read_zerocopy
  (cb: circular_buffer)
  (rm: range_vec_t)
  (read_len: SZ.t)
  (#st: erased Spec.cb_state)
  requires
    CB.is_circular_buffer cb rm st **
    pure (Spec.cb_wf st /\
          SZ.v read_len <= GT.contiguous_prefix_length st.contents /\
          SZ.v read_len <= st.alloc_length /\
          SZ.v read_len > 0)
  returns rv: read_view
  ensures exists* (s1 s2: Seq.seq byte).
    CB.zc_segs rv s1 s2 **
    (CB.zc_segs rv s1 s2 @==> CB.is_circular_buffer cb rm st) **
    pure (
      SZ.v rv.len1 + SZ.v rv.len2 == SZ.v read_len /\
      SZ.v rv.off1 + SZ.v rv.len1 <= st.alloc_length /\
      SZ.v rv.off2 + SZ.v rv.len2 <= st.alloc_length)
{
  CB.read_zerocopy cb rm read_len
}

fn release_read
  (cb: circular_buffer)
  (rm: range_vec_t)
  (rv: read_view)
  (#st: erased Spec.cb_state)
  (#s1 #s2: erased (Seq.seq byte))
  requires
    CB.zc_segs rv s1 s2 **
    (CB.zc_segs rv s1 s2 @==> CB.is_circular_buffer cb rm st)
  ensures
    CB.is_circular_buffer cb rm st
{
  CB.release_read cb rm rv
}

fn drain_after_read
  (cb: circular_buffer)
  (rm: range_vec_t)
  (rv: read_view)
  (drain_len: SZ.t)
  (#st: erased Spec.cb_state)
  (#s1 #s2: erased (Seq.seq byte))
  requires
    CB.zc_segs rv s1 s2 **
    (CB.zc_segs rv s1 s2 @==> CB.is_circular_buffer cb rm st) **
    pure (Spec.cb_wf st /\
          SZ.v drain_len <= st.alloc_length /\
          SZ.v drain_len <= GT.contiguous_prefix_length st.contents /\
          SZ.fits (st.base_offset + SZ.v drain_len))
  returns no_more_data: bool
  ensures
    CB.is_circular_buffer cb rm (Spec.drain_result st (SZ.v drain_len)) **
    pure (no_more_data == (GT.contiguous_prefix_length st.contents = SZ.v drain_len))
{
  CB.drain_after_read cb rm rv drain_len
}
