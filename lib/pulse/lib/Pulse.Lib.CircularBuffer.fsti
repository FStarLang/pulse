module Pulse.Lib.CircularBuffer

#lang-pulse
open Pulse.Lib.Pervasives
open FStar.SizeT
open Pulse.Lib.CircularBuffer.Spec
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Spec = Pulse.Lib.CircularBuffer.Spec
module Pow2 = Pulse.Lib.CircularBuffer.Pow2
module GT = Pulse.Lib.CircularBuffer.GapTrack
module A = Pulse.Lib.Array

/// Pre-computed pow2 63 so Z3 never evaluates Prims.pow2 recursively
let pow2_63 : nat = 0x8000000000000000

/// Abstract circular buffer type
val circular_buffer : Type0

/// Abstract predicate connecting physical buffer to ghost spec state.
val is_circular_buffer ([@@@mkey]cb: circular_buffer) (st: Spec.cb_state) : slprop

/// Create a new empty circular buffer
fn create
  (alloc_len: SZ.t{SZ.v alloc_len > 0})
  (virt_len: SZ.t{SZ.v virt_len > 0})
  requires pure (
    Pow2.is_pow2 (SZ.v alloc_len) /\
    Pow2.is_pow2 (SZ.v virt_len) /\
    SZ.v alloc_len <= SZ.v virt_len /\
    SZ.v virt_len <= pow2_63)
  returns cb : circular_buffer
  ensures exists* st.
    is_circular_buffer cb st **
    pure (Spec.cb_wf st /\
          st.base_offset == 0 /\
          st.alloc_length == SZ.v alloc_len /\
          st.virtual_length == SZ.v virt_len /\
          GT.contiguous_prefix_length st.contents == 0)

/// Write a single byte at a logical offset, with new prefix length
fn write_byte
  (cb: circular_buffer)
  (offset: SZ.t)
  (b: byte)
  (new_pl: SZ.t)
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer cb st **
    pure (Spec.cb_wf st /\ SZ.v offset < st.alloc_length /\
          SZ.v new_pl == GT.contiguous_prefix_length
            (Seq.upd st.contents (SZ.v offset) (Some b)))
  ensures
    is_circular_buffer cb (Spec.write_result st (SZ.v offset) b)

/// Get the length of contiguous readable data
fn read_length
  (cb: circular_buffer)
  (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st ** pure (Spec.cb_wf st)
  returns n : SZ.t
  ensures is_circular_buffer cb st **
          pure (SZ.v n == GT.contiguous_prefix_length st.contents)

/// Drain n bytes from the front (n must not exceed prefix length)
fn drain
  (cb: circular_buffer)
  (n: SZ.t)
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer cb st **
    pure (Spec.cb_wf st /\ SZ.v n <= st.alloc_length /\
          SZ.v n <= GT.contiguous_prefix_length st.contents)
  ensures
    is_circular_buffer cb (Spec.drain_result st (SZ.v n))

/// Resize (grow) the buffer
fn resize
  (cb: circular_buffer)
  (new_al: SZ.t{SZ.v new_al > 0})
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer cb st **
    pure (Spec.cb_wf st /\
          Pow2.is_pow2 (SZ.v new_al) /\
          SZ.v new_al >= st.alloc_length /\
          SZ.v new_al <= st.virtual_length /\
          SZ.v new_al <= pow2_63)
  ensures
    is_circular_buffer cb (Spec.resize_result st (SZ.v new_al))

/// Free the circular buffer
fn free
  (cb: circular_buffer)
  (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st
  ensures emp

/// Get the current alloc_length
fn get_alloc_length
  (cb: circular_buffer)
  (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st ** pure (Spec.cb_wf st)
  returns n : SZ.t
  ensures is_circular_buffer cb st ** pure (SZ.v n == st.alloc_length)

/// Read a single byte at a logical offset within the contiguous prefix
fn read_byte
  (cb: circular_buffer)
  (offset: SZ.t)
  (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st **
    pure (Spec.cb_wf st /\
          SZ.v offset < GT.contiguous_prefix_length st.contents /\
          SZ.v offset < Seq.length st.contents)
  returns b: byte
  ensures is_circular_buffer cb st **
    pure (SZ.v offset < Seq.length st.contents /\
          Some? (Seq.index st.contents (SZ.v offset)) /\
          b == Some?.v (Seq.index st.contents (SZ.v offset)))

/// Write a buffer of bytes sequentially at the end of the contiguous prefix.
/// Auto-resizes if the write would exceed the current alloc_length.
/// Requires the buffer to be gapless (all positions >= prefix are None).
fn write_buffer
  (cb: circular_buffer)
  (src: A.array byte)
  (write_len: SZ.t)
  (#p: perm)
  (#src_data: erased (Seq.seq byte))
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer cb st **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st /\
          Spec.gapless st /\
          SZ.v write_len == Seq.length src_data /\
          SZ.v write_len == A.length src /\
          GT.contiguous_prefix_length st.contents + SZ.v write_len <= st.virtual_length)
  returns new_data_ready: bool
  ensures exists* st'.
    is_circular_buffer cb st' **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st' /\
          Spec.gapless st' /\
          st'.base_offset == st.base_offset /\
          st'.virtual_length == st.virtual_length /\
          st'.alloc_length >= st.alloc_length /\
          GT.contiguous_prefix_length st'.contents ==
            GT.contiguous_prefix_length st.contents + SZ.v write_len /\
          new_data_ready == (SZ.v write_len > 0))

/// Read the contiguous prefix of the buffer into a destination array.
/// Copies read_len bytes from the circular buffer into dst.
/// The circular buffer state is unchanged.
fn read_buffer
  (cb: circular_buffer)
  (dst: A.array byte)
  (read_len: SZ.t)
  (#dst_data: erased (Seq.seq byte))
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer cb st **
    A.pts_to dst dst_data **
    pure (Spec.cb_wf st /\
          SZ.v read_len <= GT.contiguous_prefix_length st.contents /\
          SZ.v read_len <= st.alloc_length /\
          SZ.v read_len <= A.length dst /\
          A.is_full_array dst)
  ensures exists* (dst_data': Seq.seq byte).
    is_circular_buffer cb st **
    A.pts_to dst dst_data' **
    pure (Spec.cb_wf st /\
          SZ.v read_len <= Seq.length st.contents /\
          SZ.v read_len <= Seq.length dst_data' /\
          Seq.length dst_data' == Seq.length dst_data /\
          (forall (i:nat{i < SZ.v read_len}).
            Some? (Seq.index st.contents i) /\
            Seq.index dst_data' i == Some?.v (Seq.index st.contents i)))
