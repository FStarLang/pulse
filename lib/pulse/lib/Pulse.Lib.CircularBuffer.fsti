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
module RM = Pulse.Lib.RangeMap
module RMSpec = Pulse.Lib.RangeMap.Spec
open Pulse.Lib.Trade

/// Pre-computed pow2 63 so Z3 never evaluates Prims.pow2 recursively
let pow2_63 : nat = 0x8000000000000000

/// Result of a write operation
noeq type write_result = {
  wrote: bool;          // true if any bytes were actually written
  new_data_ready: bool; // true if new contiguous data became available from position 0
  resize_failed: bool;  // true if auto-resize was needed but would exceed cb_max_length
}

/// Abstract circular buffer type
val circular_buffer : Type0

/// Abstract predicate connecting physical buffer to ghost spec state.
/// Prefix length is tracked exactly (pl == contiguous_prefix_length).
val is_circular_buffer ([@@@mkey]cb: circular_buffer) (st: Spec.cb_state) : slprop

/// OOO predicate: same as is_circular_buffer but prefix length is a lower bound.
/// Used after out-of-order writes where exact prefix can't be determined without a range map.
val is_circular_buffer_ooo ([@@@mkey]cb: circular_buffer) (st: Spec.cb_state) : slprop

/// Create a new empty circular buffer
fn create
  (alloc_len: SZ.t{SZ.v alloc_len > 0})
  (virt_len: SZ.t{SZ.v virt_len > 0})
  requires pure (
    Pow2.is_pow2 (SZ.v alloc_len) /\
    Pow2.is_pow2 (SZ.v virt_len) /\
    SZ.v alloc_len <= SZ.v virt_len /\
    SZ.v alloc_len <= Spec.cb_max_length /\
    SZ.v virt_len <= pow2_63)
  returns cb : circular_buffer
  ensures exists* st.
    is_circular_buffer cb st **
    pure (Spec.cb_wf st /\
          st.base_offset == 0 /\
          st.alloc_length == SZ.v alloc_len /\
          st.virtual_length == SZ.v virt_len /\
          GT.contiguous_prefix_length st.contents == 0)

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
          SZ.v n <= GT.contiguous_prefix_length st.contents /\
          SZ.fits (st.base_offset + SZ.v n))
  returns no_more_data: bool
  ensures
    is_circular_buffer cb (Spec.drain_result st (SZ.v n)) **
    pure (no_more_data == (GT.contiguous_prefix_length st.contents = SZ.v n))

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
          SZ.v new_al <= Spec.cb_max_length /\
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
          GT.contiguous_prefix_length st.contents + SZ.v write_len <= st.virtual_length /\
          GT.contiguous_prefix_length st.contents + SZ.v write_len <= Spec.cb_max_length)
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

/// Transition from exact prefix tracking to OOO mode (== implies <=)
fn enter_ooo
  (cb: circular_buffer)
  (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st
  ensures is_circular_buffer_ooo cb st

/// Get a lower bound on contiguous prefix length (OOO mode)
fn read_length_ooo
  (cb: circular_buffer)
  (#st: erased Spec.cb_state)
  requires is_circular_buffer_ooo cb st ** pure (Spec.cb_wf st)
  returns n : SZ.t
  ensures is_circular_buffer_ooo cb st **
          pure (SZ.v n <= GT.contiguous_prefix_length st.contents)

/// Out-of-order write at an arbitrary offset within the allocated buffer.
/// Does not require gapless. Does not auto-resize.
/// Uses OOO predicate (conservative prefix tracking).
fn write_buffer_ooo
  (cb: circular_buffer)
  (offset: SZ.t)
  (src: A.array byte)
  (write_len: SZ.t)
  (#p: perm)
  (#src_data: erased (Seq.seq byte))
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer_ooo cb st **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st /\
          SZ.v write_len == Seq.length src_data /\
          SZ.v write_len == A.length src /\
          SZ.v offset + SZ.v write_len <= st.alloc_length)
  ensures exists* st'.
    is_circular_buffer_ooo cb st' **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st' /\
          st'.base_offset == st.base_offset /\
          st'.virtual_length == st.virtual_length /\
          st'.alloc_length == st.alloc_length /\
          st'.read_start == st.read_start /\
          st'.contents == GT.write_range_contents_t st.contents (SZ.v offset) (reveal src_data) /\
          GT.contiguous_prefix_length st'.contents >=
            GT.contiguous_prefix_length st.contents)

/// RM-tracked predicate: exact prefix via RangeMap, bridge links RM to option-byte contents.
val is_circular_buffer_rm
  ([@@@mkey]cb: circular_buffer)
  (rm: RM.range_map_t)
  (st: Spec.cb_state) : slprop

/// Transition from exact mode + RangeMap to RM mode
fn enter_rm
  (cb: circular_buffer) (rm: RM.range_map_t)
  (#st: erased Spec.cb_state)
  (#repr: erased (Seq.seq RMSpec.interval))
  requires
    is_circular_buffer cb st **
    RM.is_range_map rm repr **
    pure (Spec.ranges_match_contents repr st.contents st.base_offset /\
          Spec.base_aligned repr st.base_offset /\
          RMSpec.range_map_wf repr)
  ensures is_circular_buffer_rm cb rm st

/// Transition from RM mode back to OOO mode, releasing the range map
fn exit_rm_to_ooo
  (cb: circular_buffer) (rm: RM.range_map_t)
  (#st: erased Spec.cb_state)
  requires is_circular_buffer_rm cb rm st
  ensures exists* repr.
    is_circular_buffer_ooo cb st **
    RM.is_range_map rm repr

/// RM-mode resize: grow buffer while preserving range map bridge.
fn resize_rm
  (cb: circular_buffer) (rm: RM.range_map_t) (new_al: SZ.t{SZ.v new_al > 0})
  (#st: erased Spec.cb_state)
  requires is_circular_buffer_rm cb rm st **
    pure (Spec.cb_wf st /\ Pow2.is_pow2 (SZ.v new_al) /\
          SZ.v new_al >= st.alloc_length /\
          SZ.v new_al <= st.virtual_length /\
          SZ.v new_al <= Spec.cb_max_length /\
          SZ.v new_al <= pow2_63)
  ensures is_circular_buffer_rm cb rm (Spec.resize_result st (SZ.v new_al))

/// Get a lower bound on contiguous prefix length (RM mode)
fn read_length_rm
  (cb: circular_buffer) (rm: RM.range_map_t)
  (#st: erased Spec.cb_state)
  requires is_circular_buffer_rm cb rm st
  returns n : SZ.t
  ensures is_circular_buffer_rm cb rm st **
          pure (SZ.v n == GT.contiguous_prefix_length st.contents)

/// Get total length: max absolute offset with data (RM mode)
fn get_total_length_rm
  (cb: circular_buffer) (rm: RM.range_map_t)
  (#st: erased Spec.cb_state)
  requires is_circular_buffer_rm cb rm st
  returns n: SZ.t
  ensures is_circular_buffer_rm cb rm st **
          pure (SZ.v n <= st.base_offset + st.alloc_length)

/// Increase virtual buffer length (both modes)
fn set_virtual_length
  (cb: circular_buffer) (new_vl: SZ.t{SZ.v new_vl > 0})
  (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st **
    pure (Spec.cb_wf st /\
          Pow2.is_pow2 (SZ.v new_vl) /\
          SZ.v new_vl >= st.virtual_length /\
          SZ.v new_vl <= pow2_63)
  ensures is_circular_buffer cb ({ st with virtual_length = SZ.v new_vl })

fn set_virtual_length_rm
  (cb: circular_buffer) (rm: RM.range_map_t) (new_vl: SZ.t{SZ.v new_vl > 0})
  (#st: erased Spec.cb_state)
  requires is_circular_buffer_rm cb rm st **
    pure (Spec.cb_wf st /\
          Pow2.is_pow2 (SZ.v new_vl) /\
          SZ.v new_vl >= st.virtual_length /\
          SZ.v new_vl <= pow2_63)
  ensures is_circular_buffer_rm cb rm ({ st with virtual_length = SZ.v new_vl })

/// RM-tracked out-of-order write: writes data at an arbitrary offset,
/// updates both the physical buffer and the range map, and computes exact new prefix.
fn write_buffer_rm
  (cb: circular_buffer)
  (rm: RM.range_map_t)
  (offset: SZ.t)
  (src: A.array byte)
  (write_len: SZ.t)
  (#p: perm)
  (#src_data: erased (Seq.seq byte))
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer_rm cb rm st **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st /\
          SZ.v write_len == Seq.length src_data /\
          SZ.v write_len == A.length src /\
          SZ.v write_len > 0 /\
          SZ.v offset + SZ.v write_len <= st.alloc_length /\
          SZ.fits (st.base_offset + SZ.v offset + SZ.v write_len))
  ensures exists* st'.
    is_circular_buffer_rm cb rm st' **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st' /\
          st'.base_offset == st.base_offset /\
          st'.virtual_length == st.virtual_length /\
          st'.alloc_length == st.alloc_length /\
          st'.read_start == st.read_start /\
          st'.contents == GT.write_range_contents_t st.contents (SZ.v offset) (reveal src_data) /\
          GT.contiguous_prefix_length st'.contents >=
            GT.contiguous_prefix_length st.contents)

/// RM-tracked absolute-offset write with trim, auto-resize, and failure handling.
/// Handles stale writes (no-op), partial overlap trim, auto-resize up to cb_max_length.
fn write_buffer_rm_abs
  (cb: circular_buffer) (rm: RM.range_map_t)
  (abs_offset: SZ.t) (src: A.array byte) (write_len: SZ.t)
  (#p: perm)
  (#src_data: erased (Seq.seq byte))
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer_rm cb rm st **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st /\
          SZ.v write_len == Seq.length src_data /\
          SZ.v write_len == A.length src /\
          SZ.v write_len > 0 /\
          SZ.v abs_offset + SZ.v write_len <= st.base_offset + st.virtual_length /\
          SZ.fits (SZ.v abs_offset + SZ.v write_len))
  returns wr: write_result
  ensures exists* st'.
    is_circular_buffer_rm cb rm st' **
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

/// RM-tracked drain: advance read_start and base_offset, slice contents.
/// The range map is UNCHANGED — this is the key advantage of absolute offsets.
fn drain_rm
  (cb: circular_buffer)
  (rm: RM.range_map_t)
  (n: SZ.t)
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer_rm cb rm st **
    pure (Spec.cb_wf st /\ SZ.v n <= st.alloc_length /\
          SZ.v n <= GT.contiguous_prefix_length st.contents /\
          SZ.fits (st.base_offset + SZ.v n))
  returns no_more_data: bool
  ensures
    is_circular_buffer_rm cb rm (Spec.drain_result st (SZ.v n)) **
    pure (no_more_data == (GT.contiguous_prefix_length st.contents = SZ.v n))

/// --- Zero-copy Read ---

/// Return type for zero-copy read: references into the buffer's internal array.
noeq type read_view = {
  arr: A.array byte;    // The underlying buffer array
  off1: SZ.t;           // Start of segment 1
  len1: SZ.t;           // Length of segment 1
  off2: SZ.t;           // Start of segment 2 (0 if no wrap)
  len2: SZ.t;           // Length of segment 2 (0 if no wrap)
}

/// Abbreviation for the two read-segment slprops
let zc_segs (rv: read_view) (s1 s2: Seq.seq byte) : slprop =
  A.pts_to_range rv.arr (SZ.v rv.off1) (SZ.v rv.off1 + SZ.v rv.len1) s1 **
  A.pts_to_range rv.arr (SZ.v rv.off2) (SZ.v rv.off2 + SZ.v rv.len2) s2

/// Zero-copy read: returns segment pointers into the internal buffer,
/// plus a trade that restores the buffer when the segments are returned.
/// Up to 2 segments for wrap-around (like MsQuic's QuicRecvBufferRead).
fn read_zerocopy
  (cb: circular_buffer)
  (read_len: SZ.t)
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer cb st **
    pure (Spec.cb_wf st /\
          SZ.v read_len <= GT.contiguous_prefix_length st.contents /\
          SZ.v read_len <= st.alloc_length /\
          SZ.v read_len > 0)
  returns rv: read_view
  ensures exists* (s1 s2: Seq.seq byte).
    zc_segs rv s1 s2 **
    (zc_segs rv s1 s2 @==> is_circular_buffer cb st) **
    pure (
      SZ.v rv.len1 + SZ.v rv.len2 == SZ.v read_len /\
      SZ.v rv.off1 + SZ.v rv.len1 <= st.alloc_length /\
      SZ.v rv.off2 + SZ.v rv.len2 <= st.alloc_length)

/// RM-mode zero-copy read
fn read_zerocopy_rm
  (cb: circular_buffer)
  (rm: RM.range_map_t)
  (read_len: SZ.t)
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer_rm cb rm st **
    pure (Spec.cb_wf st /\
          SZ.v read_len <= GT.contiguous_prefix_length st.contents /\
          SZ.v read_len <= st.alloc_length /\
          SZ.v read_len > 0)
  returns rv: read_view
  ensures exists* (s1 s2: Seq.seq byte).
    zc_segs rv s1 s2 **
    (zc_segs rv s1 s2 @==> is_circular_buffer_rm cb rm st) **
    pure (
      SZ.v rv.len1 + SZ.v rv.len2 == SZ.v read_len /\
      SZ.v rv.off1 + SZ.v rv.len1 <= st.alloc_length /\
      SZ.v rv.off2 + SZ.v rv.len2 <= st.alloc_length)

/// Release zero-copy read without draining (cancel)
fn release_read
  (cb: circular_buffer)
  (rv: read_view)
  (#st: erased Spec.cb_state)
  (#s1 #s2: erased (Seq.seq byte))
  requires
    zc_segs rv s1 s2 **
    (zc_segs rv s1 s2 @==> is_circular_buffer cb st)
  ensures
    is_circular_buffer cb st

/// Release zero-copy read AND drain
fn drain_after_read
  (cb: circular_buffer)
  (rv: read_view)
  (drain_len: SZ.t)
  (#st: erased Spec.cb_state)
  (#s1 #s2: erased (Seq.seq byte))
  requires
    zc_segs rv s1 s2 **
    (zc_segs rv s1 s2 @==> is_circular_buffer cb st) **
    pure (Spec.cb_wf st /\
          SZ.v drain_len <= st.alloc_length /\
          SZ.v drain_len <= GT.contiguous_prefix_length st.contents /\
          SZ.fits (st.base_offset + SZ.v drain_len))
  returns no_more_data: bool
  ensures
    is_circular_buffer cb (Spec.drain_result st (SZ.v drain_len)) **
    pure (no_more_data == (GT.contiguous_prefix_length st.contents = SZ.v drain_len))

/// RM-mode release zero-copy read
fn release_read_rm
  (cb: circular_buffer)
  (rm: RM.range_map_t)
  (rv: read_view)
  (#st: erased Spec.cb_state)
  (#s1 #s2: erased (Seq.seq byte))
  requires
    zc_segs rv s1 s2 **
    (zc_segs rv s1 s2 @==> is_circular_buffer_rm cb rm st)
  ensures
    is_circular_buffer_rm cb rm st

/// RM-mode release + drain
fn drain_after_read_rm
  (cb: circular_buffer)
  (rm: RM.range_map_t)
  (rv: read_view)
  (drain_len: SZ.t)
  (#st: erased Spec.cb_state)
  (#s1 #s2: erased (Seq.seq byte))
  requires
    zc_segs rv s1 s2 **
    (zc_segs rv s1 s2 @==> is_circular_buffer_rm cb rm st) **
    pure (Spec.cb_wf st /\
          SZ.v drain_len <= st.alloc_length /\
          SZ.v drain_len <= GT.contiguous_prefix_length st.contents /\
          SZ.fits (st.base_offset + SZ.v drain_len))
  returns no_more_data: bool
  ensures
    is_circular_buffer_rm cb rm (Spec.drain_result st (SZ.v drain_len)) **
    pure (no_more_data == (GT.contiguous_prefix_length st.contents = SZ.v drain_len))
