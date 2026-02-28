module Pulse.Lib.CircularBuffer.Spec

/// Specification of the circular buffer (Circular mode, MsQuic recv_buffer.c).
/// Defines state, coherence, operation specs, and the no-overcommit theorem.

module Seq = FStar.Seq
module ML = FStar.Math.Lemmas
module Pow2 = Pulse.Lib.CircularBuffer.Pow2
module Mod = Pulse.Lib.CircularBuffer.Modular
module GT = Pulse.Lib.CircularBuffer.GapTrack

type byte = FStar.UInt8.t

/// --- Physical Index ---

/// Compute the physical array index for logical offset i (always in bounds)
let phys_index (read_start: nat) (i: nat) (al: pos) : Tot (j:nat{j < al}) =
  Mod.circular_index_in_bounds read_start i al;
  (read_start + i) % al

/// --- Buffer State ---

noeq type cb_state = {
  base_offset: nat;
  read_start: nat;
  alloc_length: pos;
  virtual_length: pos;
  contents: Seq.seq (option byte);
}

/// Platform bound on maximum allocatable buffer size (simulates finite memory).
assume val cb_max_length : n:pos{ Pow2.is_pow2 n /\ n <= 0x8000000000000000 }

let cb_wf (st: cb_state) : prop =
  Pow2.is_pow2 st.alloc_length /\
  Pow2.is_pow2 st.virtual_length /\
  st.alloc_length <= st.virtual_length /\
  st.alloc_length <= cb_max_length /\
  st.read_start < st.alloc_length /\
  Seq.length st.contents == st.alloc_length

/// --- Physical-Logical Coherence ---

/// Coherence at a single position
let coherent_at
  (al: pos)
  (phys: Seq.seq byte{Seq.length phys == al})
  (contents: Seq.seq (option byte){Seq.length contents == al})
  (read_start: nat{read_start < al})
  (i: nat{i < al})
  : prop
  = Some? (Seq.index contents i) ==>
    Seq.index phys (phys_index read_start i al) == Some?.v (Seq.index contents i)

/// Full coherence: all positions agree
let phys_log_coherent
  (al: pos)
  (phys: Seq.seq byte{Seq.length phys == al})
  (contents: Seq.seq (option byte){Seq.length contents == al})
  (read_start: nat{read_start < al})
  : prop
  = forall (i:nat{i < al}). coherent_at al phys contents read_start i

/// --- Write Spec ---

/// Writing byte b at logical offset i preserves coherence
let write_preserves_coherence
  (al: pos)
  (phys: Seq.seq byte{Seq.length phys == al})
  (contents: Seq.seq (option byte){Seq.length contents == al})
  (read_start: nat{read_start < al})
  (i: nat{i < al})
  (b: byte)
  : Lemma (requires phys_log_coherent al phys contents read_start)
          (ensures phys_log_coherent al
                    (Seq.upd phys (phys_index read_start i al) b)
                    (Seq.upd contents i (Some b))
                    read_start)
  = let pidx = phys_index read_start i al in
    let new_phys = Seq.upd phys pidx b in
    let new_contents = Seq.upd contents i (Some b) in
    let aux (j:nat{j < al})
      : Lemma (coherent_at al new_phys new_contents read_start j)
      = if j = i then ()
        else Mod.circular_index_injective read_start i j al
    in
    FStar.Classical.forall_intro aux

/// --- Linearize (Resize) Spec ---

/// Construct the linearized physical buffer after resize
let linearized_phys
  (old_al: pos) (new_al: pos)
  (old_phys: Seq.seq byte{Seq.length old_phys == old_al})
  (old_read_start: nat{old_read_start < old_al})
  : Pure (Seq.seq byte)
    (requires new_al >= old_al)
    (ensures fun r -> Seq.length r == new_al)
  = Seq.init new_al (fun k ->
      if k < old_al then Seq.index old_phys (phys_index old_read_start k old_al)
      else 0uy)

/// Extend contents with Nones for new capacity
let resized_contents
  (old_al: pos) (new_al: pos)
  (old_contents: Seq.seq (option byte){Seq.length old_contents == old_al})
  : Pure (Seq.seq (option byte))
    (requires new_al >= old_al)
    (ensures fun r -> Seq.length r == new_al)
  = Seq.init new_al (fun k ->
      if k < old_al then Seq.index old_contents k
      else None)

/// Linearization preserves coherence (read_start resets to 0)
let linearize_preserves_coherence
  (old_al: pos) (new_al: pos)
  (old_phys: Seq.seq byte{Seq.length old_phys == old_al})
  (old_contents: Seq.seq (option byte){Seq.length old_contents == old_al})
  (old_read_start: nat{old_read_start < old_al})
  : Lemma
    (requires
      new_al >= old_al /\
      phys_log_coherent old_al old_phys old_contents old_read_start)
    (ensures
      phys_log_coherent new_al
        (linearized_phys old_al new_al old_phys old_read_start)
        (resized_contents old_al new_al old_contents)
        0)
  = let np = linearized_phys old_al new_al old_phys old_read_start in
    let nc = resized_contents old_al new_al old_contents in
    let aux (j:nat{j < new_al})
      : Lemma (coherent_at new_al np nc 0 j)
      = if j >= old_al then ()
        else begin
          ML.small_mod j new_al;
          assert (coherent_at old_al old_phys old_contents old_read_start j)
        end
    in
    FStar.Classical.forall_intro aux

/// --- Drain Spec ---

/// Drained contents: shift left by n, fill tail with None
let drained_contents
  (al: pos)
  (contents: Seq.seq (option byte){Seq.length contents == al})
  (n: nat{n <= al})
  : Tot (s:Seq.seq (option byte){Seq.length s == al})
  = Seq.init al (fun k ->
      if k + n < al then Seq.index contents (k + n)
      else None)

/// Drain preserves coherence with updated read_start
let drain_preserves_coherence
  (al: pos)
  (phys: Seq.seq byte{Seq.length phys == al})
  (contents: Seq.seq (option byte){Seq.length contents == al})
  (read_start: nat{read_start < al})
  (n: nat{n <= al})
  : Lemma
    (requires phys_log_coherent al phys contents read_start)
    (ensures
      phys_log_coherent al phys
        (drained_contents al contents n)
        (phys_index read_start n al))
  = let new_rs = phys_index read_start n al in
    let nc = drained_contents al contents n in
    let aux (j:nat{j < al})
      : Lemma (coherent_at al phys nc new_rs j)
      = if j + n >= al then ()
        else begin
          Mod.advance_read_start read_start n j al;
          assert (coherent_at al phys contents read_start (j + n))
        end
    in
    FStar.Classical.forall_intro aux

/// --- Drain Prefix Lemma ---

/// After draining n from the front (where n <= cpl), the prefix shrinks by exactly n.
let drain_prefix_length
  (al: pos)
  (contents: Seq.seq (option byte){Seq.length contents == al})
  (n: nat{n <= al})
  : Lemma
    (requires n <= GT.contiguous_prefix_length contents)
    (ensures GT.contiguous_prefix_length (drained_contents al contents n)
             == GT.contiguous_prefix_length contents - n)
  = let cpl = GT.contiguous_prefix_length contents in
    let p = cpl - n in
    let ds = drained_contents al contents n in
    GT.prefix_length_bounded contents;
    // All positions [0, p) of ds are Some
    let aux1 (k:nat{k < p}) : Lemma (Some? (Seq.index ds k))
      = assert (k + n < al);
        assert (Seq.index ds k == Seq.index contents (k + n));
        GT.prefix_elements_are_some contents (k + n)
    in
    FStar.Classical.forall_intro aux1;
    // ds[p] is None (or p == al)
    if p < al then begin
      if cpl < al then begin
        assert (Seq.index ds p == Seq.index contents (p + n));
        assert (p + n == cpl);
        GT.prefix_boundary_is_none contents
      end else begin
        // cpl == al, so p = al - n, and p + n = al >= al, so ds[p] = None
        assert (p + n >= al)
      end
    end else ();
    GT.cpl_characterization ds p

/// --- Resize Prefix Lemma ---

/// After resize (pad with None), prefix is unchanged.
let resize_prefix_length
  (old_al: pos) (new_al: pos)
  (contents: Seq.seq (option byte){Seq.length contents == old_al})
  : Lemma
    (requires new_al >= old_al)
    (ensures GT.contiguous_prefix_length (resized_contents old_al new_al contents)
             == GT.contiguous_prefix_length contents)
  = let cpl = GT.contiguous_prefix_length contents in
    let rc = resized_contents old_al new_al contents in
    GT.prefix_length_bounded contents;
    // All positions [0, cpl) of rc are Some (same as original)
    let aux1 (k:nat{k < cpl}) : Lemma (Some? (Seq.index rc k))
      = assert (k < old_al);
        assert (Seq.index rc k == Seq.index contents k);
        GT.prefix_elements_are_some contents k
    in
    FStar.Classical.forall_intro aux1;
    // rc[cpl] is None (or cpl == new_al)
    if cpl < new_al then begin
      if cpl < old_al then begin
        assert (Seq.index rc cpl == Seq.index contents cpl);
        GT.prefix_boundary_is_none contents
      end else begin
        // cpl == old_al, so rc[cpl] = None (padding)
        assert (Seq.index rc cpl == None)
      end
    end else ();
    GT.cpl_characterization rc cpl

/// --- No-Overcommit Theorem ---

/// For any in-bounds write, there exists a sufficient power-of-2 buffer size
/// that accommodates the write and is at most virtual_length.
/// This is the top-level safety property from recv_buffer.c:
/// "We must always be willing/able to allocate the buffer length advertised to the peer."
let no_overcommit (st: cb_state) (write_end: nat)
  : Lemma
    (requires
      cb_wf st /\
      write_end > st.base_offset /\
      write_end <= st.base_offset + st.virtual_length)
    (ensures
      exists (new_al: pos).
        Pow2.is_pow2 new_al /\
        new_al >= st.alloc_length /\
        new_al <= st.virtual_length /\
        write_end <= st.base_offset + new_al)
  = if write_end <= st.base_offset + st.alloc_length then ()
    else begin
      let needed : pos = write_end - st.base_offset in
      Pow2.doubling_reaches_in_range st.alloc_length st.virtual_length needed
    end

/// --- Total helpers for Pulse interface (no preconditions) ---

/// State after writing a byte (total: no-op if out of bounds)
let write_byte_result (st: cb_state) (i: nat) (b: byte) : cb_state =
  if i < Seq.length st.contents then
    { st with contents = Seq.upd st.contents i (Some b) }
  else st

/// State after draining n bytes (total: no-op if out of bounds)
let drain_result (st: cb_state) (n: nat) : cb_state =
  if n <= st.alloc_length
     && Seq.length st.contents = st.alloc_length
     && st.read_start < st.alloc_length then
    { st with
      base_offset = st.base_offset + n;
      read_start = phys_index st.read_start n st.alloc_length;
      contents = drained_contents st.alloc_length st.contents n }
  else st

/// State after resize (total: no-op if invalid)
let resize_result (st: cb_state) (new_al: pos) : cb_state =
  if new_al >= st.alloc_length && Seq.length st.contents = st.alloc_length then
    { st with
      read_start = 0;
      alloc_length = new_al;
      contents = resized_contents st.alloc_length new_al st.contents }
  else st

/// Transfer coherence across Seq.equal contents
let phys_log_coherent_seq_equal
  (al: pos) (phys: Seq.seq byte{Seq.length phys == al})
  (c1 c2: Seq.seq (option byte))
  (rs: nat{rs < al})
  : Lemma
    (requires Seq.length c1 == al /\ Seq.length c2 == al /\
              phys_log_coherent al phys c1 rs /\ c1 `Seq.equal` c2)
    (ensures phys_log_coherent al phys c2 rs)
  = ()

/// Combined step: write a byte and maintain coherence with write_range_contents
let write_step_coherence
  (al: pos)
  (phys: Seq.seq byte{Seq.length phys == al})
  (contents: Seq.seq (option byte){Seq.length contents == al})
  (rs: nat{rs < al})
  (offset: nat)
  (data: Seq.seq byte)
  (i: nat)
  : Lemma
    (requires offset + Seq.length data <= al /\
             i < Seq.length data /\
             offset + i < al /\
             phys_log_coherent al phys
               (GT.write_range_contents contents offset (Seq.slice data 0 i)) rs)
    (ensures phys_log_coherent al
              (Seq.upd phys (phys_index rs (offset + i) al) (Seq.index data i))
              (GT.write_range_contents contents offset (Seq.slice data 0 (i + 1))) rs)
  = let old_c = GT.write_range_contents contents offset (Seq.slice data 0 i) in
    let b = Seq.index data i in
    write_preserves_coherence al phys old_c rs (offset + i) b;
    GT.write_range_snoc contents offset data i;
    phys_log_coherent_seq_equal al
      (Seq.upd phys (phys_index rs (offset + i) al) b)
      (Seq.upd old_c (offset + i) (Some b))
      (GT.write_range_contents contents offset (Seq.slice data 0 (i + 1)))
      rs

/// --- Read step helper ---
/// Extends the read_buffer loop invariant from k<vi to k<vi+1.
/// Bundles: coherence extraction at vi, Seq.upd reasoning for old/new elements.
let read_step_invariant
  (al: pos)
  (phys: Seq.seq byte{Seq.length phys == al})
  (contents: Seq.seq (option byte){Seq.length contents == al})
  (rs: nat{rs < al})
  (dst: Seq.seq byte) (vi: nat) (byte_val: byte)
  : Lemma
    (requires
      vi < al /\
      vi < Seq.length dst /\
      phys_log_coherent al phys contents rs /\
      Some? (Seq.index contents vi) /\
      byte_val == Seq.index phys (phys_index rs vi al) /\
      (forall (k:nat{k < vi}).
        Some? (Seq.index contents k) /\
        Seq.index dst k == Some?.v (Seq.index contents k)))
    (ensures (
      let dst' = Seq.upd dst vi byte_val in
      forall (k:nat{k < vi + 1}).
        Some? (Seq.index contents k) /\
        Seq.index dst' k == Some?.v (Seq.index contents k)))
  = let dst' = Seq.upd dst vi byte_val in
    let aux (k:nat{k < vi + 1})
      : Lemma (Some? (Seq.index contents k) /\
               Seq.index dst' k == Some?.v (Seq.index contents k))
      = if k < vi then
          // Old element: upd at vi doesn't affect index k
          Seq.lemma_index_upd2 dst vi byte_val k
        else begin
          // New element: k == vi; byte_val from coherent_at via phys_log_coherent
          Seq.lemma_index_upd1 dst vi byte_val;
          assert (coherent_at al phys contents rs vi)
        end
    in
    FStar.Classical.forall_intro aux

/// --- Zero-copy read segment computation ---

/// A pair of physical segments for zero-copy read.
/// seg1 is [off1, off1+len1), seg2 is [off2, off2+len2) (possibly empty).
noeq type read_segments = {
  off1: nat;
  len1: nat;
  off2: nat;
  len2: nat;
}

/// Compute the physical segment boundaries for reading n bytes starting at read_start.
/// If the read wraps around: seg1 = [rs, al), seg2 = [0, n - (al - rs))
/// If no wrap:               seg1 = [rs, rs+n), seg2 = empty
let compute_read_segments (rs: nat) (n: nat) (al: pos)
  : Pure read_segments
    (requires rs < al /\ n <= al)
    (ensures fun segs ->
      segs.off1 == rs /\
      segs.len1 + segs.len2 == n /\
      segs.off1 + segs.len1 <= al /\
      segs.off2 + segs.len2 <= al /\
      (segs.len2 > 0 ==> segs.off2 == 0) /\
      (segs.len2 == 0 ==> segs.off1 + segs.len1 == rs + n))
  = if rs + n <= al then
      { off1 = rs; len1 = n; off2 = 0; len2 = 0 }
    else
      { off1 = rs; len1 = al - rs; off2 = 0; len2 = n - (al - rs) }

/// The physical bytes for segment 1 match the logical contents.
/// phys[off1..off1+len1) corresponds to contents[0..len1) via coherence.
let read_segments_seg1_correct
  (al: pos) (phys: Seq.seq byte{Seq.length phys == al})
  (contents: Seq.seq (option byte){Seq.length contents == al})
  (rs: nat{rs < al}) (n: nat{n <= al})
  (cpl: nat{cpl >= n})
  : Lemma
    (requires
      phys_log_coherent al phys contents rs /\
      cpl <= GT.contiguous_prefix_length contents)
    (ensures (
      let segs = compute_read_segments rs n al in
      forall (i:nat{i < segs.len1}).
        Some? (Seq.index contents i) /\
        Seq.index phys (segs.off1 + i) == Some?.v (Seq.index contents i)))
  = let segs = compute_read_segments rs n al in
    let aux (i:nat{i < segs.len1})
      : Lemma (Some? (Seq.index contents i) /\
               Seq.index phys (segs.off1 + i) == Some?.v (Seq.index contents i))
      = GT.prefix_elements_are_some contents i;
        assert (coherent_at al phys contents rs i);
        Mod.circular_index_in_bounds rs i al;
        // phys_index rs i al == (rs + i) % al
        // Since i < len1 and off1 = rs, off1 + i = rs + i
        // No wrap case: rs + i < al, so (rs + i) % al = rs + i = off1 + i
        // Wrap case: i < al - rs, so rs + i < al, so (rs + i) % al = rs + i = off1 + i
        ML.small_mod (rs + i) al
    in
    FStar.Classical.forall_intro aux

/// The physical bytes for segment 2 match the logical contents.
/// phys[0..len2) corresponds to contents[len1..len1+len2) via coherence.
let read_segments_seg2_correct
  (al: pos) (phys: Seq.seq byte{Seq.length phys == al})
  (contents: Seq.seq (option byte){Seq.length contents == al})
  (rs: nat{rs < al}) (n: nat{n <= al})
  (cpl: nat{cpl >= n})
  : Lemma
    (requires
      phys_log_coherent al phys contents rs /\
      cpl <= GT.contiguous_prefix_length contents)
    (ensures (
      let segs = compute_read_segments rs n al in
      forall (i:nat{i < segs.len2}).
        Some? (Seq.index contents (segs.len1 + i)) /\
        Seq.index phys (segs.off2 + i) == Some?.v (Seq.index contents (segs.len1 + i))))
  = let segs = compute_read_segments rs n al in
    if segs.len2 = 0 then ()
    else
      let aux (i:nat{i < segs.len2})
        : Lemma (Some? (Seq.index contents (segs.len1 + i)) /\
                 Seq.index phys (segs.off2 + i) == Some?.v (Seq.index contents (segs.len1 + i)))
        = let li = segs.len1 + i in
          GT.prefix_elements_are_some contents li;
          assert (coherent_at al phys contents rs li);
          Mod.circular_index_in_bounds rs li al;
          // phys_index rs li al == (rs + li) % al
          // li = (al - rs) + i, so rs + li = al + i
          // (al + i) % al = i = off2 + i (since off2 = 0)
          ML.lemma_mod_plus i 1 al;
          assert ((rs + li) % al == i)
      in
      FStar.Classical.forall_intro aux

/// Combined: both segments are correct
let read_segments_correct
  (al: pos) (phys: Seq.seq byte{Seq.length phys == al})
  (contents: Seq.seq (option byte){Seq.length contents == al})
  (rs: nat{rs < al}) (n: nat{n <= al})
  (cpl: nat{cpl >= n})
  : Lemma
    (requires
      phys_log_coherent al phys contents rs /\
      cpl <= GT.contiguous_prefix_length contents)
    (ensures (
      let segs = compute_read_segments rs n al in
      // Segment 1 data matches
      (forall (i:nat{i < segs.len1}).
        Some? (Seq.index contents i) /\
        Seq.index phys (segs.off1 + i) == Some?.v (Seq.index contents i)) /\
      // Segment 2 data matches
      (forall (i:nat{i < segs.len2}).
        Some? (Seq.index contents (segs.len1 + i)) /\
        Seq.index phys (segs.off2 + i) == Some?.v (Seq.index contents (segs.len1 + i)))))
  = read_segments_seg1_correct al phys contents rs n cpl;
    read_segments_seg2_correct al phys contents rs n cpl

/// Slice equality: phys[off1..off1+len1) == the logical bytes for [0..len1)
let read_segments_slice_eq
  (al: pos) (phys: Seq.seq byte{Seq.length phys == al})
  (contents: Seq.seq (option byte){Seq.length contents == al})
  (rs: nat{rs < al}) (n: nat{n <= al})
  (cpl: nat{cpl >= n})
  : Lemma
    (requires
      phys_log_coherent al phys contents rs /\
      cpl <= GT.contiguous_prefix_length contents)
    (ensures (
      let segs = compute_read_segments rs n al in
      let s1 = Seq.slice phys segs.off1 (segs.off1 + segs.len1) in
      let s2 = Seq.slice phys segs.off2 (segs.off2 + segs.len2) in
      // Each byte in s1 matches the logical contents
      (forall (i:nat{i < segs.len1}).
        Some? (Seq.index contents i) /\
        Seq.index s1 i == Some?.v (Seq.index contents i)) /\
      // Each byte in s2 matches the logical contents
      (forall (i:nat{i < segs.len2}).
        Some? (Seq.index contents (segs.len1 + i)) /\
        Seq.index s2 i == Some?.v (Seq.index contents (segs.len1 + i)))))
  = read_segments_correct al phys contents rs n cpl;
    let segs = compute_read_segments rs n al in
    let aux1 (i:nat{i < segs.len1})
      : Lemma (Seq.index (Seq.slice phys segs.off1 (segs.off1 + segs.len1)) i
               == Seq.index phys (segs.off1 + i))
      = Seq.lemma_index_slice phys segs.off1 (segs.off1 + segs.len1) i
    in
    FStar.Classical.forall_intro aux1;
    let aux2 (i:nat{i < segs.len2})
      : Lemma (Seq.index (Seq.slice phys segs.off2 (segs.off2 + segs.len2)) i
               == Seq.index phys (segs.off2 + i))
      = Seq.lemma_index_slice phys segs.off2 (segs.off2 + segs.len2) i
    in
    FStar.Classical.forall_intro aux2

/// --- Out-of-order write helpers ---

/// cb_wf is preserved by write_range_contents (contents length unchanged)
let write_range_preserves_wf
  (st: cb_state) (offset: nat) (data: Seq.seq byte)
  : Lemma
    (requires cb_wf st /\ offset + Seq.length data <= st.alloc_length)
    (ensures cb_wf { st with contents = GT.write_range_contents st.contents offset data })
  = ()

/// Transfer coherence from Seq.slice to full data for OOO write (no-resize case)
let write_ooo_coherence_transfer
  (al: pos) (phys: Seq.seq byte{Seq.length phys == al})
  (contents: Seq.seq (option byte){Seq.length contents == al})
  (rs: nat{rs < al})
  (offset: nat) (data: Seq.seq byte) (n: nat) (write_len: nat)
  : Lemma
    (requires
      n <= write_len /\
      write_len == Seq.length data /\
      false == (n < write_len) /\
      offset + write_len <= al /\
      phys_log_coherent al phys
        (GT.write_range_contents contents offset (Seq.slice data 0 n))
        rs)
    (ensures
      phys_log_coherent al phys
        (GT.write_range_contents contents offset data)
        rs)
  = assert (n == Seq.length data);
    Seq.lemma_eq_intro (Seq.slice data 0 n) data;
    Seq.lemma_eq_elim (Seq.slice data 0 n) data

/// --- RangeMap ↔ Contents Bridge ---

module RMSpec = Pulse.Lib.RangeMap.Spec

/// Bridge: RangeMap intervals (absolute offsets) match the option-byte contents.
/// Intervals use absolute stream positions; contents is indexed relative to base_offset.
/// For every position i, mem repr (base_offset + i) <==> Some? contents[i].
/// All interval endpoints are bounded by base_offset + Seq.length contents.
let ranges_match_contents
  (repr: Seq.seq RMSpec.interval)
  (contents: Seq.seq (option byte))
  (base_offset: nat) : prop =
  Seq.length contents > 0 /\
  (forall (i:nat{i < Seq.length contents}).
    RMSpec.mem repr (base_offset + i) <==> Some? (Seq.index contents i)) /\
  RMSpec.range_map_bounded repr (base_offset + Seq.length contents)

/// base_offset is within the first interval (or repr is empty).
/// Invariant of the CircularBuffer: first interval starts at 0 and base_offset
/// only advances by drain (contiguous_from), so it stays within the first interval.
let base_aligned (repr: Seq.seq RMSpec.interval) (base_offset: nat) : prop =
  Seq.length repr = 0 \/
  (let first = Seq.index repr 0 in first.low <= base_offset /\ base_offset <= RMSpec.high first)

/// Empty repr matches all-None contents (base_offset = 0), and is trivially base_aligned.
let ranges_match_empty (al: pos)
  : Lemma (ranges_match_contents Seq.empty (Seq.create al (None #byte)) 0 /\
           base_aligned Seq.empty 0)
  = let contents : Seq.seq (option byte) = Seq.create al None in
    let aux (i:nat{i < Seq.length contents})
      : Lemma (RMSpec.mem Seq.empty (0 + i) <==> Some? (Seq.index contents i))
      = ()
    in
    FStar.Classical.forall_intro aux

/// Writing data preserves the bridge.
/// add_range uses absolute offset (base_offset + rel_offset).
let ranges_match_write
  (repr: Seq.seq RMSpec.interval)
  (contents: Seq.seq (option byte))
  (base_offset: nat) (rel_offset: nat) (data: Seq.seq byte)
  : Lemma
    (requires
      ranges_match_contents repr contents base_offset /\
      Seq.length data > 0 /\
      rel_offset + Seq.length data <= Seq.length contents)
    (ensures
      ranges_match_contents
        (RMSpec.add_range repr (base_offset + rel_offset) (Seq.length data))
        (GT.write_range_contents contents rel_offset data)
        base_offset)
  = let len = Seq.length data in
    let abs_offset = base_offset + rel_offset in
    let new_repr = RMSpec.add_range repr abs_offset len in
    let new_contents = GT.write_range_contents contents rel_offset data in
    let aux (i:nat{i < Seq.length new_contents})
      : Lemma (RMSpec.mem new_repr (base_offset + i) <==> Some? (Seq.index new_contents i))
      = GT.write_range_index contents rel_offset data i;
        let abs_i = base_offset + i in
        if rel_offset <= i && i < rel_offset + len then (
          assert (abs_offset <= abs_i && abs_i < abs_offset + len);
          RMSpec.add_range_mem_new repr abs_offset len abs_i
        ) else (
          assert (Seq.index new_contents i == Seq.index contents i);
          assert (not (abs_offset <= abs_i && abs_i < abs_offset + len));
          if Some? (Seq.index contents i) then (
            assert (RMSpec.mem repr abs_i);
            RMSpec.add_range_mem_old repr abs_offset len abs_i
          ) else ();
          if RMSpec.mem new_repr abs_i then (
            RMSpec.add_range_mem_inv repr abs_offset len abs_i;
            assert (RMSpec.mem repr abs_i)
          ) else ()
        )
    in
    FStar.Classical.forall_intro aux;
    RMSpec.add_range_bounded repr abs_offset len (base_offset + Seq.length contents)

/// Resize preserves the bridge: extending contents with Nones doesn't break the correspondence.
let ranges_match_resize
  (repr: Seq.seq RMSpec.interval)
  (contents: Seq.seq (option byte))
  (base_offset: nat)
  (old_al: pos) (new_al: pos)
  : Lemma
    (requires
      ranges_match_contents repr contents base_offset /\
      Seq.length contents == old_al /\
      new_al >= old_al)
    (ensures
      ranges_match_contents repr (resized_contents old_al new_al contents) base_offset)
  = let new_c = resized_contents old_al new_al contents in
    let aux (i:nat{i < Seq.length new_c})
      : Lemma (RMSpec.mem repr (base_offset + i) <==> Some? (Seq.index new_c i))
      = if i < old_al then ()
        else RMSpec.mem_bounded repr (base_offset + old_al) (base_offset + i)
    in
    FStar.Classical.forall_intro aux;
    RMSpec.range_map_bounded_monotone repr (base_offset + old_al) (base_offset + new_al)

/// Lower bound: contiguous_from is always <= contiguous_prefix_length.
/// Does NOT require base_aligned. When base_aligned holds, use ranges_match_prefix for equality.
let ranges_match_prefix_lower
  (repr: Seq.seq RMSpec.interval)
  (contents: Seq.seq (option byte))
  (base_offset: nat)
  : Lemma
    (requires ranges_match_contents repr contents base_offset /\
             RMSpec.range_map_wf repr)
    (ensures RMSpec.contiguous_from repr base_offset <= GT.contiguous_prefix_length contents)
  = RMSpec.cf_bounded repr base_offset (base_offset + Seq.length contents);
    let cf = RMSpec.contiguous_from repr base_offset in
    GT.prefix_length_bounded contents;
    if cf > 0 then (
      let first = Seq.index repr 0 in
      assert (first.low <= base_offset /\ base_offset < RMSpec.high first);
      assert (cf == RMSpec.high first - base_offset);
      assert (cf <= Seq.length contents);
      let aux (i:nat{i < cf})
        : Lemma (Some? (Seq.index contents i))
        = assert (i < Seq.length contents);
          assert (base_offset + i < RMSpec.high first);
          assert (first.low <= base_offset + i);
          assert (RMSpec.in_interval first (base_offset + i));
          assert (RMSpec.mem repr (base_offset + i))
      in
      FStar.Classical.forall_intro aux;
      GT.all_some_prefix_ge contents cf
    ) else ()

/// Prefix equivalence: under the bridge + base_aligned,
/// contiguous_from(repr, base_offset) == contiguous_prefix_length(contents).
#push-options "--z3rlimit_factor 4 --fuel 2 --ifuel 1"
let ranges_match_prefix
  (repr: Seq.seq RMSpec.interval)
  (contents: Seq.seq (option byte))
  (base_offset: nat)
  : Lemma
    (requires ranges_match_contents repr contents base_offset /\
             RMSpec.range_map_wf repr /\
             base_aligned repr base_offset)
    (ensures RMSpec.contiguous_from repr base_offset == GT.contiguous_prefix_length contents)
  = RMSpec.cf_bounded repr base_offset (base_offset + Seq.length contents);
    let cf = RMSpec.contiguous_from repr base_offset in
    let cpl = GT.contiguous_prefix_length contents in
    GT.prefix_length_bounded contents;
    // Direction 1: cf <= cpl
    if cf > 0 then (
      let first = Seq.index repr 0 in
      assert (first.low <= base_offset /\ base_offset < RMSpec.high first);
      assert (cf == RMSpec.high first - base_offset);
      assert (cf <= Seq.length contents);
      let aux (i:nat{i < cf})
        : Lemma (Some? (Seq.index contents i))
        = assert (i < Seq.length contents);
          assert (base_offset + i < RMSpec.high first);
          assert (first.low <= base_offset + i);
          assert (RMSpec.in_interval first (base_offset + i));
          assert (RMSpec.mem repr (base_offset + i))
      in
      FStar.Classical.forall_intro aux;
      GT.all_some_prefix_ge contents cf
    ) else ();
    // Direction 2: cpl <= cf (by contradiction: assume cpl > cf, derive false)
    if cpl > cf then (
      GT.prefix_elements_are_some contents cf;
      assert (Some? (Seq.index contents cf));
      assert (RMSpec.mem repr (base_offset + cf));
      if Seq.length repr = 0 then ()
      else (
        let first = Seq.index repr 0 in
        // From base_aligned: first.low <= base_offset <= high first
        if first.low <= base_offset && base_offset < RMSpec.high first then (
          // cf = high first - base_offset, so base_offset + cf = high first
          // high first is NOT in the first interval (boundary), so must be in tail
          assert (not (RMSpec.in_interval first (base_offset + cf)));
          RMSpec.mem_tail repr (base_offset + cf);
          if Seq.length (Seq.tail repr) > 0 then
            // tail membership implies position > high first, but position = high first
            RMSpec.mem_wf_tail_gt repr (base_offset + cf)
          else ()
        ) else (
          // first.low <= base_offset (from base_aligned) AND NOT (base_offset < high first)
          // AND base_offset <= high first (from base_aligned)
          // Therefore base_offset = high first, and cf = 0
          assert (base_offset == RMSpec.high first);
          assert (not (RMSpec.in_interval first base_offset));
          RMSpec.mem_tail repr base_offset;
          if Seq.length (Seq.tail repr) > 0 then
            // tail membership implies position > high first = base_offset, contradiction
            RMSpec.mem_wf_tail_gt repr base_offset
          else ()
        )
      )
    ) else ()
#pop-options

/// Drain preservation: the bridge is automatically preserved by index substitution.
let ranges_match_drain
  (repr: Seq.seq RMSpec.interval)
  (contents: Seq.seq (option byte))
  (base_offset: nat) (n: nat)
  : Lemma
    (requires ranges_match_contents repr contents base_offset /\
             n <= Seq.length contents /\
             Seq.length contents - n > 0)
    (ensures ranges_match_contents repr (Seq.slice contents n (Seq.length contents)) (base_offset + n))
  = let new_contents = Seq.slice contents n (Seq.length contents) in
    let new_base = base_offset + n in
    let aux (i:nat{i < Seq.length new_contents})
      : Lemma (RMSpec.mem repr (new_base + i) <==> Some? (Seq.index new_contents i))
      = assert (new_base + i == base_offset + (n + i));
        assert (Seq.index new_contents i == Seq.index contents (n + i))
    in
    FStar.Classical.forall_intro aux;
    assert (base_offset + Seq.length contents == new_base + Seq.length new_contents)

/// Drain with padding: bridge preserved for drained_contents (slice + None padding).
/// This is what the actual CircularBuffer drain uses (keeps length = alloc_length).
#push-options "--z3rlimit_factor 2"
let ranges_match_drain_padded
  (repr: Seq.seq RMSpec.interval)
  (contents: Seq.seq (option byte))
  (base_offset: nat) (n: nat)
  : Lemma
    (requires ranges_match_contents repr contents base_offset /\
             n <= Seq.length contents)
    (ensures ranges_match_contents repr
               (drained_contents (Seq.length contents) contents n)
               (base_offset + n))
  = let al = Seq.length contents in
    let new_contents = drained_contents al contents n in
    let new_base = base_offset + n in
    assert (Seq.length new_contents == al);
    assert (al > 0);
    let aux (i:nat{i < al})
      : Lemma (RMSpec.mem repr (new_base + i) <==> Some? (Seq.index new_contents i))
      = if i < al - n then (
          // Position in sliced region: new_contents[i] = contents[n + i]
          assert (Seq.index new_contents i == Seq.index contents (n + i));
          assert (new_base + i == base_offset + (n + i));
          assert (n + i < al)
        ) else (
          // Position in padding region: new_contents[i] = None
          assert (Seq.index new_contents i == None #byte);
          // base_offset + (n + i) >= base_offset + al, beyond all intervals
          assert (new_base + i == base_offset + (n + i));
          assert (n + i >= al);
          RMSpec.mem_bounded repr (base_offset + al) (base_offset + (n + i))
        )
    in
    FStar.Classical.forall_intro aux;
    // Bounded: old bound (base_offset + al) <= new bound (base_offset + n + al)
    RMSpec.range_map_bounded_monotone repr (base_offset + al) (base_offset + n + al)
#pop-options

/// Drain repr bridge: drain_repr preserves ranges_match_contents with new base
let ranges_match_drain_repr
  (repr: Seq.seq RMSpec.interval)
  (contents: Seq.seq (option byte))
  (base_offset: nat) (n: nat)
  : Lemma
    (requires ranges_match_contents repr contents base_offset /\
             RMSpec.range_map_wf repr /\
             base_aligned repr base_offset /\
             n <= RMSpec.contiguous_from repr base_offset /\
             n <= Seq.length contents)
    (ensures ranges_match_contents
               (RMSpec.drain_repr repr (base_offset + n))
               (drained_contents (Seq.length contents) contents n)
               (base_offset + n))
  = let al = Seq.length contents in
    let new_bo = base_offset + n in
    let new_contents = drained_contents al contents n in
    let new_repr = RMSpec.drain_repr repr new_bo in
    // First: original bridge after drain (using unchanged repr)
    ranges_match_drain_padded repr contents base_offset n;
    // So: ranges_match_contents repr new_contents new_bo
    // Now show: drain_repr preserves mem for positions >= new_bo
    if Seq.length repr = 0 then ()
    else begin
      let first = Seq.index repr 0 in
      assert (first.low <= base_offset);
      assert (base_offset <= RMSpec.high first);
      assert (new_bo <= RMSpec.high first);
      // drain_repr_mem_above: for x >= new_bo, mem new_repr x == mem repr x
      let aux (i:nat{i < al})
        : Lemma (RMSpec.mem new_repr (new_bo + i) <==> Some? (Seq.index new_contents i))
        = RMSpec.drain_repr_mem_above repr new_bo (new_bo + i)
      in
      FStar.Classical.forall_intro aux;
      // Bounded
      RMSpec.drain_repr_bounded repr new_bo (base_offset + al);
      RMSpec.range_map_bounded_monotone new_repr (base_offset + al) (new_bo + al)
    end

/// Drain preserves base_aligned when draining at most contiguous_from bytes.
let drain_preserves_base_aligned
  (repr: Seq.seq RMSpec.interval)
  (base_offset: nat) (n: nat)
  : Lemma
    (requires base_aligned repr base_offset /\
             n <= RMSpec.contiguous_from repr base_offset)
    (ensures base_aligned repr (base_offset + n))
  = if Seq.length repr = 0 then ()
    else (
      let first = Seq.index repr 0 in
      if first.low <= base_offset && base_offset < RMSpec.high first then (
        assert (RMSpec.contiguous_from repr base_offset == RMSpec.high first - base_offset);
        assert (base_offset + n <= RMSpec.high first)
      ) else (
        assert (base_offset + n == base_offset)
      )
    )


/// 3-way invariant: empty, gap (first starts after base), or base_aligned.
/// Excludes the unreachable case where first starts at/before base but base is past the end.
let repr_well_positioned (repr: Seq.seq RMSpec.interval) (base_offset: nat) : prop =
  Seq.length repr = 0 \/
  (Seq.index repr 0).low > base_offset \/
  ((Seq.index repr 0).low <= base_offset /\ base_offset <= RMSpec.high (Seq.index repr 0))

/// repr_well_positioned subsumes base_aligned
let base_aligned_implies_rwp (repr: Seq.seq RMSpec.interval) (base_offset: nat)
  : Lemma (requires base_aligned repr base_offset)
          (ensures repr_well_positioned repr base_offset) = ()

/// Empty repr matches create_nones contents (base_offset = 0), with all invariants.
let ranges_match_create_nones (al: pos)
  : Lemma (ranges_match_contents Seq.empty (GT.create_nones al) 0 /\
           RMSpec.range_map_wf Seq.empty /\
           repr_well_positioned Seq.empty 0)
  = let contents = GT.create_nones al in
    let aux (i:nat{i < Seq.length contents})
      : Lemma (RMSpec.mem Seq.empty (0 + i) <==> Some? (Seq.index contents i))
      = GT.create_nones_all_none al i
    in
    FStar.Classical.forall_intro aux

/// repr_well_positioned implies cf == cpl (the key property for drain_rm postconditions)
let rwp_cf_eq_cpl
  (repr: Seq.seq RMSpec.interval)
  (contents: Seq.seq (option byte))
  (base_offset: nat)
  : Lemma
    (requires ranges_match_contents repr contents base_offset /\
             RMSpec.range_map_wf repr /\
             repr_well_positioned repr base_offset)
    (ensures RMSpec.contiguous_from repr base_offset == GT.contiguous_prefix_length contents)
  = if Seq.length repr = 0 then (
      // Empty repr: no members, all None
      ranges_match_prefix repr contents base_offset
    ) else if (Seq.index repr 0).low > base_offset then (
      // Gap state: first starts after base
      // cf = 0 (first doesn't cover base)
      assert (RMSpec.contiguous_from repr base_offset == 0);
      // position base_offset is not a member (below first.low, which is the lowest)
      // So contents[0] = None, hence cpl = 0
      let first = Seq.index repr 0 in
      assert (not (RMSpec.in_interval first base_offset));
      RMSpec.mem_not_below_first repr base_offset;
      assert (not (RMSpec.mem repr base_offset));
      // contents[0] = None since mem repr (base_offset + 0) = false
      assert (Seq.length contents > 0);
      // cpl = 0 since contents[0] = None (from ranges_match_contents + non-membership)
      assert (not (Some? (Seq.index contents 0)));
      assert (GT.contiguous_prefix_length contents == 0)
    ) else (
      // base_aligned: first.low <= base_offset <= high first
      ranges_match_prefix repr contents base_offset
    )

/// Write preserves repr_well_positioned
let write_preserves_rwp
  (repr: Seq.seq RMSpec.interval) (base_offset: nat) (rel_offset: nat) (len: pos)
  : Lemma
    (requires RMSpec.range_map_wf repr /\
             repr_well_positioned repr base_offset)
    (ensures repr_well_positioned (RMSpec.add_range repr (base_offset + rel_offset) len) base_offset)
  = let offset = base_offset + rel_offset in
    let r = RMSpec.add_range repr offset len in
    if Seq.length repr = 0 then (
      // Empty repr: add creates [{offset, len}]
      if rel_offset = 0 then
        // Write at base: new first at base, base_aligned
        RMSpec.add_range_at_base_establishes_aligned repr base_offset len
      else
        // Gap write: new first at offset > base
        RMSpec.add_range_preserves_gap repr base_offset offset len
    ) else if (Seq.index repr 0).low > base_offset then (
      // Gap state
      if rel_offset = 0 then
        // Write at base into gap state: establishes base_aligned
        RMSpec.add_range_at_base_establishes_aligned repr base_offset len
      else
        // Gap write: offset > base_offset, preserves gap
        RMSpec.add_range_preserves_gap repr base_offset offset len
    ) else (
      // base_aligned: first.low <= base_offset <= high first
      // offset = base_offset + rel_offset >= base_offset >= first.low
      RMSpec.add_range_base_aligned repr base_offset offset len
    )

/// Drain preserves repr_well_positioned
let drain_preserves_rwp
  (repr: Seq.seq RMSpec.interval) (base_offset: nat) (n: nat)
  : Lemma
    (requires repr_well_positioned repr base_offset /\
             n <= RMSpec.contiguous_from repr base_offset)
    (ensures repr_well_positioned repr (base_offset + n))
  = if Seq.length repr = 0 then ()
    else if (Seq.index repr 0).low > base_offset then (
      // Gap state: cf = 0, n = 0
      assert (RMSpec.contiguous_from repr base_offset == 0);
      assert (n == 0)
    ) else (
      // base_aligned: drain preserves it
      drain_preserves_base_aligned repr base_offset n
    )

/// drain_repr preserves repr_well_positioned with new base
let drain_repr_preserves_rwp
  (repr: Seq.seq RMSpec.interval) (base_offset: nat) (n: nat)
  : Lemma
    (requires repr_well_positioned repr base_offset /\
             RMSpec.range_map_wf repr /\
             base_aligned repr base_offset /\
             n <= RMSpec.contiguous_from repr base_offset)
    (ensures repr_well_positioned (RMSpec.drain_repr repr (base_offset + n)) (base_offset + n))
  = if Seq.length repr = 0 then ()
    else
      let first = Seq.index repr 0 in
      let new_bo = base_offset + n in
      let result = RMSpec.drain_repr repr new_bo in
      if RMSpec.high first <= new_bo then begin
        let tl = Seq.tail repr in
        if Seq.length tl = 0 then ()
        else begin
          let next = Seq.index tl 0 in
          assert (Seq.index repr 1 == next);
          assert (RMSpec.separated first next);
          assert (next.low > RMSpec.high first);
          assert (next.low > new_bo);
          assert (Seq.index result 0 == next)
        end
      end else if first.low < new_bo then begin
        let trimmed = { RMSpec.low = new_bo; RMSpec.count = RMSpec.high first - new_bo } in
        assert (Seq.index result 0 == trimmed);
        assert (trimmed.low == new_bo);
        assert (new_bo <= RMSpec.high trimmed)
      end else
        assert (new_bo == base_offset)

/// Master lemma: write preserves cf == cpl under the 3-way invariant
#push-options "--z3rlimit_factor 2"
let write_preserves_cf_eq_cpl
  (repr: Seq.seq RMSpec.interval)
  (contents: Seq.seq (option byte))
  (base_offset: nat)
  (rel_offset: nat)
  (data: Seq.seq byte)
  : Lemma
    (requires
      ranges_match_contents repr contents base_offset /\
      RMSpec.range_map_wf repr /\
      repr_well_positioned repr base_offset /\
      RMSpec.contiguous_from repr base_offset == GT.contiguous_prefix_length contents /\
      Seq.length data > 0 /\
      rel_offset + Seq.length data <= Seq.length contents)
    (ensures (
      let new_repr = RMSpec.add_range repr (base_offset + rel_offset) (Seq.length data) in
      let new_contents = GT.write_range_contents contents rel_offset data in
      RMSpec.contiguous_from new_repr base_offset ==
        GT.contiguous_prefix_length new_contents))
  = let len = Seq.length data in
    let new_repr = RMSpec.add_range repr (base_offset + rel_offset) len in
    let new_contents = GT.write_range_contents contents rel_offset data in
    // Prove preservation of ranges_match_contents and wf for new state
    ranges_match_write repr contents base_offset rel_offset data;
    RMSpec.add_range_wf repr (base_offset + rel_offset) len;
    // Prove repr_well_positioned for new state
    write_preserves_rwp repr base_offset rel_offset len;
    // Use rwp_cf_eq_cpl on new state
    rwp_cf_eq_cpl new_repr new_contents base_offset
#pop-options

/// --- Trim Write (for absolute-offset API) ---

/// Trim a write to remove bytes before base_offset (already consumed).
/// Returns (relative_offset, trimmed_data_length, skip_count).
/// skip_count is the number of leading bytes to skip from src.
let trim_write_params (abs_offset: nat) (write_len: nat) (base_offset: nat)
  : (nat & nat & nat)   // (rel_offset, trimmed_len, skip)
  = let abs_end = abs_offset + write_len in
    if abs_end <= base_offset then (0, 0, 0)   // fully stale — no bytes to write
    else if abs_offset >= base_offset then
      (abs_offset - base_offset, write_len, 0)  // no overlap — all bytes valid
    else
      let skip = base_offset - abs_offset in    // partial overlap — skip consumed prefix
      (0, write_len - skip, skip)

/// Stale check: true if the entire write is before base_offset
let is_stale_write (abs_offset: nat) (write_len: nat) (base_offset: nat) : bool =
  abs_offset + write_len <= base_offset

/// After trimming, the relative offset + trimmed length fits in alloc_length
/// if the original absolute write fits in base_offset + alloc_length.
let trim_write_in_bounds
  (abs_offset: nat) (write_len: nat) (base_offset: nat) (alloc_length: nat)
  : Lemma
    (requires
      write_len > 0 /\
      abs_offset + write_len <= base_offset + alloc_length /\
      not (is_stale_write abs_offset write_len base_offset))
    (ensures (
      let (rel_off, tlen, skip) = trim_write_params abs_offset write_len base_offset in
      rel_off + tlen <= alloc_length /\
      skip + tlen == write_len /\
      tlen > 0))
  = ()

/// The trimmed write produces the same logical result as writing only the
/// non-stale portion: write_range_contents at rel_offset with data[skip..].
let trim_write_equiv
  (abs_offset: nat) (write_len: nat) (base_offset: nat)
  (contents: Seq.seq (option byte)) (data: Seq.seq byte)
  : Lemma
    (requires
      Seq.length data == write_len /\
      not (is_stale_write abs_offset write_len base_offset) /\
      (let (rel_off, tlen, skip) = trim_write_params abs_offset write_len base_offset in
       rel_off + tlen <= Seq.length contents))
    (ensures (
      let (rel_off, tlen, skip) = trim_write_params abs_offset write_len base_offset in
      GT.write_range_contents_t contents rel_off (Seq.slice data skip (skip + tlen)) ==
      GT.write_range_contents contents rel_off (Seq.slice data skip (skip + tlen))))
  = let (rel_off, tlen, skip) = trim_write_params abs_offset write_len base_offset in
    GT.write_range_contents_t_eq contents rel_off (Seq.slice data skip (skip + tlen))

/// Needed resize size: smallest pow2 >= abs_end - base_offset
let needed_alloc_for_write (abs_offset: nat) (write_len: nat) (base_offset: nat) : nat =
  if abs_offset + write_len <= base_offset then 0
  else abs_offset + write_len - base_offset

/// Count bound: when repr starts at/after base_offset, the count is bounded.
/// In gap case (first.low > bo): 2n <= al
/// In base_aligned case (first.low <= bo): 2n <= bo + al - first.low + 1
/// For the write fold site, we only use the gap case + the empty case.
let repr_count_bound_gap
  (repr: Seq.seq RMSpec.interval) (base_offset: nat) (al: pos)
  : Lemma
    (requires RMSpec.range_map_wf repr /\
             RMSpec.range_map_bounded repr (base_offset + al) /\
             Seq.length repr > 0 /\
             (Seq.index repr 0).low >= base_offset)
    (ensures Seq.length repr + Seq.length repr <= al + 1)
  = RMSpec.wf_count_bound repr base_offset (base_offset + al)
