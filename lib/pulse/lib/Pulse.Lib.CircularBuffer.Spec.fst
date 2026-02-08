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

let cb_wf (st: cb_state) : prop =
  Pow2.is_pow2 st.alloc_length /\
  Pow2.is_pow2 st.virtual_length /\
  st.alloc_length <= st.virtual_length /\
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
let write_result (st: cb_state) (i: nat) (b: byte) : cb_state =
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

/// --- Gapless Property (for sequential writes) ---

/// A gapless buffer has all positions >= prefix as None
let gapless (st: cb_state) : prop =
  let pl = GT.contiguous_prefix_length st.contents in
  forall (i:nat). (i >= pl /\ i < Seq.length st.contents) ==> None? (Seq.index st.contents i)

/// Writing at the prefix position in a gapless buffer gives prefix + 1
let gapless_write_extends_prefix
  (al: pos)
  (contents: Seq.seq (option byte){Seq.length contents == al})
  (b: byte)
  : Lemma
    (requires
      GT.contiguous_prefix_length contents < al /\
      (forall (i:nat). (i >= GT.contiguous_prefix_length contents /\ i < al) ==>
        None? (Seq.index contents i)))
    (ensures (
      let pl = GT.contiguous_prefix_length contents in
      let c' = Seq.upd contents pl (Some b) in
      GT.contiguous_prefix_length c' == pl + 1))
  = let pl = GT.contiguous_prefix_length contents in
    let c' = Seq.upd contents pl (Some b) in
    GT.prefix_length_bounded contents;
    // [0, pl) are Some in c' (unchanged from original)
    let aux1 (k:nat{k < pl + 1}) : Lemma (Some? (Seq.index c' k))
      = if k < pl then begin
          GT.prefix_elements_are_some contents k;
          Seq.lemma_index_upd2 contents pl (Some b) k
        end
        else Seq.lemma_index_upd1 contents pl (Some b)
    in
    FStar.Classical.forall_intro aux1;
    // position pl+1 is None in c' (if it exists)
    if pl + 1 < al then begin
      assert (None? (Seq.index contents (pl + 1)));
      Seq.lemma_index_upd2 contents pl (Some b) (pl + 1)
    end;
    GT.cpl_characterization c' (pl + 1)

/// Gapless is preserved by resize (padding with Nones)
let gapless_preserved_by_resize (st: cb_state) (new_al: pos)
  : Lemma
    (requires cb_wf st /\ gapless st /\ new_al >= st.alloc_length)
    (ensures (
      let st' = resize_result st new_al in
      gapless st'))
  = let st' = resize_result st new_al in
    resize_prefix_length st.alloc_length new_al st.contents;
    let pl = GT.contiguous_prefix_length st.contents in
    let rc = resized_contents st.alloc_length new_al st.contents in
    let aux (i:nat{i >= pl /\ i < Seq.length rc})
      : Lemma (None? (Seq.index rc i))
      = if i < st.alloc_length then ()  // same as original contents
        else ()  // padding is None
    in
    FStar.Classical.forall_intro aux

/// Sequential range write: prefix grows by data length, gapless preserved
let rec write_range_sequential_prefix
  (al: pos) (contents: Seq.seq (option byte){Seq.length contents == al})
  (data: Seq.seq byte) (pl: nat)
  : Lemma
    (requires
      pl + Seq.length data <= al /\
      GT.contiguous_prefix_length contents == pl /\
      (forall (i:nat). (i >= pl /\ i < al) ==> None? (Seq.index contents i)))
    (ensures (
      let c' = GT.write_range_contents contents pl data in
      GT.contiguous_prefix_length c' == pl + Seq.length data /\
      (forall (i:nat). (i >= pl + Seq.length data /\ i < al) ==> None? (Seq.index c' i))))
    (decreases (Seq.length data))
  = if Seq.length data = 0 then ()
    else begin
      let b = Seq.index data 0 in
      let c1 = Seq.upd contents pl (Some b) in
      gapless_write_extends_prefix al contents b;
      let aux (i:nat{i >= pl + 1 /\ i < al})
        : Lemma (None? (Seq.index c1 i))
        = Seq.lemma_index_upd2 contents pl (Some b) i
      in
      FStar.Classical.forall_intro aux;
      write_range_sequential_prefix al c1 (Seq.tail data) (pl + 1)
    end

/// Transfer coherence across Seq.equal contents
let phys_log_coherent_seq_equal
  (al: pos) (phys: Seq.seq byte{Seq.length phys == al})
  (c1 c2: Seq.seq (option byte))
  (rs: nat{rs < al})
  : Lemma
    (requires Seq.length c1 == al /\ Seq.length c2 == al /\
              phys_log_coherent al phys c1 rs /\ c1 `Seq.equal` c2)
    (ensures phys_log_coherent al phys c2 rs)
  = let aux (j:nat{j < al}) : Lemma (coherent_at al phys c2 rs j)
      = ()
    in
    FStar.Classical.forall_intro aux

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

/// --- Write-buffer resize fold helpers ---
/// Each lemma proves one conjunct of the is_circular_buffer fold in the resize branch.

/// The new contents after resize + sequential write have the correct length.
let write_buffer_resize_contents_length
  (old_al: pos) (new_al: pos)
  (contents: Seq.seq (option byte){Seq.length contents == old_al})
  (pl: nat) (data: Seq.seq byte)
  : Lemma
    (requires new_al >= old_al /\ pl + Seq.length data <= new_al)
    (ensures Seq.length (GT.write_range_contents
               (resized_contents old_al new_al contents) pl data) == new_al)
  = ()

/// The new state after resize + sequential write is well-formed.
let write_buffer_resize_wf
  (st: cb_state) (new_al: pos) (data: Seq.seq byte)
  : Lemma
    (requires
      cb_wf st /\
      Pow2.is_pow2 new_al /\
      new_al >= st.alloc_length /\
      new_al <= st.virtual_length /\
      GT.contiguous_prefix_length st.contents + Seq.length data <= new_al)
    (ensures
      cb_wf { st with
        read_start = 0;
        alloc_length = new_al;
        contents = GT.write_range_contents
          (resized_contents st.alloc_length new_al st.contents)
          (GT.contiguous_prefix_length st.contents) data })
  = ()

/// The prefix length of the new state equals pl + length of data.
let write_buffer_resize_prefix
  (st: cb_state) (new_al: pos) (data: Seq.seq byte)
  : Lemma
    (requires
      cb_wf st /\ gapless st /\
      new_al >= st.alloc_length /\
      Pow2.is_pow2 new_al /\
      new_al <= st.virtual_length /\
      GT.contiguous_prefix_length st.contents + Seq.length data <= new_al)
    (ensures (
      let pl = GT.contiguous_prefix_length st.contents in
      let rc = resized_contents st.alloc_length new_al st.contents in
      let nc = GT.write_range_contents rc pl data in
      GT.contiguous_prefix_length nc == pl + Seq.length data))
  = let pl = GT.contiguous_prefix_length st.contents in
    let rc = resized_contents st.alloc_length new_al st.contents in
    resize_prefix_length st.alloc_length new_al st.contents;
    gapless_preserved_by_resize st new_al;
    // gapless on resized state means all positions >= pl in rc are None
    let aux (i:nat{i >= pl /\ i < new_al}) : Lemma (None? (Seq.index rc i))
      = if i < st.alloc_length then () else ()
    in
    FStar.Classical.forall_intro aux;
    write_range_sequential_prefix new_al rc data pl

/// Transfer coherence from Seq.slice data 0 n to data when the loop exit
/// condition says n is not less than write_len (== Seq.length data).
/// The precondition uses `false == (n < write_len)` instead of `n == Seq.length data`
/// because that's exactly what Pulse's bool-bound while invariant provides.
let write_buffer_resize_coherence_transfer
  (al: pos) (phys: Seq.seq byte{Seq.length phys == al})
  (old_al: pos) (contents: Seq.seq (option byte){Seq.length contents == old_al})
  (pl: nat) (data: Seq.seq byte) (n: nat) (write_len: nat)
  : Lemma
    (requires
      n <= write_len /\
      write_len == Seq.length data /\
      false == (n < write_len) /\
      al >= old_al /\
      pl + write_len <= al /\
      phys_log_coherent al phys
        (GT.write_range_contents (resized_contents old_al al contents) pl (Seq.slice data 0 n))
        0)
    (ensures
      phys_log_coherent al phys
        (GT.write_range_contents (resized_contents old_al al contents) pl data)
        0)
  = assert (n == Seq.length data);
    Seq.lemma_eq_intro (Seq.slice data 0 n) data;
    Seq.lemma_eq_elim (Seq.slice data 0 n) data

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
      = if k < vi then begin
          // Old element: upd at vi doesn't affect index k
          Seq.lemma_index_upd2 dst vi byte_val k
          // Some? and value equality from inductive hypothesis (k < vi)
        end else begin
          // New element: k == vi
          Seq.lemma_index_upd1 dst vi byte_val;
          // byte_val == phys[phys_index rs vi al] and by coherent_at:
          // phys[phys_index rs vi al] == Some?.v(contents[vi])
          assert (coherent_at al phys contents rs vi)
        end
    in
    FStar.Classical.forall_intro aux
