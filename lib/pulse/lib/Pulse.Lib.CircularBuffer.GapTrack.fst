module Pulse.Lib.CircularBuffer.GapTrack

/// Gap tracking spec for circular buffer.
/// Defines contiguous_prefix_length on seq (option byte) and proves
/// monotonicity/update properties.

module Seq = FStar.Seq

type byte = FStar.UInt8.t

/// Length of the longest contiguous prefix of Some values
let rec contiguous_prefix_length (s:Seq.seq (option byte)) 
  : Tot nat (decreases (Seq.length s))
  = if Seq.length s = 0 then 0
    else match Seq.index s 0 with
    | None -> 0
    | Some _ -> 1 + contiguous_prefix_length (Seq.tail s)

/// Prefix length is bounded by sequence length
let rec prefix_length_bounded (s:Seq.seq (option byte))
  : Lemma (ensures contiguous_prefix_length s <= Seq.length s)
          (decreases (Seq.length s))
  = if Seq.length s = 0 then ()
    else match Seq.index s 0 with
    | None -> ()
    | Some _ -> prefix_length_bounded (Seq.tail s)

/// All elements before the prefix length are Some
let rec prefix_elements_are_some (s:Seq.seq (option byte)) (i:nat)
  : Lemma (requires i < contiguous_prefix_length s /\ i < Seq.length s)
          (ensures Some? (Seq.index s i))
          (decreases (Seq.length s))
  = prefix_length_bounded s;
    if i = 0 then ()
    else begin
      assert (Some? (Seq.index s 0));
      prefix_elements_are_some (Seq.tail s) (i - 1)
    end

/// Element at the prefix length (if it exists) is None
let rec prefix_boundary_is_none_aux (s:Seq.seq (option byte)) (pl:nat)
  : Lemma (requires pl == contiguous_prefix_length s /\ pl < Seq.length s /\ pl > 0)
    (ensures None? (Seq.index s pl))
    (decreases pl)
  = assert (Some? (Seq.index s 0));
    let s' = Seq.tail s in
    let pl' = contiguous_prefix_length s' in
    if pl' = 0 then ()
    else prefix_boundary_is_none_aux s' pl'

let prefix_boundary_is_none (s:Seq.seq (option byte))
  : Lemma (requires contiguous_prefix_length s < Seq.length s)
          (ensures None? (Seq.index s (contiguous_prefix_length s)))
  = let pl = contiguous_prefix_length s in
    prefix_length_bounded s;
    if pl = 0 then ()
    else prefix_boundary_is_none_aux s pl

/// Converse of prefix_elements_are_some:
/// If all positions 0..n-1 are Some, then contiguous_prefix_length >= n.
let rec all_some_prefix_ge (s:Seq.seq (option byte)) (n:nat)
  : Lemma (requires n <= Seq.length s /\
                    (forall (i:nat{i < n}). Some? (Seq.index s i)))
          (ensures contiguous_prefix_length s >= n)
          (decreases n)
  = if n = 0 then ()
    else (
      assert (Some? (Seq.index s 0));
      // cpl s = 1 + cpl (tail s)
      // All positions 0..n-2 of tail are Some (shifted from 1..n-1 of s)
      let s' = Seq.tail s in
      let aux (i:nat{i < n - 1})
        : Lemma (Some? (Seq.index s' i))
        = assert (Seq.index s' i == Seq.index s (i + 1));
          assert (Some? (Seq.index s (i + 1)))
      in
      FStar.Classical.forall_intro aux;
      all_some_prefix_ge s' (n - 1)
    )

/// Writing Some at an index strictly beyond the prefix doesn't change the prefix
let rec write_beyond_prefix_preserves (s:Seq.seq (option byte)) (i:nat) (b:byte)
  : Lemma (requires i < Seq.length s /\ i > contiguous_prefix_length s)
          (ensures contiguous_prefix_length (Seq.upd s i (Some b)) == contiguous_prefix_length s)
          (decreases (Seq.length s))
  = if Seq.length s = 0 then ()
    else match Seq.index s 0 with
    | None -> ()
    | Some _ ->
      let s' = Seq.tail s in
      assert (Seq.upd s i (Some b) `Seq.equal` 
              Seq.cons (Seq.index s 0) (Seq.upd s' (i - 1) (Some b)));
      write_beyond_prefix_preserves s' (i - 1) b

/// Writing Some at exactly the prefix length extends the prefix by ≥ 1
let rec write_at_prefix_extends (s:Seq.seq (option byte)) (b:byte)
  : Lemma (requires 
      contiguous_prefix_length s < Seq.length s /\
      None? (Seq.index s (contiguous_prefix_length s)))
    (ensures 
      contiguous_prefix_length (Seq.upd s (contiguous_prefix_length s) (Some b)) >= 
      contiguous_prefix_length s + 1)
    (decreases (Seq.length s))
  = let pl = contiguous_prefix_length s in
    if pl = 0 then ()
    else begin
      let s_tail = Seq.tail s in
      let pl' = contiguous_prefix_length s_tail in
      let s' = Seq.upd s pl (Some b) in
      assert (s' `Seq.equal` Seq.cons (Seq.index s 0) (Seq.upd s_tail (pl - 1) (Some b)));
      write_at_prefix_extends s_tail b
    end

/// Overwriting an existing Some preserves the prefix
let rec write_some_at_existing_some (s:Seq.seq (option byte)) (i:nat) (b:byte)
  : Lemma (requires i < Seq.length s /\ Some? (Seq.index s i) /\ i < contiguous_prefix_length s)
          (ensures contiguous_prefix_length (Seq.upd s i (Some b)) >= contiguous_prefix_length s)
          (decreases (Seq.length s))
  = if i = 0 then begin
      let s' = Seq.upd s 0 (Some b) in
      assert (Some? (Seq.index s' 0));
      assert (Seq.tail s' `Seq.equal` Seq.tail s)
    end
    else begin
      let s' = Seq.upd s i (Some b) in
      assert (s' `Seq.equal` Seq.cons (Seq.index s 0) (Seq.upd (Seq.tail s) (i - 1) (Some b)));
      write_some_at_existing_some (Seq.tail s) (i - 1) b
    end

/// Monotonicity: writing Some never decreases the prefix length
let write_some_monotone (s:Seq.seq (option byte)) (i:nat) (b:byte)
  : Lemma (requires i < Seq.length s)
          (ensures contiguous_prefix_length (Seq.upd s i (Some b)) >= contiguous_prefix_length s)
  = let pl = contiguous_prefix_length s in
    prefix_length_bounded s;
    if i > pl then
      write_beyond_prefix_preserves s i b
    else if i < pl then begin
      prefix_elements_are_some s i;
      write_some_at_existing_some s i b
    end
    else if pl < Seq.length s then begin
      prefix_boundary_is_none s;
      write_at_prefix_extends s b
    end
    else ()

/// Creating a sequence of Nones
let rec create_nones (n:nat) : Tot (s:Seq.seq (option byte){Seq.length s == n}) (decreases n) =
  if n = 0 then Seq.empty
  else Seq.cons None (create_nones (n - 1))

/// Prefix of all-Nones is 0
let prefix_of_nones (n:nat) 
  : Lemma (ensures contiguous_prefix_length (create_nones n) == 0)
  = if n = 0 then () else ()

/// All elements of create_nones are None
let rec create_nones_all_none (n:nat) (i:nat{i < n})
  : Lemma (ensures None? (Seq.index (create_nones n) i))
          (decreases n)
  = if i = 0 then ()
    else create_nones_all_none (n - 1) (i - 1)

/// Characterization: if all [0,p) are Some and (p==len or s[p] is None),
/// then cpl(s) == p.
let rec cpl_characterization (s: Seq.seq (option byte)) (p: nat)
  : Lemma
    (requires
      p <= Seq.length s /\
      (forall (k:nat). k < p ==> Some? (Seq.index s k)) /\
      (p == Seq.length s \/ (p < Seq.length s /\ None? (Seq.index s p))))
    (ensures contiguous_prefix_length s == p)
    (decreases p)
  = if p = 0 then ()
    else begin
      assert (Some? (Seq.index s 0));
      let ts = Seq.tail s in
      assert (forall (k:nat). k < p - 1 ==> Seq.index ts k == Seq.index s (k + 1));
      if p - 1 < Seq.length ts then
        assert (Seq.index ts (p - 1) == Seq.index s p)
      else ();
      cpl_characterization ts (p - 1)
    end

/// Write a range of bytes at consecutive offsets
let rec write_range_contents
  (contents: Seq.seq (option byte))
  (offset: nat)
  (data: Seq.seq byte)
  : Pure (Seq.seq (option byte))
    (requires offset + Seq.length data <= Seq.length contents)
    (ensures fun r -> Seq.length r == Seq.length contents)
    (decreases (Seq.length data))
  = if Seq.length data = 0 then contents
    else
      let c' = Seq.upd contents offset (Some (Seq.index data 0)) in
      write_range_contents c' (offset + 1) (Seq.tail data)

/// Writing a range of bytes never decreases the contiguous prefix length
let rec write_range_monotone
  (contents: Seq.seq (option byte))
  (offset: nat)
  (data: Seq.seq byte)
  : Lemma
    (requires offset + Seq.length data <= Seq.length contents)
    (ensures contiguous_prefix_length (write_range_contents contents offset data)
             >= contiguous_prefix_length contents)
    (decreases (Seq.length data))
  = if Seq.length data = 0 then ()
    else begin
      let c' = Seq.upd contents offset (Some (Seq.index data 0)) in
      write_some_monotone contents offset (Seq.index data 0);
      write_range_monotone c' (offset + 1) (Seq.tail data)
    end

/// Stepping lemma: writing one more byte = upd of the previous range result
let rec write_range_snoc
  (contents: Seq.seq (option byte))
  (offset: nat)
  (data: Seq.seq byte)
  (i: nat)
  : Lemma
    (requires offset + Seq.length data <= Seq.length contents /\
             i < Seq.length data /\
             offset + i + 1 <= Seq.length contents)
    (ensures
      write_range_contents contents offset (Seq.slice data 0 (i + 1)) `Seq.equal`
      Seq.upd (write_range_contents contents offset (Seq.slice data 0 i))
              (offset + i) (Some (Seq.index data i)))
    (decreases i)
  = if i = 0 then ()
    else begin
      let d_ip1 = Seq.slice data 0 (i + 1) in
      let d_i = Seq.slice data 0 i in
      let c' = Seq.upd contents offset (Some (Seq.index data 0)) in
      assert (Seq.length d_ip1 > 0);
      assert (Seq.index d_ip1 0 == Seq.index data 0);
      let tail_ip1 = Seq.tail d_ip1 in
      let tail_i = Seq.tail d_i in
      assert (tail_ip1 `Seq.equal` Seq.slice data 1 (i + 1));
      assert (tail_i `Seq.equal` Seq.slice data 1 i);
      assert (Seq.length tail_ip1 == i);
      assert (Seq.length tail_i == i - 1);
      // Shift to tail data
      let d' = Seq.tail data in
      assert (tail_ip1 `Seq.equal` Seq.slice d' 0 i);
      assert (tail_i `Seq.equal` Seq.slice d' 0 (i - 1));
      assert (Seq.index d' (i - 1) == Seq.index data i);
      write_range_snoc c' (offset + 1) d' (i - 1)
    end

/// Total wrapper for write_range_contents (no precondition; identity when out of bounds)
let write_range_contents_t
  (contents: Seq.seq (option byte))
  (offset: nat)
  (data: Seq.seq byte)
  : Seq.seq (option byte)
  = if offset + Seq.length data <= Seq.length contents
    then write_range_contents contents offset data
    else contents

/// Equivalence: when precondition holds, total version equals partial version
let write_range_contents_t_eq
  (contents: Seq.seq (option byte))
  (offset: nat)
  (data: Seq.seq byte)
  : Lemma
    (requires offset + Seq.length data <= Seq.length contents)
    (ensures write_range_contents_t contents offset data ==
             write_range_contents contents offset data)
  = ()

/// Length preservation for total version
let write_range_contents_t_length
  (contents: Seq.seq (option byte))
  (offset: nat)
  (data: Seq.seq byte)
  : Lemma (Seq.length (write_range_contents_t contents offset data) ==
           Seq.length contents)
  = if offset + Seq.length data <= Seq.length contents
    then ()
    else ()

/// Pointwise characterization of write_range_contents
let rec write_range_index
  (contents: Seq.seq (option byte))
  (offset: nat)
  (data: Seq.seq byte)
  (i: nat)
  : Lemma
    (requires offset + Seq.length data <= Seq.length contents /\
             i < Seq.length contents)
    (ensures
      Seq.index (write_range_contents contents offset data) i ==
        (if offset <= i && i < offset + Seq.length data
         then Some (Seq.index data (i - offset))
         else Seq.index contents i))
    (decreases (Seq.length data))
  = if Seq.length data = 0 then ()
    else begin
      let c' = Seq.upd contents offset (Some (Seq.index data 0)) in
      if i = offset then begin
        // First byte written at offset — show it's overwritten
        write_range_index c' (offset + 1) (Seq.tail data) i
      end
      else if i > offset && i < offset + Seq.length data then begin
        // In the written range but not the first position
        write_range_index c' (offset + 1) (Seq.tail data) i;
        assert (Seq.index c' i == Seq.index contents i);
        assert (i - offset >= 1);
        assert (Seq.index (Seq.tail data) (i - (offset + 1)) == Seq.index data (i - offset))
      end
      else begin
        // Outside the written range — unchanged
        write_range_index c' (offset + 1) (Seq.tail data) i;
        if i = offset then ()
        else assert (Seq.index c' i == Seq.index contents i)
      end
    end

/// Forall version: characterize every index of write_range_contents
let write_range_forall_index
  (contents: Seq.seq (option byte))
  (offset: nat)
  (data: Seq.seq byte)
  : Lemma
    (requires offset + Seq.length data <= Seq.length contents)
    (ensures
      forall (i:nat{i < Seq.length contents}).
        Seq.index (write_range_contents contents offset data) i ==
          (if offset <= i && i < offset + Seq.length data
           then Some (Seq.index data (i - offset))
           else Seq.index contents i))
  = let aux (i:nat{i < Seq.length contents})
      : Lemma (Seq.index (write_range_contents contents offset data) i ==
                (if offset <= i && i < offset + Seq.length data
                 then Some (Seq.index data (i - offset))
                 else Seq.index contents i))
      = write_range_index contents offset data i
    in
    FStar.Classical.forall_intro aux
