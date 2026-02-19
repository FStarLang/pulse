module Pulse.Lib.RangeMap.Spec

/// Spec for a range set — sorted non-overlapping, non-adjacent intervals.
/// Models MsQuic's QUIC_RANGE (WrittenRanges) for tracking received byte offsets.

module Seq = FStar.Seq

(*** Types ***)

/// An interval [low, low+count)
noeq type interval = { low: nat; count: pos }

/// Upper bound (exclusive) of an interval
let high (iv: interval) : nat = iv.low + iv.count

(*** Well-formedness ***)

/// Two intervals are non-overlapping and non-adjacent, and sorted
let separated (a b: interval) : prop =
  high a < b.low   // gap between a and b (not adjacent, not overlapping)

/// A range set is a sorted sequence of separated intervals
let rec range_map_wf (s: Seq.seq interval) 
  : Tot prop (decreases Seq.length s) =
  if Seq.length s <= 1 then True
  else
    separated (Seq.index s 0) (Seq.index s 1) /\
    range_map_wf (Seq.tail s)

type range_map = s:Seq.seq interval{range_map_wf s}

(*** Membership ***)

/// An offset is covered by an interval
let in_interval (iv: interval) (offset: nat) : bool =
  iv.low <= offset && offset < high iv

/// An offset is covered by some interval in the range set
let rec mem (s: Seq.seq interval) (offset: nat) 
  : Tot bool (decreases Seq.length s) =
  if Seq.length s = 0 then false
  else in_interval (Seq.index s 0) offset || mem (Seq.tail s) offset

(*** Core operations ***)

/// Length of contiguous coverage starting from offset 0.
/// If the first interval starts at 0, returns its count; otherwise 0.
let contiguous_from_zero (s: Seq.seq interval) : nat =
  if Seq.length s = 0 then 0
  else
    let first = Seq.index s 0 in
    if first.low = 0 then first.count
    else 0

/// Length of contiguous coverage starting from a given base offset.
/// If the first interval covers base, returns high(first) - base; otherwise 0.
let contiguous_from (s: Seq.seq interval) (base: nat) : nat =
  if Seq.length s = 0 then 0
  else
    let first = Seq.index s 0 in
    if first.low <= base && base < high first then high first - base
    else 0

/// Check if interval overlaps or is adjacent to [offset, offset+len)
let mergeable (iv: interval) (offset: nat) (len: pos) : bool =
  not (high iv < offset || offset + len < iv.low)

/// Merge interval [offset, offset+len) into sorted range set
let rec add_range (s: Seq.seq interval) (offset: nat) (len: pos) 
  : Tot (Seq.seq interval) (decreases Seq.length s) =
  if Seq.length s = 0 then
    Seq.create 1 ({ low = offset; count = len })
  else
    let hd = Seq.index s 0 in
    let tl = Seq.tail s in
    if offset + len < hd.low then
      // New interval goes entirely before hd (no overlap/adjacency)
      Seq.cons ({ low = offset; count = len }) s
    else if high hd < offset then
      // hd is entirely before new interval, keep hd, recurse on tail
      Seq.cons hd (add_range tl offset len)
    else
      // Overlap or adjacency — merge
      let merged_low = if offset < hd.low then offset else hd.low in
      let merged_high = if offset + len > high hd then offset + len else high hd in
      // Continue merging with tail (the merged interval might overlap more)
      add_range tl merged_low (merged_high - merged_low)

/// Drain n bytes: shift all intervals left by n, drop/trim those below 0
let rec drain_ranges (s: Seq.seq interval) (n: nat) 
  : Tot (Seq.seq interval) (decreases Seq.length s) =
  if Seq.length s = 0 then Seq.empty
  else
    let hd = Seq.index s 0 in
    let tl = Seq.tail s in
    if high hd <= n then
      // Entire interval is drained
      drain_ranges tl n
    else if hd.low < n then
      // Partially drained — trim the front
      Seq.cons ({ low = 0; count = high hd - n }) (drain_ranges tl n)
    else
      // Shift left by n
      Seq.cons ({ low = hd.low - n; count = hd.count }) (drain_ranges tl n)

(*** Lemmas ***)

/// Helper: range_map_wf is preserved by tail
let range_map_wf_tail (s: Seq.seq interval) 
  : Lemma (requires range_map_wf s /\ Seq.length s > 0)
          (ensures range_map_wf (Seq.tail s)) =
  ()

/// Helper: cons preserves range_map_wf if head is separated from new head  
let range_map_wf_cons (hd: interval) (tl: Seq.seq interval)
  : Lemma (requires (Seq.length tl = 0 \/ (range_map_wf tl /\ separated hd (Seq.index tl 0))))
          (ensures range_map_wf (Seq.cons hd tl)) =
  let s = Seq.cons hd tl in
  assert (Seq.length s = Seq.length tl + 1);
  if Seq.length tl = 0 then
    assert (Seq.length s = 1)
  else (
    assert (Seq.length s > 1);
    assert (Seq.length tl > 0);
    // Need to show: separated (Seq.index s 0) (Seq.index s 1) /\ range_map_wf (Seq.tail s)
    assert (Seq.index s 0 == hd);
    assert (Seq.index s 1 == Seq.index tl 0);
    assert (Seq.tail s `Seq.equal` tl)
  )

/// drain_ranges preserves well-formedness
let rec drain_ranges_wf (s: Seq.seq interval) (n: nat)
  : Lemma (requires range_map_wf s)
          (ensures range_map_wf (drain_ranges s n))
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else
    let hd = Seq.index s 0 in
    let tl = Seq.tail s in
    range_map_wf_tail s;
    drain_ranges_wf tl n;
    if high hd <= n then ()
    else if hd.low < n then
      let drained_tl = drain_ranges tl n in
      if Seq.length drained_tl > 0 then (
        let new_hd = { low = 0; count = high hd - n } in
        let tl_hd = Seq.index drained_tl 0 in
        assert (separated hd (Seq.index tl 0));
        assert (high hd < (Seq.index tl 0).low);
        assert (tl_hd.low = (Seq.index tl 0).low - n);
        assert (high new_hd = high hd - n);
        assert (high new_hd < (Seq.index tl 0).low - n);
        assert (high new_hd < tl_hd.low);
        range_map_wf_cons new_hd drained_tl
      ) else ()
    else
      let drained_tl = drain_ranges tl n in
      if Seq.length drained_tl > 0 then (
        let new_hd = { low = hd.low - n; count = hd.count } in
        let tl_hd = Seq.index drained_tl 0 in
        assert (separated hd (Seq.index tl 0));
        assert (high new_hd = high hd - n);
        range_map_wf_cons new_hd drained_tl
      ) else ()

/// add_range preserves well-formedness
/// Helper: add_range preserves lower bounds
let rec add_range_first_lower_bound (s: Seq.seq interval) (offset: nat) (len: pos)
  : Lemma (ensures (let r = add_range s offset len in
                    Seq.length r > 0 ==>
                    (Seq.length s = 0 ==> (Seq.index r 0).low = offset) /\
                    (Seq.length s > 0 ==> (Seq.index r 0).low <= (Seq.index s 0).low /\
                                           (Seq.index r 0).low <= offset)))
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else
    let hd = Seq.index s 0 in
    let tl = Seq.tail s in
    if offset + len < hd.low then ()
    else if high hd < offset then
      add_range_first_lower_bound tl offset len
    else
      let merged_low = if offset < hd.low then offset else hd.low in
      let merged_high = if offset + len > high hd then offset + len else high hd in
      add_range_first_lower_bound tl merged_low (merged_high - merged_low)

/// Helper: add_range respects lower bound
let rec add_range_respects_lower_bound (s: Seq.seq interval) (offset: nat) (len: pos) (iv: interval)
  : Lemma (requires Seq.length s > 0 /\
                    range_map_wf s /\
                    high iv < (Seq.index s 0).low /\
                    high iv < offset)
          (ensures (let r = add_range s offset len in
                    Seq.length r > 0 ==> high iv < (Seq.index r 0).low))
          (decreases Seq.length s) =
  add_range_first_lower_bound s offset len;
  let hd = Seq.index s 0 in
  let tl = Seq.tail s in
  if offset + len < hd.low then (
    // Result is [new_interval; ...s], so first element has low = offset
    ()
  ) else if high hd < offset then (
    // Result is [hd; ...add_range tl offset len]
    // The first element is hd, and we know high iv < hd.low
    ()
  ) else (
    // Merging case: the result comes from recursing on tl with merged interval
    let merged_low = if offset < hd.low then offset else hd.low in
    let merged_high = if offset + len > high hd then offset + len else high hd in
    let result_tl = add_range tl merged_low (merged_high - merged_low) in
    // We need to show that if result_tl is non-empty, high iv < (Seq.index result_tl 0).low
    // We know: high iv < hd.low and high iv < offset
    // Therefore: high iv < merged_low
    if Seq.length tl > 0 then (
      // From separated: high hd < (Seq.index tl 0).low
      // From transitivity: high iv < hd.low < hd.low + hd.count = high hd < (Seq.index tl 0).low
      assert (separated hd (Seq.index tl 0));
      range_map_wf_tail s;
      assert (high hd == hd.low + hd.count);
      assert (high iv < hd.low);
      assert (hd.low < high hd);
      assert (high iv < high hd);
      assert (high hd < (Seq.index tl 0).low);
      assert (high iv < (Seq.index tl 0).low);
      assert (high iv < merged_low);
      add_range_respects_lower_bound tl merged_low (merged_high - merged_low) iv
    ) else (
      // tl is empty, so result_tl is just the merged interval
      assert ((Seq.index result_tl 0).low = merged_low);
      assert (high iv < merged_low)
    )
  )

let rec add_range_wf (s: Seq.seq interval) (offset: nat) (len: pos)
  : Lemma (requires range_map_wf s)
          (ensures range_map_wf (add_range s offset len))
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else
    let hd = Seq.index s 0 in
    let tl = Seq.tail s in
    range_map_wf_tail s;
    if offset + len < hd.low then
      let new_iv = { low = offset; count = len } in
      assert (high new_iv = offset + len);
      assert (high new_iv < hd.low);
      assert (separated new_iv hd);
      range_map_wf_cons new_iv s
    else if high hd < offset then (
      add_range_wf tl offset len;
      let result = add_range tl offset len in
      if Seq.length result > 0 then (
        if Seq.length tl > 0 then (
          add_range_respects_lower_bound tl offset len hd;
          assert (separated hd (Seq.index result 0))
        ) else ();
        range_map_wf_cons hd result
      ) else ()
    ) else
      let merged_low = if offset < hd.low then offset else hd.low in
      let merged_high = if offset + len > high hd then offset + len else high hd in
      add_range_wf tl merged_low (merged_high - merged_low)

/// Helper: membership in tail
let mem_tail (s: Seq.seq interval) (offset: nat)
  : Lemma (requires Seq.length s > 0 /\ mem s offset /\ not (in_interval (Seq.index s 0) offset))
          (ensures mem (Seq.tail s) offset) =
  ()

/// Helper: membership after cons
let mem_cons (hd: interval) (tl: Seq.seq interval) (offset: nat)
  : Lemma (ensures mem (Seq.cons hd tl) offset <==> (in_interval hd offset || mem tl offset)) =
  let s = Seq.cons hd tl in
  assert (Seq.length s > 0);
  assert (Seq.index s 0 == hd);
  assert (Seq.tail s `Seq.equal` tl)

/// add_range includes all offsets in the added range
let rec add_range_mem_new (s: Seq.seq interval) (offset: nat) (len: pos) (x: nat)
  : Lemma (requires offset <= x /\ x < offset + len)
          (ensures mem (add_range s offset len) x)
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else
    let hd = Seq.index s 0 in
    let tl = Seq.tail s in
    if offset + len < hd.low then
      mem_cons ({ low = offset; count = len }) s x
    else if high hd < offset then (
      add_range_mem_new tl offset len x;
      mem_cons hd (add_range tl offset len) x
    ) else
      let merged_low = if offset < hd.low then offset else hd.low in
      let merged_high = if offset + len > high hd then offset + len else high hd in
      assert (merged_low <= offset);
      assert (merged_high >= offset + len);
      assert (merged_low <= x);
      assert (x < merged_high);
      add_range_mem_new tl merged_low (merged_high - merged_low) x

/// add_range preserves existing members
let rec add_range_mem_old (s: Seq.seq interval) (offset: nat) (len: pos) (x: nat)
  : Lemma (requires mem s x)
          (ensures mem (add_range s offset len) x)
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else
    let hd = Seq.index s 0 in
    let tl = Seq.tail s in
    if in_interval hd x then (
      if offset + len < hd.low then
        mem_cons ({ low = offset; count = len }) s x
      else if high hd < offset then
        mem_cons hd (add_range tl offset len) x
      else
        let merged_low = if offset < hd.low then offset else hd.low in
        let merged_high = if offset + len > high hd then offset + len else high hd in
        assert (merged_low <= hd.low);
        assert (merged_high >= high hd);
        assert (merged_low <= x);
        assert (x < merged_high);
        add_range_mem_new tl merged_low (merged_high - merged_low) x
    ) else (
      mem_tail s x;
      assert (mem tl x);
      if offset + len < hd.low then
        mem_cons ({ low = offset; count = len }) s x
      else if high hd < offset then (
        add_range_mem_old tl offset len x;
        mem_cons hd (add_range tl offset len) x
      ) else
        let merged_low = if offset < hd.low then offset else hd.low in
        let merged_high = if offset + len > high hd then offset + len else high hd in
        add_range_mem_old tl merged_low (merged_high - merged_low) x
    )

/// add_range converse: if x is in the result, then either x was in [offset, offset+len) or in s
let rec add_range_mem_inv (s: Seq.seq interval) (offset: nat) (len: pos) (x: nat)
  : Lemma (requires mem (add_range s offset len) x)
          (ensures (offset <= x /\ x < offset + len) \/ mem s x)
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else
    let hd = Seq.index s 0 in
    let tl = Seq.tail s in
    if offset + len < hd.low then (
      // Result is cons {offset,len} s
      mem_cons ({ low = offset; count = len }) s x;
      if in_interval ({ low = offset; count = len }) x then ()
      else ()  // mem s x
    ) else if high hd < offset then (
      // Result is cons hd (add_range tl offset len)
      mem_cons hd (add_range tl offset len) x;
      if in_interval hd x then (
        mem_cons hd tl x
      ) else (
        add_range_mem_inv tl offset len x;
        if mem tl x then
          mem_cons hd tl x
        else ()
      )
    ) else (
      // Merge case
      let merged_low = if offset < hd.low then offset else hd.low in
      let merged_high = if offset + len > high hd then offset + len else high hd in
      let new_len : pos = merged_high - merged_low in
      add_range_mem_inv tl merged_low new_len x;
      if merged_low <= x && x < merged_high then (
        // x is in merged range — either in [offset, offset+len) or in hd
        if offset <= x && x < offset + len then ()
        else (
          // x must be in hd
          assert (hd.low <= x /\ x < high hd);
          mem_cons hd tl x
        )
      ) else (
        // x was in tl
        mem_cons hd tl x
      )
    )

/// In a well-formed range map, any member of the tail is >= high of head.
/// (All tail intervals are separated from head, so their low > high head.)
let rec mem_wf_tail_ge (s: Seq.seq interval) (x: nat)
  : Lemma (requires range_map_wf s /\ Seq.length s > 0 /\
                    mem (Seq.tail s) x)
          (ensures x >= high (Seq.index s 0))
          (decreases Seq.length s) =
  let hd = Seq.index s 0 in
  let tl = Seq.tail s in
  if Seq.length tl = 0 then ()
  else
    let tl_hd = Seq.index tl 0 in
    assert (separated hd tl_hd);
    assert (tl_hd.low > high hd);
    if in_interval tl_hd x then
      assert (x >= tl_hd.low)
    else (
      mem_tail tl x;
      range_map_wf_tail s;
      mem_wf_tail_ge tl x;
      assert (x >= high tl_hd);
      assert (high tl_hd > high hd)
    )

/// Strict version: member of tail is strictly greater than high of head
let mem_wf_tail_gt (s: Seq.seq interval) (x: nat)
  : Lemma (requires range_map_wf s /\ Seq.length s > 0 /\
                    Seq.length (Seq.tail s) > 0 /\
                    mem (Seq.tail s) x)
          (ensures x > high (Seq.index s 0))
  = let hd = Seq.index s 0 in
    let tl = Seq.tail s in
    let tl_hd = Seq.index tl 0 in
    assert (separated hd tl_hd);
    assert (tl_hd.low > high hd);
    range_map_wf_tail s;
    if in_interval tl_hd x then
      assert (x >= tl_hd.low)
    else (
      mem_tail tl x;
      mem_wf_tail_ge tl x;
      assert (x >= high tl_hd);
      assert (high tl_hd > tl_hd.low);
      assert (tl_hd.low > high hd)
    )

/// Positions below the first interval's low are not members (wf ensures sorted order)
let rec mem_not_below_first (s: Seq.seq interval) (x: nat)
  : Lemma (requires range_map_wf s /\ Seq.length s > 0 /\ x < (Seq.index s 0).low)
          (ensures not (mem s x))
          (decreases Seq.length s)
  = let hd = Seq.index s 0 in
    assert (not (in_interval hd x));
    let tl = Seq.tail s in
    if Seq.length tl = 0 then ()
    else (
      range_map_wf_tail s;
      assert (separated hd (Seq.index tl 0));
      assert ((Seq.index tl 0).low > high hd);
      assert ((Seq.index tl 0).low > x);
      mem_not_below_first tl x
    )

/// All interval endpoints are bounded by a given value
let range_map_bounded (s: Seq.seq interval) (bound: nat) : prop =
  forall (i:nat{i < Seq.length s}). high (Seq.index s i) <= bound

/// add_range preserves boundedness
let rec add_range_bounded (s: Seq.seq interval) (offset: nat) (len: pos) (bound: nat)
  : Lemma (requires range_map_bounded s bound /\ offset + len <= bound)
          (ensures range_map_bounded (add_range s offset len) bound)
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else
    let hd = Seq.index s 0 in
    let tl = Seq.tail s in
    assert (high hd <= bound);
    let bounded_tail () : Lemma (range_map_bounded tl bound) =
      let aux (i:nat{i < Seq.length tl}) : Lemma (high (Seq.index tl i) <= bound) =
        assert (Seq.index tl i == Seq.index s (i + 1))
      in
      FStar.Classical.forall_intro aux
    in
    bounded_tail ();
    if offset + len < hd.low then (
      // Inserted before: new first is {low=offset; count=len}, rest is s
      let r = add_range s offset len in
      let aux (i:nat{i < Seq.length r}) : Lemma (high (Seq.index r i) <= bound) =
        if i = 0 then assert (high (Seq.index r 0) == offset + len)
        else assert (Seq.index r i == Seq.index s (i - 1))
      in
      FStar.Classical.forall_intro aux
    ) else if high hd < offset then (
      // Keep hd, recurse on tail
      add_range_bounded tl offset len bound;
      let r = add_range s offset len in
      let r_tl = add_range tl offset len in
      let aux (i:nat{i < Seq.length r}) : Lemma (high (Seq.index r i) <= bound) =
        if i = 0 then assert (Seq.index r 0 == hd)
        else assert (Seq.index r i == Seq.index r_tl (i - 1))
      in
      FStar.Classical.forall_intro aux
    ) else (
      // Merge: merged_high = max(offset+len, high hd) <= bound
      let merged_low = if offset < hd.low then offset else hd.low in
      let merged_high = if offset + len > high hd then offset + len else high hd in
      assert (merged_high <= bound);
      add_range_bounded tl merged_low (merged_high - merged_low) bound
    )

/// contiguous_from is bounded by range_map_bounded
let cf_bounded (s: Seq.seq interval) (base: nat) (bound: nat)
  : Lemma (requires range_map_bounded s bound /\ base <= bound)
          (ensures contiguous_from s base <= bound - base)
  = if Seq.length s = 0 then ()
    else (
      let first = Seq.index s 0 in
      assert (high first <= bound);
      if first.low <= base && base < high first then
        assert (contiguous_from s base == high first - base)
      else ()
    )

/// Positions beyond bound are not members (when range_map_bounded holds)
let rec mem_bounded (s: Seq.seq interval) (bound: nat) (x: nat)
  : Lemma (requires range_map_bounded s bound /\ x >= bound)
          (ensures not (mem s x))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (
      let first = Seq.index s 0 in
      assert (high first <= bound);
      assert (x >= bound);
      assert (not (in_interval first x));
      let tl = Seq.tail s in
      let bounded_tail () : Lemma (range_map_bounded tl bound) =
        let aux (i:nat{i < Seq.length tl}) : Lemma (high (Seq.index tl i) <= bound) =
          assert (Seq.index tl i == Seq.index s (i + 1))
        in
        FStar.Classical.forall_intro aux
      in
      bounded_tail ();
      mem_bounded tl bound x
    )

/// range_map_bounded is monotone in the bound
let range_map_bounded_monotone (s: Seq.seq interval) (bound1: nat) (bound2: nat)
  : Lemma (requires range_map_bounded s bound1 /\ bound1 <= bound2)
          (ensures range_map_bounded s bound2)
  = ()

/// add_range result is non-empty
let rec add_range_nonempty (s: Seq.seq interval) (offset: nat) (len: pos)
  : Lemma (ensures Seq.length (add_range s offset len) > 0)
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else
    let tl = Seq.tail s in
    let hd = Seq.index s 0 in
    if offset + len < hd.low then ()
    else if high hd < offset then
      add_range_nonempty tl offset len
    else
      let merged_low = if offset < hd.low then offset else hd.low in
      let merged_high = if offset + len > high hd then offset + len else high hd in
      add_range_nonempty tl merged_low (merged_high - merged_low)

/// Maximum endpoint of any interval in the range map (0 if empty)
let range_map_max_endpoint (s: Seq.seq interval) : nat =
  if Seq.length s = 0 then 0
  else high (Seq.index s (Seq.length s - 1))

/// range_map_max_endpoint is bounded by range_map_bounded
let range_map_max_endpoint_bounded (s: Seq.seq interval) (bound: nat)
  : Lemma (requires range_map_bounded s bound)
          (ensures range_map_max_endpoint s <= bound) = ()

/// contiguous_from > 0 implies base_aligned (first interval covers base)
let contiguous_from_implies_base_aligned (s: Seq.seq interval) (base: nat)
  : Lemma (requires contiguous_from s base > 0)
          (ensures Seq.length s > 0 /\
                   (let first = Seq.index s 0 in first.low <= base /\ base <= high first)) = ()

/// contiguous_from decreases linearly when advancing the base within the first interval
let contiguous_from_after_advance (s: Seq.seq interval) (base: nat) (n: nat)
  : Lemma (requires contiguous_from s base > 0 /\ n <= contiguous_from s base)
          (ensures contiguous_from s (base + n) == contiguous_from s base - n) = ()

/// add_range preserves base_aligned when existing base_aligned holds and offset >= base
/// (i.e., the add can only merge/extend the first interval or append after it)

/// Helper: after add_range with offset <= first element's low (or empty seq),
/// result's first has high >= offset + len
#push-options "--z3rlimit_factor 4"
let rec add_range_first_high_bound (s: Seq.seq interval) (offset: nat) (len: pos)
  : Lemma (requires range_map_wf s /\ (Seq.length s = 0 \/ offset <= (Seq.index s 0).low))
          (ensures (let r = add_range s offset len in
                    Seq.length r > 0 /\
                    high (Seq.index r 0) >= offset + len))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else
      let hd = Seq.index s 0 in
      let tl = Seq.tail s in
      range_map_wf_tail s;
      if offset + len < hd.low then ()  // insert before: result_first = {offset, len}
      else (
        // offset <= hd.low and offset + len >= hd.low, so merge (not "keep first" since offset <= hd.low)
        let merged_low = if offset < hd.low then offset else hd.low in
        let merged_high = if offset + len > high hd then offset + len else high hd in
        assert (merged_low == offset);  // since offset <= hd.low
        if Seq.length tl = 0 then ()
        else (
          assert (separated hd (Seq.index tl 0));
          assert ((Seq.index tl 0).low > high hd);
          assert (merged_low <= (Seq.index tl 0).low);
          add_range_first_high_bound tl merged_low (merged_high - merged_low)
        )
      )
#pop-options

let rec add_range_base_aligned
  (s: Seq.seq interval) (base offset: nat) (len: pos)
  : Lemma
    (requires range_map_wf s /\
             Seq.length s > 0 /\
             (let first = Seq.index s 0 in
               first.low <= base /\ base <= high first) /\
             offset >= (Seq.index s 0).low)
    (ensures (
      Seq.length (add_range s offset len) > 0 /\
      (Seq.index (add_range s offset len) 0).low <= base /\
      base <= high (Seq.index (add_range s offset len) 0)))
    (decreases Seq.length s)
  = let first = Seq.index s 0 in
    let tl = Seq.tail s in
    range_map_wf_tail s;
    if offset + len < first.low then ()  // can't happen: offset >= first.low
    else if high first < offset then (
      // Keep first, recurse on tail — base_aligned trivially preserved (first unchanged)
      add_range_wf tl offset len;
      ()
    ) else (
      // Merge: merged_low = min(offset, first.low) = first.low (since offset >= first.low)
      let merged_low = if offset < first.low then offset else first.low in
      let merged_high = if offset + len > high first then offset + len else high first in
      // merged_low = first.low <= base, merged_high >= high first >= base
      add_range_first_lower_bound tl merged_low (merged_high - merged_low);
      add_range_first_high_bound tl merged_low (merged_high - merged_low)
    )

/// Gap state: if first.low > base, contiguous_from is 0
let contiguous_from_gap (s: Seq.seq interval) (base: nat)
  : Lemma (requires Seq.length s > 0 /\ (Seq.index s 0).low > base)
          (ensures contiguous_from s base == 0) = ()

/// add_range preserves gap state: if all intervals start above base and offset > base,
/// result's first element also starts above base
let rec add_range_preserves_gap
  (s: Seq.seq interval) (base offset: nat) (len: pos)
  : Lemma (requires range_map_wf s /\ offset > base /\
                    (Seq.length s = 0 \/ (Seq.index s 0).low > base))
          (ensures (let r = add_range s offset len in
                    Seq.length r > 0 /\
                    (Seq.index r 0).low > base))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else
      let hd = Seq.index s 0 in
      let tl = Seq.tail s in
      range_map_wf_tail s;
      if offset + len < hd.low then ()  // insert before: new first = {offset, len}, offset > base ✓
      else if high hd < offset then (
        // keep first (hd), hd.low > base ✓
        ()
      ) else (
        let merged_low = if offset < hd.low then offset else hd.low in
        let merged_high = if offset + len > high hd then offset + len else high hd in
        // merged_low = min(offset, hd.low). Both > base. So merged_low > base.
        assert (merged_low > base);
        if Seq.length tl = 0 then ()
        else (
          assert (separated hd (Seq.index tl 0));
          assert ((Seq.index tl 0).low > high hd);
          add_range_preserves_gap tl base merged_low (merged_high - merged_low)
        )
      )

/// add_range at exactly base establishes base_aligned when all existing intervals are above base
let add_range_at_base_establishes_aligned
  (s: Seq.seq interval) (base: nat) (len: pos)
  : Lemma (requires range_map_wf s /\
                    (Seq.length s = 0 \/ (Seq.index s 0).low > base))
          (ensures (let r = add_range s base len in
                    Seq.length r > 0 /\
                    (Seq.index r 0).low <= base /\
                    base <= high (Seq.index r 0)))
  = add_range_first_lower_bound s base len;
    add_range_first_high_bound s base len

(*** Lemmas bridging add_range to imperative implementation ***)

/// When all intervals have high < offset, add_range appends at the end
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec add_range_all_before (s: Seq.seq interval) (offset: nat) (len: pos)
  : Lemma (requires range_map_wf s /\
                    (forall (i:nat). i < Seq.length s ==> high (Seq.index s i) < offset))
          (ensures add_range s offset len == Seq.snoc s ({ low = offset; count = len }))
          (decreases Seq.length s)
  = let iv = { low = offset; count = len } in
    if Seq.length s = 0 then (
      // Base case: empty sequence
      // add_range s offset len = Seq.create 1 iv
      // Seq.snoc s iv = Seq.snoc Seq.empty iv = Seq.create 1 iv
      assert (add_range s offset len `Seq.equal` Seq.create 1 iv);
      assert (Seq.snoc s iv `Seq.equal` Seq.create 1 iv)
    ) else (
      // Inductive case: s is non-empty
      let hd = Seq.index s 0 in
      let tl = Seq.tail s in
      
      // From precondition, high hd < offset (using i=0)
      assert (high hd < offset);
      
      // By definition of add_range, since high hd < offset:
      // add_range s offset len = Seq.cons hd (add_range tl offset len)
      
      // Establish precondition for tail:
      // forall i < Seq.length tl. high (Seq.index tl i) < offset
      let tail_pre () : Lemma (forall (i:nat). i < Seq.length tl ==> high (Seq.index tl i) < offset) =
        let aux (i:nat{i < Seq.length tl}) : Lemma (high (Seq.index tl i) < offset) =
          assert (Seq.index tl i == Seq.index s (i + 1))
        in
        FStar.Classical.forall_intro aux
      in
      tail_pre ();
      
      // Apply IH to tail
      range_map_wf_tail s;
      add_range_all_before tl offset len;
      
      // Now we have: add_range tl offset len == Seq.snoc tl iv
      // So: add_range s offset len = Seq.cons hd (Seq.snoc tl iv)
      // Goal: Seq.cons hd (Seq.snoc tl iv) == Seq.snoc s iv
      
      // We need to show Seq.cons hd (Seq.snoc tl iv) == Seq.snoc (Seq.cons hd tl) iv
      // and Seq.cons hd tl == s
      
      let result_lhs = Seq.cons hd (Seq.snoc tl iv) in
      let result_rhs = Seq.snoc s iv in
      
      // Show sequences are equal by extensionality
      let len_eq () : Lemma (Seq.length result_lhs == Seq.length result_rhs) =
        assert (Seq.length result_lhs == Seq.length (Seq.snoc tl iv) + 1);
        assert (Seq.length (Seq.snoc tl iv) == Seq.length tl + 1);
        assert (Seq.length result_lhs == Seq.length tl + 2);
        assert (Seq.length s == Seq.length tl + 1);
        assert (Seq.length result_rhs == Seq.length s + 1);
        assert (Seq.length result_rhs == Seq.length tl + 2)
      in
      len_eq ();
      
      let elem_eq (i:nat{i < Seq.length result_lhs}) 
        : Lemma (Seq.index result_lhs i == Seq.index result_rhs i) =
        if i = 0 then (
          assert (Seq.index result_lhs 0 == hd);
          assert (Seq.index result_rhs 0 == Seq.index s 0);
          assert (Seq.index s 0 == hd)
        ) else if i < Seq.length result_lhs - 1 then (
          assert (Seq.index result_lhs i == Seq.index (Seq.snoc tl iv) (i - 1));
          assert (Seq.index (Seq.snoc tl iv) (i - 1) == Seq.index tl (i - 1));
          assert (Seq.index tl (i - 1) == Seq.index s i);
          assert (Seq.index result_rhs i == Seq.index s i)
        ) else (
          assert (i == Seq.length result_lhs - 1);
          assert (Seq.index result_lhs i == Seq.index (Seq.snoc tl iv) (i - 1));
          assert (i - 1 == Seq.length tl);
          assert (Seq.index (Seq.snoc tl iv) (Seq.length tl) == iv);
          assert (Seq.index result_rhs i == iv)
        )
      in
      FStar.Classical.forall_intro elem_eq;
      Seq.lemma_eq_intro result_lhs result_rhs
    )
#pop-options

/// When intervals [0..k) have high < offset, and offset+len < s[k].low, 
/// add_range inserts at position k
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec add_range_insert_no_overlap (s: Seq.seq interval) (offset: nat) (len: pos) (k: nat)
  : Lemma (requires range_map_wf s /\ k < Seq.length s /\
                    (forall (i:nat). i < k ==> high (Seq.index s i) < offset) /\
                    offset + len < (Seq.index s k).low)
          (ensures add_range s offset len == 
                   Seq.append (Seq.slice s 0 k) 
                              (Seq.cons ({ low = offset; count = len }) (Seq.slice s k (Seq.length s))))
          (decreases k)
  = let iv = { low = offset; count = len } in
    if k = 0 then (
      // Base case: insert at position 0
      let hd = Seq.index s 0 in
      
      // From precondition: offset + len < hd.low
      assert (offset + len < hd.low);
      
      // By definition of add_range, this branch returns Seq.cons iv s
      assert (add_range s offset len `Seq.equal` Seq.cons iv s);
      
      // RHS = Seq.append (Seq.slice s 0 0) (Seq.cons iv (Seq.slice s 0 (Seq.length s)))
      //     = Seq.append Seq.empty (Seq.cons iv s)
      //     = Seq.cons iv s
      assert (Seq.slice s 0 0 `Seq.equal` Seq.empty);
      assert (Seq.slice s 0 (Seq.length s) `Seq.equal` s);
      assert (Seq.cons iv s `Seq.equal` Seq.append Seq.empty (Seq.cons iv s))
    ) else (
      // Inductive case: k > 0
      let hd = Seq.index s 0 in
      let tl = Seq.tail s in
      
      // From precondition with i=0: high hd < offset
      assert (high hd < offset);
      
      // By definition of add_range, since high hd < offset:
      // add_range s offset len = Seq.cons hd (add_range tl offset len)
      
      // Establish preconditions for tail with k-1:
      // 1. range_map_wf tl
      range_map_wf_tail s;
      
      // 2. k - 1 < Seq.length tl
      assert (k < Seq.length s);
      assert (Seq.length tl == Seq.length s - 1);
      assert (k - 1 < Seq.length tl);
      
      // 3. forall i < k-1. high (Seq.index tl i) < offset
      let tail_forall () : Lemma (forall (i:nat). i < k - 1 ==> high (Seq.index tl i) < offset) =
        let aux (i:nat{i < k - 1}) : Lemma (high (Seq.index tl i) < offset) =
          assert (Seq.index tl i == Seq.index s (i + 1));
          assert (i + 1 < k)
        in
        FStar.Classical.forall_intro aux
      in
      tail_forall ();
      
      // 4. offset + len < (Seq.index tl (k-1)).low
      assert (Seq.index tl (k - 1) == Seq.index s k);
      assert (offset + len < (Seq.index tl (k - 1)).low);
      
      // Apply IH to tail with k-1
      add_range_insert_no_overlap tl offset len (k - 1);
      
      // IH gives us: add_range tl offset len == 
      //              Seq.append (Seq.slice tl 0 (k-1)) 
      //                         (Seq.cons iv (Seq.slice tl (k-1) (Seq.length tl)))
      
      // So: add_range s offset len = Seq.cons hd (add_range tl offset len)
      //                            = Seq.cons hd (Seq.append (Seq.slice tl 0 (k-1))
      //                                                      (Seq.cons iv (Seq.slice tl (k-1) (Seq.length tl))))
      
      // Goal: This equals Seq.append (Seq.slice s 0 k) (Seq.cons iv (Seq.slice s k (Seq.length s)))
      
      // Key observations:
      // - Seq.slice s 0 k = Seq.cons hd (Seq.slice tl 0 (k-1))
      // - Seq.slice s k (Seq.length s) = Seq.slice tl (k-1) (Seq.length tl)
      
      let lhs = add_range s offset len in
      let rhs = Seq.append (Seq.slice s 0 k) (Seq.cons iv (Seq.slice s k (Seq.length s))) in
      
      // Prove Seq.slice s 0 k == Seq.cons hd (Seq.slice tl 0 (k-1))
      let slice_s_eq () : Lemma (Seq.slice s 0 k `Seq.equal` Seq.cons hd (Seq.slice tl 0 (k - 1))) =
        let s_prefix = Seq.slice s 0 k in
        let tl_prefix = Seq.slice tl 0 (k - 1) in
        let expected = Seq.cons hd tl_prefix in
        
        assert (Seq.length s_prefix == k);
        assert (Seq.length expected == k);
        
        let aux (i:nat{i < k}) : Lemma (Seq.index s_prefix i == Seq.index expected i) =
          if i = 0 then (
            assert (Seq.index s_prefix 0 == Seq.index s 0);
            assert (Seq.index s 0 == hd);
            assert (Seq.index expected 0 == hd)
          ) else (
            assert (Seq.index s_prefix i == Seq.index s i);
            assert (Seq.index s i == Seq.index tl (i - 1));
            assert (Seq.index tl (i - 1) == Seq.index tl_prefix (i - 1));
            assert (Seq.index expected i == Seq.index tl_prefix (i - 1))
          )
        in
        FStar.Classical.forall_intro aux;
        Seq.lemma_eq_intro s_prefix expected
      in
      slice_s_eq ();
      
      // Prove Seq.slice s k (Seq.length s) == Seq.slice tl (k-1) (Seq.length tl)
      let slice_s_suffix_eq () : Lemma (Seq.slice s k (Seq.length s) `Seq.equal` Seq.slice tl (k - 1) (Seq.length tl)) =
        let s_suffix = Seq.slice s k (Seq.length s) in
        let tl_suffix = Seq.slice tl (k - 1) (Seq.length tl) in
        
        assert (Seq.length s_suffix == Seq.length s - k);
        assert (Seq.length tl_suffix == Seq.length tl - (k - 1));
        assert (Seq.length tl == Seq.length s - 1);
        assert (Seq.length tl_suffix == Seq.length s - k);
        
        let aux (i:nat{i < Seq.length s - k}) : Lemma (Seq.index s_suffix i == Seq.index tl_suffix i) =
          assert (Seq.index s_suffix i == Seq.index s (k + i));
          assert (Seq.index s (k + i) == Seq.index tl (k + i - 1));
          assert (Seq.index tl_suffix i == Seq.index tl (k - 1 + i))
        in
        FStar.Classical.forall_intro aux;
        Seq.lemma_eq_intro s_suffix tl_suffix
      in
      slice_s_suffix_eq ();
      
      // Now prove the final equality using associativity of append and cons
      // lhs = Seq.cons hd (Seq.append (Seq.slice tl 0 (k-1)) (Seq.cons iv (Seq.slice tl (k-1) (Seq.length tl))))
      // rhs = Seq.append (Seq.cons hd (Seq.slice tl 0 (k-1))) (Seq.cons iv (Seq.slice tl (k-1) (Seq.length tl)))
      
      // Use the property: Seq.cons x (Seq.append a b) == Seq.append (Seq.cons x a) b
      let cons_append_assoc (x: interval) (a b: Seq.seq interval)
        : Lemma (Seq.cons x (Seq.append a b) `Seq.equal` Seq.append (Seq.cons x a) b) =
        let lhs = Seq.cons x (Seq.append a b) in
        let rhs = Seq.append (Seq.cons x a) b in
        assert (Seq.length lhs == 1 + Seq.length a + Seq.length b);
        assert (Seq.length rhs == (1 + Seq.length a) + Seq.length b);
        let aux (i:nat{i < Seq.length lhs}) : Lemma (Seq.index lhs i == Seq.index rhs i) =
          if i = 0 then ()
          else if i <= Seq.length a then ()
          else ()
        in
        FStar.Classical.forall_intro aux;
        Seq.lemma_eq_intro lhs rhs
      in
      cons_append_assoc hd (Seq.slice tl 0 (k - 1)) (Seq.cons iv (Seq.slice tl (k - 1) (Seq.length tl)));
      
      Seq.lemma_eq_intro lhs rhs
    )
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec add_range_skip_prefix (s: Seq.seq interval) (offset: nat) (len: pos) (k: nat)
  : Lemma (requires range_map_wf s /\ k <= Seq.length s /\
                    (forall (i:nat). i < k ==> high (Seq.index s i) < offset))
          (ensures add_range s offset len ==
                   Seq.append (Seq.slice s 0 k) (add_range (Seq.slice s k (Seq.length s)) offset len))
          (decreases k) =
  if k = 0 then (
    // Base case: Seq.slice s 0 0 is empty, Seq.slice s 0 n is s
    assert (Seq.slice s 0 0 `Seq.equal` Seq.empty);
    assert (Seq.slice s 0 (Seq.length s) `Seq.equal` s);
    Seq.lemma_eq_intro (Seq.slice s 0 0) Seq.empty;
    Seq.lemma_eq_intro (Seq.slice s 0 (Seq.length s)) s;
    assert (Seq.append Seq.empty (add_range s offset len) `Seq.equal` add_range s offset len);
    Seq.lemma_eq_intro (Seq.append Seq.empty (add_range s offset len)) (add_range s offset len)
  ) else (
    // Inductive case: k > 0
    let hd = Seq.index s 0 in
    let tl = Seq.tail s in
    let n = Seq.length s in
    
    // hd has high hd < offset (from forall with i=0)
    assert (high hd < offset);
    
    // So add_range s offset len takes the branch: Seq.cons hd (add_range tl offset len)
    assert (add_range s offset len == Seq.cons hd (add_range tl offset len));
    
    // Apply IH on tl with k-1
    // Need: range_map_wf tl
    range_map_wf_tail s;
    
    // Need: forall for the tail
    let forall_tail (i:nat{i < k - 1}) : Lemma (high (Seq.index tl i) < offset) =
      assert (Seq.length tl == n - 1);
      assert (k <= n);
      assert (i < k - 1);
      assert (i < n - 1);
      assert (i < Seq.length tl);
      assert (Seq.index tl i == Seq.index s (i + 1));
      assert (i + 1 < k);
      assert (high (Seq.index s (i + 1)) < offset)
    in
    FStar.Classical.forall_intro forall_tail;
    
    add_range_skip_prefix tl offset len (k - 1);
    
    // From IH: add_range tl offset len == Seq.append (Seq.slice tl 0 (k-1)) (add_range (Seq.slice tl (k-1) (Seq.length tl)) offset len)
    
    // Prove Seq.slice s 0 k == Seq.cons hd (Seq.slice tl 0 (k-1))
    let slice_prefix_eq () : Lemma (Seq.slice s 0 k `Seq.equal` Seq.cons hd (Seq.slice tl 0 (k - 1))) =
      let s_prefix = Seq.slice s 0 k in
      let expected = Seq.cons hd (Seq.slice tl 0 (k - 1)) in
      
      assert (Seq.length s_prefix == k);
      assert (Seq.length expected == 1 + (k - 1));
      assert (Seq.length expected == k);
      
      let aux (i:nat{i < k}) : Lemma (Seq.index s_prefix i == Seq.index expected i) =
        if i = 0 then (
          assert (Seq.index s_prefix 0 == Seq.index s 0);
          assert (Seq.index s 0 == hd);
          assert (Seq.index expected 0 == hd)
        ) else (
          assert (Seq.index s_prefix i == Seq.index s i);
          assert (Seq.index s i == Seq.index tl (i - 1));
          assert (Seq.index (Seq.slice tl 0 (k - 1)) (i - 1) == Seq.index tl (i - 1));
          assert (Seq.index expected i == Seq.index (Seq.slice tl 0 (k - 1)) (i - 1))
        )
      in
      FStar.Classical.forall_intro aux;
      Seq.lemma_eq_intro s_prefix expected
    in
    slice_prefix_eq ();
    
    // Prove Seq.slice s k n == Seq.slice tl (k-1) (Seq.length tl)
    let slice_suffix_eq () : Lemma (Seq.slice s k n `Seq.equal` Seq.slice tl (k - 1) (Seq.length tl)) =
      let s_suffix = Seq.slice s k n in
      let tl_suffix = Seq.slice tl (k - 1) (Seq.length tl) in
      
      assert (Seq.length s_suffix == n - k);
      assert (Seq.length tl == n - 1);
      assert (Seq.length tl_suffix == (n - 1) - (k - 1));
      assert (Seq.length tl_suffix == n - k);
      
      let aux (i:nat{i < n - k}) : Lemma (Seq.index s_suffix i == Seq.index tl_suffix i) =
        assert (Seq.index s_suffix i == Seq.index s (k + i));
        assert (Seq.index s (k + i) == Seq.index tl (k + i - 1));
        assert (Seq.index tl_suffix i == Seq.index tl (k - 1 + i))
      in
      FStar.Classical.forall_intro aux;
      Seq.lemma_eq_intro s_suffix tl_suffix
    in
    slice_suffix_eq ();
    
    // Now prove: Seq.cons hd (Seq.append a b) == Seq.append (Seq.cons hd a) b
    let cons_append_assoc (#a:Type) (x:a) (s1 s2: Seq.seq a)
      : Lemma (Seq.cons x (Seq.append s1 s2) `Seq.equal` Seq.append (Seq.cons x s1) s2) =
      let lhs = Seq.cons x (Seq.append s1 s2) in
      let rhs = Seq.append (Seq.cons x s1) s2 in
      
      assert (Seq.length lhs == 1 + Seq.length s1 + Seq.length s2);
      assert (Seq.length rhs == (1 + Seq.length s1) + Seq.length s2);
      
      let aux (i:nat{i < Seq.length lhs}) : Lemma (Seq.index lhs i == Seq.index rhs i) =
        if i = 0 then ()
        else if i <= Seq.length s1 then ()
        else ()
      in
      FStar.Classical.forall_intro aux;
      Seq.lemma_eq_intro lhs rhs
    in
    
    cons_append_assoc hd 
                      (Seq.slice tl 0 (k - 1)) 
                      (add_range (Seq.slice tl (k - 1) (Seq.length tl)) offset len);
    
    // Final equality follows
    Seq.lemma_eq_intro 
      (add_range s offset len)
      (Seq.append (Seq.slice s 0 k) (add_range (Seq.slice s k n) offset len))
  )
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

/// Helper: prove transitive sortedness from range_map_wf
let rec range_map_wf_sorted (s: Seq.seq interval) (i j: nat)
  : Lemma (requires range_map_wf s /\ i < j /\ j < Seq.length s)
          (ensures high (Seq.index s i) < (Seq.index s j).low)
          (decreases %[Seq.length s; j - i]) =
  if i + 1 = j then begin
    // Adjacent case: directly from wf
    if i = 0 then begin
      assert (separated (Seq.index s 0) (Seq.index s 1))
    end else begin
      range_map_wf_tail s;
      range_map_wf_sorted (Seq.tail s) (i - 1) (j - 1)
    end
  end else begin
    // Transitive case: i < i+1 < j
    range_map_wf_sorted s i (i + 1);
    range_map_wf_sorted s (i + 1) j;
    // Now we have: high s[i] < s[i+1].low < high s[i+1] < s[j].low
    assert (high (Seq.index s i) < (Seq.index s (i + 1)).low);
    assert ((Seq.index s (i + 1)).low < high (Seq.index s (i + 1)));
    assert (high (Seq.index s (i + 1)) < (Seq.index s j).low)
  end

/// Helper: compute final merged high value after absorbing k elements
let rec merge_absorbed_high (s: Seq.seq interval) (mh: nat) (k: nat{k <= Seq.length s})
  : Tot nat (decreases k) =
  if k = 0 then mh
  else let hd = Seq.index s 0 in
       merge_absorbed_high (Seq.tail s) (if mh > high hd then mh else high hd) (k - 1)

/// Monotonicity of merge_absorbed_high
let rec merge_absorbed_high_mono (s: Seq.seq interval) (mh: nat) (k: nat{k <= Seq.length s})
  : Lemma (ensures merge_absorbed_high s mh k >= mh)
          (decreases k) =
  if k = 0 then ()
  else merge_absorbed_high_mono (Seq.tail s) (if mh > high (Seq.index s 0) then mh else high (Seq.index s 0)) (k - 1)

/// Unfold from the right: merge_absorbed_high(s, mh, k+1) == max(merge_absorbed_high(s, mh, k), high(s[k]))
/// This enables imperative loop invariant tracking where the last element absorbed is s[k]
let rec merge_absorbed_high_unfold_right (s: Seq.seq interval) (mh: nat) (k: nat{k < Seq.length s})
  : Lemma (ensures (let mh_k = merge_absorbed_high s mh k in
                    merge_absorbed_high s mh (k + 1) ==
                    (if mh_k > high (Seq.index s k) then mh_k else high (Seq.index s k))))
          (decreases k) =
  if k = 0 then begin
    // Base case: merge_absorbed_high s mh 1 == max(mh, high(s[0]))
    // LHS: merge_absorbed_high s mh 1
    //      = merge_absorbed_high (Seq.tail s) (max(mh, high(s[0]))) 0
    //      = max(mh, high(s[0]))
    // RHS: merge_absorbed_high s mh 0 = mh, so max(mh, high(s[0]))
    ()
  end else begin
    // Inductive case: use IH on (Seq.tail s) with mh' = max(mh, high(s[0])) and k-1
    let mh' = if mh > high (Seq.index s 0) then mh else high (Seq.index s 0) in
    // IH gives: merge_absorbed_high (Seq.tail s) mh' k ==
    //           max(merge_absorbed_high (Seq.tail s) mh' (k-1), high((Seq.tail s)[k-1]))
    merge_absorbed_high_unfold_right (Seq.tail s) mh' (k - 1);
    // Note: Seq.index (Seq.tail s) (k - 1) == Seq.index s k
    assert (Seq.index (Seq.tail s) (k - 1) == Seq.index s k);
    // LHS: merge_absorbed_high s mh (k+1)
    //      = merge_absorbed_high (Seq.tail s) mh' k        (by definition)
    //      = max(merge_absorbed_high (Seq.tail s) mh' (k-1), high(s[k]))  (by IH)
    //      = max(merge_absorbed_high s mh k, high(s[k]))   (by definition of mah(s, mh, k))
    ()
  end

/// Step lemma: merge_absorbed_high(s, mh, k+1) == merge_absorbed_high(tail s, max(mh, high(s[0])), k)
let merge_absorbed_high_step (s: Seq.seq interval) (mh: nat) (k: nat{k < Seq.length s})
  : Lemma (ensures merge_absorbed_high s mh (k + 1) ==
                   merge_absorbed_high (Seq.tail s) (if mh > high (Seq.index s 0) then mh else high (Seq.index s 0)) k) = ()

/// Shift: merge_absorbed_high on slice (i..n) relates to original seq indexing
let merge_absorbed_high_slice_step (s: Seq.seq interval) (base: nat) (mh: nat) (k: nat)
  : Lemma (requires base + k + 1 <= Seq.length s /\ base + 1 <= Seq.length s)
          (ensures (let suffix = Seq.slice s base (Seq.length s) in
                    let mh' = (if mh > high (Seq.index s base) then mh else high (Seq.index s base)) in
                    Seq.lemma_eq_intro (Seq.tail suffix) (Seq.slice s (base + 1) (Seq.length s));
                    merge_absorbed_high suffix mh (k + 1) ==
                    merge_absorbed_high (Seq.slice s (base + 1) (Seq.length s)) mh' k)) =
  let suffix = Seq.slice s base (Seq.length s) in
  Seq.lemma_eq_intro (Seq.tail suffix) (Seq.slice s (base + 1) (Seq.length s));
  merge_absorbed_high_step suffix mh k

/// Lemma: With range_map_wf, high values are strictly increasing
let rec high_values_increasing (s: Seq.seq interval) (i j: nat)
  : Lemma (requires range_map_wf s /\ i < j /\ j < Seq.length s)
          (ensures high (Seq.index s i) < high (Seq.index s j))
          (decreases j - i) =
  if i + 1 = j then begin
    // Adjacent case: from wf, high(s[i]) < s[j].low <= s[j].low < high(s[j])
    range_map_wf_sorted s i j;
    assert (high (Seq.index s i) < (Seq.index s j).low);
    assert ((Seq.index s j).low < high (Seq.index s j))
  end else begin
    // Transitive case: i < j-1 < j
    high_values_increasing s i (j - 1);
    high_values_increasing s (j - 1) j;
    assert (high (Seq.index s i) < high (Seq.index s (j - 1)));
    assert (high (Seq.index s (j - 1)) < high (Seq.index s j))
  end

/// Lemma: For wf sequences with k > 0, merge_absorbed_high equals max(mh, high(s[k-1]))
/// because high values are strictly increasing, so high(s[k-1]) dominates all earlier highs
let rec merge_absorbed_high_eq_max_last (s: Seq.seq interval) (mh: nat) (k: nat)
  : Lemma (requires range_map_wf s /\ 0 < k /\ k <= Seq.length s)
          (ensures merge_absorbed_high s mh k == 
                   (if mh > high (Seq.index s (k - 1)) then mh else high (Seq.index s (k - 1))))
          (decreases k) =
  if k = 1 then begin
    // Base case: merge_absorbed_high s mh 1 == max(mh, high(s[0]))
    ()
  end else begin
    // k > 1: by IH, merge_absorbed_high s mh (k-1) == max(mh, high(s[k-2]))
    merge_absorbed_high_eq_max_last s mh (k - 1);
    // By unfold_right: merge_absorbed_high s mh k == max(mah(s, mh, k-1), high(s[k-1]))
    merge_absorbed_high_unfold_right s mh (k - 1);
    // So: merge_absorbed_high s mh k == max(max(mh, high(s[k-2])), high(s[k-1]))
    // By wf, high(s[k-2]) < high(s[k-1])
    high_values_increasing s (k - 2) (k - 1);
    assert (high (Seq.index s (k - 2)) < high (Seq.index s (k - 1)));
    // Therefore: max(max(mh, high(s[k-2])), high(s[k-1])) == max(mh, high(s[k-1]))
    ()
  end

/// Main lemma: From the running-max invariant plus wf, derive that mh0 covers absorbed elements
/// 
/// If merge_absorbed_high(s, mh0, k) >= s[k].low for some k, and range_map_wf holds,
/// then mh0 >= s[k].low.
/// 
/// Proof: By merge_absorbed_high_eq_max_last, mah(s, mh0, k) = max(mh0, high(s[k-1])).
///        By wf, high(s[k-1]) < s[k].low (from range_map_wf_sorted).
///        So max(mh0, high(s[k-1])) >= s[k].low and high(s[k-1]) < s[k].low
///        implies mh0 >= s[k].low.
let mh0_covers_absorbed (s: Seq.seq interval) (mh0: nat) (k: nat)
  : Lemma (requires range_map_wf s /\ 
                    0 < k /\ k < Seq.length s /\
                    merge_absorbed_high s mh0 k >= (Seq.index s k).low)
          (ensures mh0 >= (Seq.index s k).low) =
  // Step 1: Express merge_absorbed_high as max(mh0, high(s[k-1]))
  merge_absorbed_high_eq_max_last s mh0 k;
  assert (merge_absorbed_high s mh0 k == 
          (if mh0 > high (Seq.index s (k - 1)) then mh0 else high (Seq.index s (k - 1))));
  
  // Step 2: Use wf to show high(s[k-1]) < s[k].low
  range_map_wf_sorted s (k - 1) k;
  assert (high (Seq.index s (k - 1)) < (Seq.index s k).low);
  
  // Step 3: From merge_absorbed_high s mh0 k >= s[k].low and high(s[k-1]) < s[k].low,
  //         deduce mh0 >= s[k].low
  let mah_val = merge_absorbed_high s mh0 k in
  let s_k_low = (Seq.index s k).low in
  let high_prev = high (Seq.index s (k - 1)) in
  
  assert (mah_val >= s_k_low);
  assert (high_prev < s_k_low);
  assert (mah_val == (if mh0 > high_prev then mh0 else high_prev));
  
  // Since high_prev < s_k_low and max(mh0, high_prev) >= s_k_low,
  // we must have mh0 >= s_k_low
  if mh0 > high_prev then
    assert (mh0 >= s_k_low)
  else begin
    assert (mah_val == high_prev);
    assert (high_prev >= s_k_low);
    assert (False)  // Contradiction: high_prev < s_k_low but also high_prev >= s_k_low
  end

/// Lemma 1: Trivial unfolding lemma for the merge branch
let add_range_merge_step (s: Seq.seq interval) (offset: nat) (len: pos)
  : Lemma (requires Seq.length s > 0 /\
                    (let hd = Seq.index s 0 in
                     ~(offset + len < hd.low) /\ ~(high hd < offset)))
          (ensures (let hd = Seq.index s 0 in
                    let tl = Seq.tail s in
                    let ml = (if offset < hd.low then offset else hd.low) in
                    let mh = (if offset + len > high hd then offset + len else high hd) in
                    mh > ml /\
                    add_range s offset len == add_range tl ml (mh - ml)))
  = let hd = Seq.index s 0 in
    let ml = (if offset < hd.low then offset else hd.low) in
    let mh = (if offset + len > high hd then offset + len else high hd) in
    // Show mh > ml
    assert (offset + len > offset);
    assert (~(offset + len < hd.low));
    assert (offset + len >= hd.low);
    assert (~(high hd < offset));
    assert (high hd >= offset);
    assert (mh >= offset);
    assert (ml <= offset);
    // Unfold add_range definition
    assert (add_range s offset len == 
            (let hd' = Seq.index s 0 in
             let tl' = Seq.tail s in
             if offset + len < hd'.low then Seq.cons ({ low = offset; count = len }) s
             else if high hd' < offset then Seq.cons hd' (add_range tl' offset len)
             else
               let merged_low = if offset < hd'.low then offset else hd'.low in
               let merged_high = if offset + len > high hd' then offset + len else high hd' in
               add_range tl' merged_low (merged_high - merged_low)))

/// Lemma 2: Characterize recursive merge
let rec add_range_merge_scan (s: Seq.seq interval) (ml: nat) (mh: nat) (k: nat)
  : Lemma (requires range_map_wf s /\ mh > ml /\
                    k <= Seq.length s /\
                    (k > 0 ==> ml <= (Seq.index s 0).low) /\
                    (forall (i:nat). i < k ==> mh >= (Seq.index s i).low) /\
                    (k = Seq.length s \/ mh < (Seq.index s k).low))
          (ensures (let fh = merge_absorbed_high s mh k in
                    fh > ml /\
                    add_range s ml (mh - ml) ==
                    Seq.append (Seq.create 1 ({ low = ml; count = fh - ml }))
                               (Seq.slice s k (Seq.length s))))
          (decreases k) =
  if k = 0 then begin
    // No overlaps to absorb
    merge_absorbed_high_mono s mh 0;
    assert (merge_absorbed_high s mh 0 = mh);
    
    if Seq.length s = 0 then begin
      // Empty sequence case
      let iv = { low = ml; count = mh - ml } in
      assert (add_range s ml (mh - ml) == Seq.create 1 iv);
      Seq.lemma_eq_intro (Seq.slice s 0 0) Seq.empty;
      Seq.lemma_eq_intro (Seq.append (Seq.create 1 iv) Seq.empty) (Seq.create 1 iv)
    end else begin
      // mh < s[0].low, insert before first element
      let iv = { low = ml; count = mh - ml } in
      assert (ml + (mh - ml) = mh);
      assert (mh < (Seq.index s 0).low);
      assert (add_range s ml (mh - ml) == Seq.cons iv s);
      Seq.lemma_eq_intro (Seq.slice s 0 (Seq.length s)) s;
      Seq.lemma_eq_intro (Seq.cons iv s) (Seq.append (Seq.create 1 iv) s)
    end
  end else begin
    // k > 0: first element overlaps
    let hd = Seq.index s 0 in
    let tl = Seq.tail s in
    let n = Seq.length s in
    
    // Establish overlap conditions
    assert (mh >= hd.low); // from forall with i=0
    assert (~(ml + (mh - ml) < hd.low)); // since ml + (mh - ml) = mh >= hd.low
    
    // Show ~(high hd < ml)
    assert (ml <= hd.low); // from precondition k > 0
    assert (high hd = hd.low + hd.count);
    assert (hd.count > 0);
    assert (high hd > hd.low);
    assert (high hd >= ml); // since high hd > hd.low >= ml
    assert (~(high hd < ml));
    
    // Merge branch is taken
    let ml' = (if ml < hd.low then ml else hd.low) in
    let mh' = (if mh > high hd then mh else high hd) in
    
    // ml' = ml since ml <= hd.low
    assert (ml' = ml);
    
    // mh' = max(mh, high hd)
    assert (mh' >= mh);
    assert (mh' >= high hd);
    assert (mh' > ml);
    
    // Establish IH preconditions for tl with k-1
    range_map_wf_tail s;
    assert (range_map_wf tl);
    
    // Show: forall i < k-1. mh' >= (Seq.index tl i).low
    // Seq.index tl i = Seq.index s (i+1)
    assert (forall (i:nat). i < k - 1 ==> (
      let si1 = Seq.index s (i + 1) in
      let ti = Seq.index tl i in
      ti == si1
    ));
    
    assert (forall (i:nat). i < k - 1 ==> mh >= (Seq.index s (i + 1)).low);
    assert (forall (i:nat). i < k - 1 ==> mh' >= (Seq.index tl i).low);
    
    // Show: k-1 = Seq.length tl \/ mh' < (Seq.index tl (k-1)).low
    assert (Seq.length tl = n - 1);
    if k = n then begin
      assert (k - 1 = Seq.length tl)
    end else begin
      // mh < s[k].low, need to show mh' < s[k].low
      assert (mh < (Seq.index s k).low);
      
      // By wf, high hd < s[1].low
      if k >= 2 then begin
        assert (separated hd (Seq.index s 1));
        assert (high hd < (Seq.index s 1).low);
        range_map_wf_sorted s 1 k;
        assert (high (Seq.index s 1) < (Seq.index s k).low);
        assert ((Seq.index s 1).low < high (Seq.index s 1));
        assert ((Seq.index s 1).low < (Seq.index s k).low);
        assert (high hd < (Seq.index s 1).low);
        assert (high hd < (Seq.index s k).low)
      end else begin
        // k = 1, so we need mh' < s[1].low
        assert (k = 1);
        assert (separated hd (Seq.index s 1));
        assert (high hd < (Seq.index s 1).low)
      end;
      
      // mh' = max(mh, high hd), both < s[k].low
      assert (mh' < (Seq.index s k).low);
      assert (Seq.index tl (k - 1) == Seq.index s k);
      assert (mh' < (Seq.index tl (k - 1)).low)
    end;
    
    // Show: k-1 > 0 ==> ml <= (Seq.index tl 0).low
    if k - 1 > 0 then begin
      assert (k >= 2);
      assert (Seq.index tl 0 == Seq.index s 1);
      assert (ml <= hd.low);
      assert (separated hd (Seq.index s 1));
      assert (high hd < (Seq.index s 1).low);
      assert (hd.low < (Seq.index s 1).low);
      assert (ml <= (Seq.index tl 0).low)
    end;
    
    // Apply IH
    add_range_merge_scan tl ml mh' (k - 1);
    
    // Now we have: add_range tl ml (mh' - ml) = 
    //              append (create 1 {ml, merge_absorbed_high tl mh' (k-1) - ml})
    //                     (slice tl (k-1) (length tl))
    
    // Show: merge_absorbed_high s mh k = merge_absorbed_high tl mh' (k-1)
    assert (merge_absorbed_high s mh k = 
            merge_absorbed_high tl (if mh > high hd then mh else high hd) (k - 1));
    assert (merge_absorbed_high s mh k = merge_absorbed_high tl mh' (k - 1));
    
    let fh = merge_absorbed_high s mh k in
    
    // Show: add_range s ml (mh - ml) = add_range tl ml (mh' - ml)
    assert (add_range s ml (mh - ml) == add_range tl ml (mh' - ml));
    
    // From IH: add_range tl ml (mh' - ml) = append (create 1 {ml, fh - ml}) (slice tl (k-1) (n-1))
    
    // Show: slice tl (k-1) (n-1) = slice s k n
    assert (forall (i:nat). i < Seq.length (Seq.slice tl (k - 1) (n - 1)) ==> 
            Seq.index (Seq.slice tl (k - 1) (n - 1)) i == 
            Seq.index (Seq.slice s k n) i);
    Seq.lemma_eq_intro (Seq.slice tl (k - 1) (n - 1)) (Seq.slice s k n);
    
    // Conclude
    Seq.lemma_eq_intro 
      (add_range s ml (mh - ml))
      (Seq.append (Seq.create 1 ({ low = ml; count = fh - ml }))
                  (Seq.slice s k n))
  end

#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"

let rec range_map_wf_slice (s: Seq.seq interval) (i: nat)
  : Lemma (requires range_map_wf s /\ i <= Seq.length s)
          (ensures range_map_wf (Seq.slice s i (Seq.length s)))
          (decreases i) =
  if i = 0 then Seq.lemma_eq_intro (Seq.slice s 0 (Seq.length s)) s
  else begin
    range_map_wf_tail s;
    range_map_wf_slice (Seq.tail s) (i - 1);
    Seq.lemma_eq_intro (Seq.slice s i (Seq.length s)) (Seq.slice (Seq.tail s) (i - 1) (Seq.length (Seq.tail s)))
  end

#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40 --split_queries always"

/// Helper: the suffix part of the merge
/// add_range (slice s iv n) offset len == append (create 1 merged) (slice s j n)
let add_range_merge_suffix (s: Seq.seq interval) (offset: nat) (len: pos) (iv j: nat)
  : Lemma (requires range_map_wf s /\
                    iv < Seq.length s /\ j > iv /\ j <= Seq.length s /\
                    ~(offset + len < (Seq.index s iv).low) /\
                    ~(high (Seq.index s iv) < offset) /\
                    (let ml = (if offset < (Seq.index s iv).low then offset else (Seq.index s iv).low) in
                     let mh0 = (if offset + len > high (Seq.index s iv) then offset + len else high (Seq.index s iv)) in
                     (forall (i:nat). i > iv /\ i < j ==> mh0 >= (Seq.index s i).low) /\
                     (j = Seq.length s \/ mh0 < (Seq.index s j).low)))
          (ensures (let ml = (if offset < (Seq.index s iv).low then offset else (Seq.index s iv).low) in
                    let mh0 = (if offset + len > high (Seq.index s iv) then offset + len else high (Seq.index s iv)) in
                    let suffix_tail = Seq.slice s (iv + 1) (Seq.length s) in
                    let fh = merge_absorbed_high suffix_tail mh0 (j - iv - 1) in
                    fh > ml /\
                    add_range (Seq.slice s iv (Seq.length s)) offset len ==
                    Seq.append (Seq.create 1 ({ low = ml; count = fh - ml }))
                               (Seq.slice s j (Seq.length s)))) =
  let n = Seq.length s in
  let ml = (if offset < (Seq.index s iv).low then offset else (Seq.index s iv).low) in
  let mh0 = (if offset + len > high (Seq.index s iv) then offset + len else high (Seq.index s iv)) in
  let k = j - iv - 1 in
  let suffix = Seq.slice s iv n in
  let stail = Seq.tail suffix in

  // merge step on first element of suffix
  range_map_wf_slice s iv;
  add_range_merge_step suffix offset len;

  // merge scan using stail
  Seq.lemma_eq_intro stail (Seq.slice s (iv + 1) n);
  range_map_wf_slice s (iv + 1);
  if k > 0 then range_map_wf_sorted s iv (iv + 1);
  add_range_merge_scan stail ml mh0 k;
  merge_absorbed_high_mono stail mh0 k;

  // Relate slice stail k to slice s j n
  Seq.lemma_eq_intro (Seq.slice stail k (Seq.length stail)) (Seq.slice s j n)

/// Full merge: combines skip_prefix + merge_suffix
let add_range_merge_full (s: Seq.seq interval) (offset: nat) (len: pos) (iv j: nat)
  : Lemma (requires range_map_wf s /\
                    iv < Seq.length s /\ j > iv /\ j <= Seq.length s /\
                    (forall (i:nat). i < iv ==> high (Seq.index s i) < offset) /\
                    ~(offset + len < (Seq.index s iv).low) /\
                    ~(high (Seq.index s iv) < offset) /\
                    (let ml = (if offset < (Seq.index s iv).low then offset else (Seq.index s iv).low) in
                     let mh0 = (if offset + len > high (Seq.index s iv) then offset + len else high (Seq.index s iv)) in
                     (forall (i:nat). i > iv /\ i < j ==> mh0 >= (Seq.index s i).low) /\
                     (j = Seq.length s \/ mh0 < (Seq.index s j).low)))
          (ensures (let ml = (if offset < (Seq.index s iv).low then offset else (Seq.index s iv).low) in
                    let mh0 = (if offset + len > high (Seq.index s iv) then offset + len else high (Seq.index s iv)) in
                    let suffix_tail = Seq.slice s (iv + 1) (Seq.length s) in
                    let fh = merge_absorbed_high suffix_tail mh0 (j - iv - 1) in
                    fh > ml /\
                    add_range s offset len ==
                    Seq.append (Seq.slice s 0 iv)
                               (Seq.append (Seq.create 1 ({ low = ml; count = fh - ml }))
                                           (Seq.slice s j (Seq.length s))))) =
  add_range_skip_prefix s offset len iv;
  add_range_merge_suffix s offset len iv j

/// Explicit-mh0 version: takes mh0 as a parameter for easier SMT matching
let add_range_merge_full_explicit (s: Seq.seq interval) (offset: nat) (len: pos) (iv j: nat) (mh0: nat)
  : Lemma (requires range_map_wf s /\
                    iv < Seq.length s /\ j > iv /\ j <= Seq.length s /\
                    (forall (i:nat). i < iv ==> high (Seq.index s i) < offset) /\
                    ~(offset + len < (Seq.index s iv).low) /\
                    ~(high (Seq.index s iv) < offset) /\
                    mh0 == (if offset + len > high (Seq.index s iv) then offset + len else high (Seq.index s iv)) /\
                    (forall (i:nat). i > iv /\ i < j ==> mh0 >= (Seq.index s i).low) /\
                    (j = Seq.length s \/ mh0 < (Seq.index s j).low))
          (ensures (let ml = (if offset < (Seq.index s iv).low then offset else (Seq.index s iv).low) in
                    let suffix_tail = Seq.slice s (iv + 1) (Seq.length s) in
                    let fh = merge_absorbed_high suffix_tail mh0 (j - iv - 1) in
                    fh > ml /\
                    add_range s offset len ==
                    Seq.append (Seq.slice s 0 iv)
                               (Seq.append (Seq.create 1 ({ low = ml; count = fh - ml }))
                                           (Seq.slice s j (Seq.length s))))) =
  add_range_merge_full s offset len iv j

#pop-options

(*** Length bounds ***)

/// drain_ranges never increases the number of intervals
let rec drain_ranges_length (s: Seq.seq interval) (n: nat)
  : Lemma (ensures Seq.length (drain_ranges s n) <= Seq.length s)
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else
    let hd = Seq.index s 0 in
    let tl = Seq.tail s in
    drain_ranges_length tl n

/// Separated intervals span at least 2n-1 offsets within [lo, bound).
/// From range_map_wf (gaps >= 1) and count >= 1 per interval.
let rec wf_count_bound (s: Seq.seq interval) (lo bound: nat)
  : Lemma (requires range_map_wf s /\ range_map_bounded s bound /\
                    Seq.length s > 0 /\ (Seq.index s 0).low >= lo)
          (ensures Seq.length s + Seq.length s <= bound - lo + 1)
          (decreases Seq.length s) =
  let hd = Seq.index s 0 in
  if Seq.length s = 1 then
    // Single interval: count >= 1, so high hd <= bound and hd.low >= lo
    // high hd - lo >= hd.count >= 1 = 2*1 - 1
    ()
  else begin
    let tl = Seq.tail s in
    let hd2 = Seq.index s 1 in
    // separated hd hd2: high hd < hd2.low (gap >= 1)
    assert (Seq.index tl 0 == hd2);
    range_map_wf_tail s;
    // range_map_bounded for tail
    let aux (i:nat{i < Seq.length tl}) : Lemma (high (Seq.index tl i) <= bound) =
      assert (Seq.index tl i == Seq.index s (i + 1))
    in
    Classical.forall_intro aux;
    // Recurse: 2*(|tl|) - 1 <= bound - hd2.low
    wf_count_bound tl hd2.low bound;
    // hd spans [hd.low, high hd), count >= 1
    // gap: hd2.low > high hd, so hd2.low >= high hd + 1
    assert (high hd - hd.low >= 1);  // count >= 1
    assert (hd2.low - high hd >= 1); // separated gap >= 1
    assert (hd.low >= lo)
  end

/// add_range increases length by at most 1
let rec add_range_length (s: Seq.seq interval) (offset: nat) (len: pos)
  : Lemma (ensures Seq.length (add_range s offset len) <= Seq.length s + 1)
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else
    let hd = Seq.index s 0 in
    let tl = Seq.tail s in
    if offset + len < hd.low then ()
    else if high hd < offset then
      add_range_length tl offset len
    else
      let merged_low = if offset < hd.low then offset else hd.low in
      let merged_high = if offset + len > high hd then offset + len else high hd in
      add_range_length tl merged_low (merged_high - merged_low)

/// Drain the first interval (or trim it) up to new_bo.
/// Precondition: first interval contains new_bo (base_aligned + n <= cf).
let drain_repr (s: Seq.seq interval) (new_bo: nat)
  : Seq.seq interval =
  if Seq.length s = 0 then Seq.empty
  else
    let first = Seq.index s 0 in
    if high first <= new_bo then Seq.tail s
    else if first.low < new_bo then
      Seq.cons ({ low = new_bo; count = high first - new_bo }) (Seq.tail s)
    else s

/// drain_repr preserves range_map_wf
let drain_repr_wf (s: Seq.seq interval) (new_bo: nat)
  : Lemma (requires range_map_wf s /\ Seq.length s > 0 /\
                    (Seq.index s 0).low <= new_bo /\ new_bo <= high (Seq.index s 0))
          (ensures range_map_wf (drain_repr s new_bo)) =
  let first = Seq.index s 0 in
  let tl = Seq.tail s in
  if high first <= new_bo then ()
  else if first.low < new_bo then begin
    let trimmed = { low = new_bo; count = high first - new_bo } in
    if Seq.length tl = 0 then
      range_map_wf_cons trimmed tl
    else begin
      let next = Seq.index tl 0 in
      assert (Seq.index s 1 == next);
      assert (separated first next);
      assert (high first < next.low);
      assert (high trimmed == high first);
      assert (high trimmed < next.low);
      assert (separated trimmed next);
      range_map_wf_cons trimmed tl
    end
  end else ()

/// drain_repr preserves range_map_bounded
let drain_repr_bounded (s: Seq.seq interval) (new_bo: nat) (bound: nat)
  : Lemma (requires range_map_bounded s bound /\ Seq.length s > 0 /\
                    (Seq.index s 0).low <= new_bo /\ new_bo <= high (Seq.index s 0))
          (ensures range_map_bounded (drain_repr s new_bo) bound) =
  let first = Seq.index s 0 in
  let result = drain_repr s new_bo in
  if high first <= new_bo then begin
    let tl = Seq.tail s in
    let aux (i:nat{i < Seq.length tl})
      : Lemma (high (Seq.index tl i) <= bound)
      = assert (Seq.index tl i == Seq.index s (i + 1))
    in
    Classical.forall_intro aux
  end else if first.low < new_bo then begin
    let trimmed = { low = new_bo; count = high first - new_bo } in
    let tl = Seq.tail s in
    assert (high trimmed == high first);
    assert (high trimmed <= bound);
    let aux (i:nat{i < Seq.length tl})
      : Lemma (high (Seq.index tl i) <= bound)
      = assert (Seq.index tl i == Seq.index s (i + 1))
    in
    Classical.forall_intro aux;
    assert (Seq.index result 0 == trimmed);
    let aux2 (i:nat{i < Seq.length result})
      : Lemma (high (Seq.index result i) <= bound)
      = if i = 0 then () else assert (Seq.index result i == Seq.index tl (i - 1))
    in
    Classical.forall_intro aux2
  end else ()

/// drain_repr decreases (or preserves) length
let drain_repr_length (s: Seq.seq interval) (new_bo: nat)
  : Lemma (Seq.length (drain_repr s new_bo) <= Seq.length s) = ()

/// drain_repr mem: positions >= new_bo are preserved
let drain_repr_mem_above (s: Seq.seq interval) (new_bo: nat) (x: nat)
  : Lemma (requires range_map_wf s /\ Seq.length s > 0 /\
                    (Seq.index s 0).low <= new_bo /\ new_bo <= high (Seq.index s 0) /\
                    x >= new_bo)
          (ensures mem (drain_repr s new_bo) x == mem s x) =
  let first = Seq.index s 0 in
  let result = drain_repr s new_bo in
  if high first <= new_bo then begin
    // first removed, x >= new_bo >= high first, so x not in first
    assert (not (in_interval first x));
    if mem s x then mem_tail s x else ()
  end else if first.low < new_bo then begin
    let trimmed = { low = new_bo; count = high first - new_bo } in
    let tl = Seq.tail s in
    mem_cons trimmed tl x
  end else ()
