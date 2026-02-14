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
