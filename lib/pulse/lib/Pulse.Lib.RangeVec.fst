module Pulse.Lib.RangeVec

/// Range tracker backed by a sorted vector of non-overlapping intervals.
/// Drop-in replacement for RangeMap (AVL-based) with better cache locality
/// and clean KaRaMeL extraction (no .fsti -> no monomorphization bug).

#lang-pulse

open Pulse.Lib.Pervasives

module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = Pulse.Lib.RangeMap.Spec
module V = Pulse.Lib.Vector
module B = Pulse.Lib.Box
module G = FStar.Ghost
module R = Pulse.Lib.Reference

(*** Platform and bounds ***)

/// 64-bit platform assumption — standard for Pulse/SizeT code
assume val platform_is_64bit : squash SZ.fits_u64

/// Upper bound on range vector entries.
/// In practice, limited by CircularBuffer alloc_length (≤ pow2_63).
/// The bound ensures vector capacity doubling is always representable.
assume val max_range_vec_entries : n:pos{n <= pow2 62}

(*** Types ***)

noeq type range = { start: SZ.t; len: SZ.t }

noextract
let range_valid (r: range) : prop =
  SZ.v r.len > 0 /\
  SZ.fits (SZ.v r.start + SZ.v r.len)

noextract
let range_to_interval (r: range)
  : Pure Spec.interval (requires range_valid r) (ensures fun _ -> True) =
  { Spec.low = SZ.v r.start; Spec.count = SZ.v r.len }

let default_range : range = { start = 0sz; len = 1sz }

noextract
let rec seq_all_valid (s: Seq.seq range)
  : Tot prop (decreases Seq.length s) =
  if Seq.length s = 0 then True
  else range_valid (Seq.head s) /\ seq_all_valid (Seq.tail s)

noextract
let rec seq_all_valid_index (s: Seq.seq range) (i: nat)
  : Lemma (requires seq_all_valid s /\ i < Seq.length s)
          (ensures range_valid (Seq.index s i))
          (decreases Seq.length s) =
  if i = 0 then ()
  else seq_all_valid_index (Seq.tail s) (i - 1)

noextract
let rec seq_to_spec (s: Seq.seq range)
  : Pure (Seq.seq Spec.interval)
    (requires seq_all_valid s)
    (ensures fun r -> Seq.length r == Seq.length s)
    (decreases Seq.length s) =
  if Seq.length s = 0 then Seq.empty
  else Seq.cons (range_to_interval (Seq.head s)) (seq_to_spec (Seq.tail s))

#push-options "--fuel 2 --ifuel 1"

noextract
let rec seq_to_spec_index (s: Seq.seq range) (i: nat)
  : Lemma (requires seq_all_valid s /\ i < Seq.length s)
          (ensures range_valid (Seq.index s i) /\
                   Seq.index (seq_to_spec s) i == range_to_interval (Seq.index s i))
          (decreases Seq.length s) =
  seq_all_valid_index s i;
  if i = 0 then ()
  else seq_to_spec_index (Seq.tail s) (i - 1)

noextract
let rec seq_all_valid_forall (s: Seq.seq range)
  : Lemma (requires seq_all_valid s)
          (ensures forall (k:nat). k < Seq.length s ==> range_valid (Seq.index s k))
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else begin
    seq_all_valid_forall (Seq.tail s);
    let aux (k:nat{k < Seq.length s})
      : Lemma (range_valid (Seq.index s k)) =
      seq_all_valid_index s k
    in
    Classical.forall_intro aux
  end

#pop-options

#push-options "--fuel 3 --ifuel 2 --z3rlimit 20"

(* Helper lemma: seq_all_valid for snoc *)
noextract
let rec seq_all_valid_snoc (s: Seq.seq range) (r: range)
  : Lemma (requires seq_all_valid s /\ range_valid r)
          (ensures seq_all_valid (Seq.snoc s r))
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else begin
    seq_all_valid_snoc (Seq.tail s) r;
    // Help SMT understand the structure
    assert (Seq.length (Seq.snoc s r) > 0);
    assert (Seq.head (Seq.snoc s r) == Seq.head s);
    assert (Seq.tail (Seq.snoc s r) `Seq.equal` Seq.snoc (Seq.tail s) r)
  end

(* Lemma 1: seq_to_spec commutes with snoc *)
noextract
let rec seq_to_spec_snoc (s: Seq.seq range) (r: range)
  : Lemma (requires seq_all_valid s /\ range_valid r)
          (ensures seq_all_valid (Seq.snoc s r) /\
                   seq_to_spec (Seq.snoc s r) == Seq.snoc (seq_to_spec s) (range_to_interval r))
          (decreases Seq.length s) =
  seq_all_valid_snoc s r;
  if Seq.length s = 0 then begin
    Seq.lemma_eq_intro (Seq.snoc s r) (Seq.create 1 r);
    Seq.lemma_eq_intro (seq_to_spec (Seq.snoc s r)) (Seq.snoc (seq_to_spec s) (range_to_interval r))
  end else begin
    seq_to_spec_snoc (Seq.tail s) r;
    let s' = Seq.snoc s r in
    assert (Seq.head s' == Seq.head s);
    assert (Seq.tail s' `Seq.equal` Seq.snoc (Seq.tail s) r);
    let a = range_to_interval (Seq.head s) in
    let b = seq_to_spec (Seq.tail s) in
    let c = range_to_interval r in
    Seq.lemma_eq_intro (Seq.cons a (Seq.snoc b c)) (Seq.snoc (Seq.cons a b) c)
  end

(* Helper lemma: seq_all_valid for append *)
noextract
let rec seq_all_valid_append (s1 s2: Seq.seq range)
  : Lemma (requires seq_all_valid s1 /\ seq_all_valid s2)
          (ensures seq_all_valid (Seq.append s1 s2))
          (decreases Seq.length s1) =
  if Seq.length s1 = 0 then
    Seq.lemma_eq_intro (Seq.append s1 s2) s2
  else begin
    seq_all_valid_append (Seq.tail s1) s2;
    let s' = Seq.append s1 s2 in
    assert (Seq.length s' > 0);
    Seq.lemma_eq_intro (Seq.tail s') (Seq.append (Seq.tail s1) s2);
    assert (Seq.head s' == Seq.head s1)
  end

(* Lemma 2: seq_to_spec commutes with append *)
noextract
let rec seq_to_spec_append (s1 s2: Seq.seq range)
  : Lemma (requires seq_all_valid s1 /\ seq_all_valid s2)
          (ensures seq_all_valid (Seq.append s1 s2) /\
                   seq_to_spec (Seq.append s1 s2) == Seq.append (seq_to_spec s1) (seq_to_spec s2))
          (decreases Seq.length s1) =
  seq_all_valid_append s1 s2;
  if Seq.length s1 = 0 then begin
    Seq.lemma_eq_intro (Seq.append s1 s2) s2;
    Seq.lemma_eq_intro (seq_to_spec (Seq.append s1 s2)) (Seq.append (seq_to_spec s1) (seq_to_spec s2))
  end else begin
    seq_to_spec_append (Seq.tail s1) s2;
    let s' = Seq.append s1 s2 in
    assert (Seq.head s' == Seq.head s1);
    Seq.lemma_eq_intro (Seq.tail s') (Seq.append (Seq.tail s1) s2);
    // cons a (append b c) == append (cons a b) c
    let a = range_to_interval (Seq.head s1) in
    let b = seq_to_spec (Seq.tail s1) in
    let c = seq_to_spec s2 in
    Seq.lemma_eq_intro (Seq.cons a (Seq.append b c)) (Seq.append (Seq.cons a b) c)
  end

(* Lemma 3: seq_all_valid preserves through slice *)
noextract
let rec seq_all_valid_slice (s: Seq.seq range) (i j: nat)
  : Lemma (requires seq_all_valid s /\ i <= j /\ j <= Seq.length s)
          (ensures seq_all_valid (Seq.slice s i j))
          (decreases Seq.length s) =
  if i >= j then ()
  else if i = 0 then begin
    if j = 0 then ()
    else if j = Seq.length s then ()
    else seq_all_valid_slice (Seq.tail s) 0 (j - 1)
  end
  else seq_all_valid_slice (Seq.tail s) (i - 1) (j - 1)

(* Lemma 4: seq_to_spec commutes with slice *)
noextract
let seq_to_spec_slice (s: Seq.seq range) (i j: nat)
  : Lemma (requires seq_all_valid s /\ i <= j /\ j <= Seq.length s)
          (ensures seq_all_valid (Seq.slice s i j) /\
                   seq_to_spec (Seq.slice s i j) == Seq.slice (seq_to_spec s) i j) =
  seq_all_valid_slice s i j;
  let sliced_range = Seq.slice s i j in
  let sliced_spec = seq_to_spec sliced_range in
  let spec_sliced = Seq.slice (seq_to_spec s) i j in
  let aux (k: nat{k < Seq.length sliced_spec})
    : Lemma (Seq.index sliced_spec k == Seq.index spec_sliced k) =
    seq_to_spec_index sliced_range k;
    seq_all_valid_index s (i + k);
    seq_to_spec_index s (i + k)
  in
  Classical.forall_intro aux;
  Seq.lemma_eq_intro sliced_spec spec_sliced

#pop-options

(*** Predicate ***)

let range_vec_t = V.vector range

let is_range_vec (rv: range_vec_t) (repr: Seq.seq Spec.interval) : slprop =
  exists* (s: Seq.seq range) (cap: SZ.t).
    V.is_vector rv s cap **
    pure (seq_all_valid s /\
          seq_to_spec s == repr /\
          Spec.range_map_wf repr /\
          Seq.length s <= max_range_vec_entries /\
          (Seq.length s < SZ.v cap \/ SZ.fits (SZ.v cap + SZ.v cap)))

(*** Create / Free ***)

fn range_vec_create ()
  requires emp
  returns rv: range_vec_t
  ensures is_range_vec rv (Seq.empty #Spec.interval)
{
  let rv = V.create default_range 1sz;
  let _ = V.pop_back rv;
  with cap'. _;
  fold (is_range_vec rv (Seq.empty #Spec.interval));
  rv
}

fn range_vec_free (rv: range_vec_t) (#repr: erased (Seq.seq Spec.interval))
  requires is_range_vec rv repr
  ensures emp
{
  unfold is_range_vec;
  with s cap. _;
  V.free rv
}

(*** Queries ***)

fn range_vec_contiguous_from (rv: range_vec_t) (base: SZ.t) (#repr: erased (Seq.seq Spec.interval))
  requires is_range_vec rv repr
  returns n: SZ.t
  ensures is_range_vec rv repr ** pure (SZ.v n == Spec.contiguous_from repr (SZ.v base))
{
  unfold is_range_vec;
  with s cap. _;
  let sz = V.size rv;
  if (SZ.eq sz 0sz) {
    fold (is_range_vec rv repr);
    0sz
  } else {
    let first = V.at rv 0sz;
    seq_to_spec_index s 0;
    let r_high = SZ.add first.start first.len;
    if (SZ.lte first.start base && SZ.lt base r_high) {
      fold (is_range_vec rv repr);
      SZ.sub r_high base
    } else {
      fold (is_range_vec rv repr);
      0sz
    }
  }
}

fn range_vec_max_endpoint (rv: range_vec_t) (#repr: erased (Seq.seq Spec.interval))
  requires is_range_vec rv repr
  returns n: SZ.t
  ensures is_range_vec rv repr ** pure (SZ.v n == Spec.range_map_max_endpoint repr)
{
  unfold is_range_vec;
  with s cap. _;
  let sz = V.size rv;
  if (SZ.eq sz 0sz) {
    fold (is_range_vec rv repr);
    0sz
  } else {
    let last_idx = SZ.sub sz 1sz;
    let last = V.at rv last_idx;
    seq_to_spec_index s (SZ.v last_idx);
    let result = SZ.add last.start last.len;
    fold (is_range_vec rv repr);
    result
  }
}

(*** Add range — core operation ***)

noextract
let seq_insert (#a:Type) (s: Seq.seq a) (i: nat) (x: a) : Seq.seq a =
  if i <= Seq.length s then
    Seq.append (Seq.slice s 0 i) (Seq.cons x (Seq.slice s i (Seq.length s)))
  else s

noextract
let seq_remove (#a:Type) (s: Seq.seq a) (i: nat) (count: nat) : Seq.seq a =
  if i + count <= Seq.length s then
    Seq.append (Seq.slice s 0 i) (Seq.slice s (i + count) (Seq.length s))
  else s

(* Bridge: pointwise shift result matches seq_remove *)
noextract
let shift_to_seq_remove (#a:Type) (s s_cur: Seq.seq a) (i count: nat)
  : Lemma (requires i + count <= Seq.length s /\ count > 0 /\
                    Seq.length s_cur == Seq.length s /\
                    (forall (k:nat). k < i ==> Seq.index s_cur k == Seq.index s k) /\
                    (forall (k:nat). k >= i /\ k < Seq.length s - count ==>
                      Seq.index s_cur k == Seq.index s (k + count)) /\
                    (forall (k:nat). k >= Seq.length s - count /\ k < Seq.length s ==>
                      Seq.index s_cur k == Seq.index s k))
          (ensures Seq.slice s_cur 0 (Seq.length s - count) == seq_remove s i count) =
  let dst_end = Seq.length s - count in
  let candidate = Seq.slice s_cur 0 dst_end in
  let target = seq_remove s i count in
  Seq.lemma_eq_intro candidate target

(* Bridge: pointwise shift-right result matches seq_insert *)
noextract
let shift_to_seq_insert (#a:Type) (s s_cur: Seq.seq a) (i: nat) (r: a)
  : Lemma (requires i < Seq.length s /\
                    Seq.length s_cur == Seq.length s + 1 /\
                    (forall (m:nat). m < i ==> Seq.index s_cur m == Seq.index s m) /\
                    Seq.index s_cur i == r /\
                    (forall (m:nat). m > i /\ m < Seq.length s_cur ==>
                      Seq.index s_cur m == Seq.index s (m - 1)))
          (ensures s_cur == seq_insert s i r) =
  Seq.lemma_eq_intro s_cur (seq_insert s i r)

(* Bridge: shift-right + set produces seq_insert. Call BEFORE V.set. *)
noextract
let shift_set_is_seq_insert (#a:Type) (s s_shifted: Seq.seq a) (i: nat) (r: a)
  : Lemma (requires i < Seq.length s /\
                    Seq.length s_shifted == Seq.length s + 1 /\
                    (forall (m:nat). m < i ==> Seq.index s_shifted m == Seq.index s m) /\
                    (forall (m:nat). m > i /\ m < Seq.length s_shifted ==>
                      Seq.index s_shifted m == Seq.index s (m - 1)))
          (ensures Seq.upd s_shifted i r == seq_insert s i r) =
  Seq.lemma_eq_intro (Seq.upd s_shifted i r) (seq_insert s i r)

(* Bridge: snoc is seq_insert at end *)
noextract
let snoc_is_seq_insert (#a:Type) (s: Seq.seq a) (r: a) (i: nat)
  : Lemma (requires i >= Seq.length s /\ i <= Seq.length s)
          (ensures Seq.snoc s r == seq_insert s i r) =
  Seq.lemma_eq_intro (Seq.snoc s r) (seq_insert s i r)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"

(* seq_all_valid of seq_insert *)
noextract
let seq_all_valid_insert (s: Seq.seq range) (i: nat) (r: range)
  : Lemma (requires seq_all_valid s /\ range_valid r /\ i <= Seq.length s)
          (ensures seq_all_valid (seq_insert s i r)) =
  seq_all_valid_slice s 0 i;
  seq_all_valid_slice s i (Seq.length s);
  let suffix = Seq.slice s i (Seq.length s) in
  let cons_r = Seq.cons r suffix in
  Seq.lemma_eq_intro (Seq.tail cons_r) suffix;
  seq_all_valid_append (Seq.slice s 0 i) cons_r

(* seq_to_spec of seq_insert — relates to Seq operations on spec level *)
noextract
let seq_to_spec_insert (s: Seq.seq range) (i: nat) (r: range)
  : Lemma (requires seq_all_valid s /\ range_valid r /\ i <= Seq.length s)
          (ensures seq_all_valid (seq_insert s i r) /\
                   seq_to_spec (seq_insert s i r) ==
                   Seq.append (Seq.slice (seq_to_spec s) 0 i)
                              (Seq.cons (range_to_interval r)
                                        (Seq.slice (seq_to_spec s) i (Seq.length s)))) =
  seq_all_valid_insert s i r;
  seq_all_valid_slice s 0 i;
  seq_all_valid_slice s i (Seq.length s);
  seq_to_spec_slice s 0 i;
  seq_to_spec_slice s i (Seq.length s);
  let prefix = Seq.slice s 0 i in
  let suffix = Seq.slice s i (Seq.length s) in
  let cons_r = Seq.cons r suffix in
  Seq.lemma_eq_intro (Seq.tail cons_r) suffix;
  seq_to_spec_append prefix cons_r

(* Bridge: capacity condition after insert.
   From original |s|<cap ∨ fits(cap+cap) and cap'∈{cap,cap+cap},
   derive |s|+1<cap' ∨ fits(cap'+cap'). *)
noextract
let insert_capacity_condition (sz cap cap': nat)
  : Lemma (requires (sz < cap \/ SZ.fits (cap + cap)) /\
                    (cap' == cap \/ cap' == cap + cap) /\
                    sz <= cap /\
                    sz + 1 <= cap' /\
                    sz < max_range_vec_entries)
          (ensures sz + 1 < cap' \/ SZ.fits (cap' + cap')) =
  if cap' = cap + cap then begin
    // Resize: cap' = 2*cap.
    if cap >= 2 then
      // sz < cap → sz+1 <= cap < 2*cap = cap' ✓
      // sz == cap (via fits(cap+cap)) → sz+1 = cap+1 < 2*cap for cap≥2 ✓
      assert (sz + 1 < cap + cap)
    else
      SZ.fits_at_least_16 4 // cap == 1: SZ.fits(4) ✓
  end else begin
    // No resize: cap' == cap.
    if sz + 1 < cap then ()
    else begin
      // sz + 1 == cap. cap = sz + 1 <= max_range_vec_entries <= pow2 62.
      // cap + cap <= 2 * max_range_vec_entries <= 2 * pow2 62 = pow2 63 < pow2 64.
      // With fits_u64: SZ.fits(cap + cap).
      SZ.fits_u64_implies_fits (cap + cap)
    end
  end

(* Forall highs-below-offset lifts from ranges to spec *)
noextract
let forall_high_below_to_spec (s: Seq.seq range) (n: nat) (bound: nat)
  : Lemma (requires seq_all_valid s /\ n <= Seq.length s /\
                    (forall (k:nat). k < n ==> SZ.v (Seq.index s k).start + SZ.v (Seq.index s k).len < bound))
          (ensures (forall (k:nat). k < n ==> Spec.high (Seq.index (seq_to_spec s) k) < bound)) =
  let aux (k: nat{k < n})
    : Lemma (Spec.high (Seq.index (seq_to_spec s) k) < bound) =
    seq_to_spec_index s k;
    seq_all_valid_index s k
  in
  Classical.forall_intro aux

#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"

(* Overlap forall lifts from ranges to spec *)
noextract
let forall_overlap_to_spec (s: Seq.seq range) (iv j: nat) (mh: nat)
  : Lemma (requires seq_all_valid s /\ iv <= j /\ j <= Seq.length s /\
                    (forall (k:nat). k >= iv /\ k < j ==>
                      SZ.v (Seq.index s k).start <= mh))
          (ensures (forall (k:nat). k >= iv /\ k < j ==>
                     mh >= (Seq.index (seq_to_spec s) k).Spec.low)) =
  let aux (k: nat{k >= iv /\ k < j})
    : Lemma (mh >= (Seq.index (seq_to_spec s) k).Spec.low) =
    seq_to_spec_index s k;
    seq_all_valid_index s k
  in
  Classical.forall_intro aux

#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"

(* seq_all_valid of seq_remove *)
noextract
let seq_all_valid_remove (s: Seq.seq range) (i count: nat)
  : Lemma (requires seq_all_valid s /\ i + count <= Seq.length s)
          (ensures seq_all_valid (seq_remove s i count)) =
  seq_all_valid_slice s 0 i;
  seq_all_valid_slice s (i + count) (Seq.length s);
  seq_all_valid_append (Seq.slice s 0 i) (Seq.slice s (i + count) (Seq.length s))

(* seq_to_spec of seq_remove *)
noextract
let seq_to_spec_remove (s: Seq.seq range) (i count: nat)
  : Lemma (requires seq_all_valid s /\ i + count <= Seq.length s)
          (ensures seq_all_valid (seq_remove s i count) /\
                   seq_to_spec (seq_remove s i count) ==
                   Seq.append (Seq.slice (seq_to_spec s) 0 i)
                              (Seq.slice (seq_to_spec s) (i + count) (Seq.length s))) =
  seq_all_valid_remove s i count;
  seq_all_valid_slice s 0 i;
  seq_all_valid_slice s (i + count) (Seq.length s);
  seq_to_spec_slice s 0 i;
  seq_to_spec_slice s (i + count) (Seq.length s);
  seq_to_spec_append (Seq.slice s 0 i) (Seq.slice s (i + count) (Seq.length s))

(* Key bridge: Seq.upd at iv followed by seq_remove of [iv+1..j) gives merge result *)
noextract
let seq_upd_remove_spec (s: Seq.seq range) (iv j: nat) (r: range)
  : Lemma (requires seq_all_valid s /\ iv < Seq.length s /\ j > iv /\ j <= Seq.length s /\ range_valid r)
          (ensures (let result =
                      (if j > iv + 1
                       then seq_remove (Seq.upd s iv r) (iv + 1) (j - iv - 1)
                       else Seq.upd s iv r) in
                    seq_all_valid result /\
                    seq_to_spec result ==
                    Seq.append (Seq.slice (seq_to_spec s) 0 iv)
                               (Seq.append (Seq.create 1 (range_to_interval r))
                                           (Seq.slice (seq_to_spec s) j (Seq.length s))))) =
  let n = Seq.length s in
  let s' = Seq.upd s iv r in
  // upd preserves validity
  let upd_valid () : Lemma (seq_all_valid s') =
    let prefix = Seq.slice s 0 iv in
    let suffix = Seq.slice s (iv + 1) n in
    seq_all_valid_slice s 0 iv;
    seq_all_valid_slice s (iv + 1) n;
    Seq.lemma_eq_intro s' (Seq.append prefix (Seq.append (Seq.create 1 r) suffix));
    Seq.lemma_eq_intro (Seq.tail (Seq.cons r suffix)) suffix;
    seq_all_valid_append (Seq.create 1 r) suffix;
    Seq.lemma_eq_intro (Seq.append (Seq.create 1 r) suffix) (Seq.cons r suffix);
    seq_all_valid_append prefix (Seq.cons r suffix)
  in
  upd_valid ();
  if j > iv + 1 then begin
    let count = j - iv - 1 in
    // seq_remove s' (iv+1) count == append (slice s' 0 (iv+1)) (slice s' j n)
    // slice s' 0 (iv+1) == append (slice s 0 iv) (create 1 r)
    Seq.lemma_eq_intro (Seq.slice s' 0 (iv + 1))
      (Seq.append (Seq.slice s 0 iv) (Seq.create 1 r));
    // slice s' j n == slice s j n
    Seq.lemma_eq_intro (Seq.slice s' j n) (Seq.slice s j n);
    // So: seq_remove s' (iv+1) count == append (slice s 0 iv) (append (create 1 r) (slice s j n))
    let result = seq_remove s' (iv + 1) count in
    Seq.lemma_eq_intro result
      (Seq.append (Seq.slice s 0 iv)
                  (Seq.append (Seq.create 1 r) (Seq.slice s j n)));
    // validity of result
    seq_all_valid_slice s 0 iv;
    seq_all_valid_slice s j n;
    Seq.lemma_eq_intro (Seq.tail (Seq.cons r (Seq.slice s j n))) (Seq.slice s j n);
    seq_all_valid_append (Seq.create 1 r) (Seq.slice s j n);
    Seq.lemma_eq_intro (Seq.append (Seq.create 1 r) (Seq.slice s j n)) (Seq.cons r (Seq.slice s j n));
    seq_all_valid_append (Seq.slice s 0 iv) (Seq.cons r (Seq.slice s j n));
    // seq_to_spec of result
    seq_to_spec_slice s 0 iv;
    seq_to_spec_slice s j n;
    seq_to_spec_append (Seq.create 1 r) (Seq.slice s j n);
    seq_to_spec_append (Seq.slice s 0 iv) (Seq.cons r (Seq.slice s j n))
  end else begin
    // j == iv + 1, no removal needed
    Seq.lemma_eq_intro s' (Seq.append (Seq.slice s 0 iv) (Seq.append (Seq.create 1 r) (Seq.slice s j n)));
    seq_all_valid_slice s 0 iv;
    seq_all_valid_slice s j n;
    Seq.lemma_eq_intro (Seq.tail (Seq.cons r (Seq.slice s j n))) (Seq.slice s j n);
    seq_all_valid_append (Seq.create 1 r) (Seq.slice s j n);
    Seq.lemma_eq_intro (Seq.append (Seq.create 1 r) (Seq.slice s j n)) (Seq.cons r (Seq.slice s j n));
    seq_all_valid_append (Seq.slice s 0 iv) (Seq.cons r (Seq.slice s j n));
    seq_to_spec_slice s 0 iv;
    seq_to_spec_slice s j n;
    seq_to_spec_append (Seq.create 1 r) (Seq.slice s j n);
    seq_to_spec_append (Seq.slice s 0 iv) (Seq.cons r (Seq.slice s j n))
  end

(* Bridge: lift exit condition from range-level to spec-level with mh0 *)
noextract
let exit_condition_to_spec (s: Seq.seq range) (repr: Seq.seq Spec.interval) (jv: nat)
    (mh0_val final_high_val: nat)
  : Lemma (requires seq_all_valid s /\ repr == seq_to_spec s /\ jv <= Seq.length s /\
                    final_high_val >= mh0_val /\
                    (jv == Seq.length s \/ final_high_val < SZ.v (Seq.index s jv).start))
          (ensures jv == Seq.length repr \/ mh0_val < (Seq.index repr jv).Spec.low)
  = if jv < Seq.length s then seq_to_spec_index s jv
    else ()

(* Bridge lemma for merge loop body: packages merge_absorbed_high step + mh0 coverage *)
noextract
let merge_loop_body_step (s: Seq.seq range) (iv jv: nat) (mh_val mh0_val: nat)
  : Lemma (requires
      iv + 1 <= Seq.length s /\ jv > iv /\ jv < Seq.length s /\
      seq_all_valid s /\
      range_valid (Seq.index s jv) /\
      mh_val >= SZ.v (Seq.index s jv).start /\
      (let suffix_tail = Seq.slice (seq_to_spec s) (iv + 1) (Seq.length s) in
       let k = jv - iv - 1 in
       k < Seq.length suffix_tail /\
       mh_val == Spec.merge_absorbed_high suffix_tail mh0_val k /\
       Spec.range_map_wf suffix_tail))
    (ensures
      (let suffix_tail = Seq.slice (seq_to_spec s) (iv + 1) (Seq.length s) in
       let r_high_val = SZ.v (Seq.index s jv).start + SZ.v (Seq.index s jv).len in
       let new_mh = (if r_high_val > mh_val then r_high_val else mh_val) in
       // 1. merge_absorbed_high step
       new_mh == Spec.merge_absorbed_high suffix_tail mh0_val (jv - iv) /\
       // 2. mh0 covers all absorbed
       mh0_val >= SZ.v (Seq.index s jv).start))
  = let k = jv - iv - 1 in
    let suffix_tail = Seq.slice (seq_to_spec s) (iv + 1) (Seq.length s) in
    // Connect suffix_tail indexing to original seq
    seq_to_spec_index s jv;
    seq_all_valid_index s jv;
    assert (Seq.index suffix_tail k == range_to_interval (Seq.index s jv));
    // merge_absorbed_high unfold
    Spec.merge_absorbed_high_unfold_right suffix_tail mh0_val k;
    // mh0 covers absorbed
    if k > 0 then
      Spec.mh0_covers_absorbed suffix_tail mh0_val k
    else ()

#pop-options

#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"

/// Helper: shift elements [i..n) right by 1, set position i to r.
fn vec_insert_at (rv: range_vec_t) (i: SZ.t) (r: range)
  (#s: erased (Seq.seq range)) (#cap: erased SZ.t)
  requires V.is_vector rv s cap **
           pure (SZ.v i <= Seq.length s /\
                 Seq.length s < max_range_vec_entries /\
                 (Seq.length s < SZ.v cap \/ SZ.fits (SZ.v cap + SZ.v cap)))
  ensures exists* (s': Seq.seq range) (cap': SZ.t).
    V.is_vector rv s' cap' **
    pure (Seq.length s' == Seq.length s + 1 /\ s' == seq_insert s (SZ.v i) r /\
          (Seq.length s + 1 < SZ.v cap' \/ SZ.fits (SZ.v cap' + SZ.v cap')))
{
  V.size_bounded rv;
  V.push_back rv r;
  with cap1. _;
  insert_capacity_condition (Seq.length (G.reveal s)) (SZ.v (G.reveal cap)) (SZ.v cap1);
  let sz = V.size rv;
  if (SZ.gt sz 1sz && SZ.lt i (SZ.sub sz 1sz)) {
    let mut j = SZ.sub sz 1sz;
    let mut cont = true;
    while (!cont)
    invariant exists* jv cv s_cur cap_cur.
      R.pts_to j jv ** R.pts_to cont cv **
      V.is_vector rv s_cur cap_cur **
      pure (SZ.v jv >= SZ.v i /\ SZ.v jv < Seq.length s_cur /\
            Seq.length s_cur == Seq.length (G.reveal s) + 1 /\
            cap_cur == cap1 /\
            // Prefix unchanged
            (forall (m:nat). m < SZ.v jv ==>
              Seq.index s_cur m == Seq.index (G.reveal s) m) /\
            // Shifted region
            (forall (m:nat). m > SZ.v jv /\ m < Seq.length s_cur ==>
              Seq.index s_cur m == Seq.index (G.reveal s) (m - 1)) /\
            // Exit
            (not cv ==> SZ.v jv == SZ.v i))
    {
      let jv = !j;
      if (SZ.gt jv i) {
        let prev = V.at rv (SZ.sub jv 1sz);
        V.set rv jv prev;
        let new_j = SZ.sub jv 1sz;
        j := new_j;
        if (SZ.eq new_j i) { cont := false }
      } else {
        cont := false
      }
    };
    // Bind loop existentials; call bridge lemma BEFORE V.set
    with _jv2 _cv2 s_after_shift _cap_shift. _;
    shift_set_is_seq_insert (G.reveal s) s_after_shift (SZ.v i) r;
    V.set rv i r
  } else {
    // else: sz <= 1 or i >= sz - 1, so i >= |s|
    assert (pure (SZ.v i >= Seq.length (G.reveal s)));
    assert (pure (SZ.v i <= Seq.length (G.reveal s)));
    snoc_is_seq_insert (G.reveal s) r (SZ.v i);
    assert (pure (Seq.snoc (G.reveal s) r == seq_insert (G.reveal s) (SZ.v i) r))
  }
}

#pop-options

/// Helper: remove count elements starting at position i
fn vec_remove_range (rv: range_vec_t) (i: SZ.t) (count: SZ.t)
  (#s: erased (Seq.seq range)) (#cap: erased SZ.t)
  requires V.is_vector rv s cap **
           pure (SZ.v i + SZ.v count <= Seq.length s /\ SZ.v count > 0)
  ensures exists* (s': Seq.seq range) (cap': SZ.t).
    V.is_vector rv s' cap' **
    pure (s' == seq_remove s (SZ.v i) (SZ.v count) /\
          Seq.length s' + SZ.v count == Seq.length s /\
          (Seq.length s' < SZ.v cap' \/ SZ.fits (SZ.v cap' + SZ.v cap')))
{
  let sz = V.size rv;
  let dst_end = SZ.sub sz count;
  // Phase 1: shift elements left — copy s[j+count] to s[j] for j in [i..dst_end)
  let mut j = i;
  let mut shift_cont = true;
  while (!shift_cont)
  invariant exists* jv sc s_cur cap_cur.
    R.pts_to j jv ** R.pts_to shift_cont sc **
    V.is_vector rv s_cur cap_cur **
    pure (SZ.v jv >= SZ.v i /\ SZ.v jv <= SZ.v dst_end /\
          Seq.length s_cur == Seq.length s /\
          cap_cur == G.reveal cap /\
          // Prefix unchanged
          (forall (k:nat). k < SZ.v i ==> Seq.index s_cur k == Seq.index (G.reveal s) k) /\
          // Shifted region
          (forall (k:nat). k >= SZ.v i /\ k < SZ.v jv ==>
            Seq.index s_cur k == Seq.index (G.reveal s) (k + SZ.v count)) /\
          // Suffix unchanged
          (forall (k:nat). k >= SZ.v jv /\ k < Seq.length s_cur ==>
            Seq.index s_cur k == Seq.index (G.reveal s) k) /\
          // Exit
          (not sc ==> SZ.v jv == SZ.v dst_end))
  {
    let jv = !j;
    if (SZ.lt jv dst_end) {
      let val_ = V.at rv (SZ.add jv count);
      V.set rv jv val_;
      j := SZ.add jv 1sz
    } else {
      shift_cont := false
    }
  };
  // After shift: first dst_end elements form seq_remove
  with _jv1 _sc1 s_shifted _cap_shifted. _;
  shift_to_seq_remove (G.reveal s) s_shifted (SZ.v i) (SZ.v count);
  // Phase 2: pop count elements from the end
  let target = G.hide (seq_remove (G.reveal s) (SZ.v i) (SZ.v count));
  let mut k = 0sz;
  let mut pop_cont = true;
  while (!pop_cont)
  invariant exists* kv pc s_cur cap_cur.
    R.pts_to k kv ** R.pts_to pop_cont pc **
    V.is_vector rv s_cur cap_cur **
    pure (SZ.v kv <= SZ.v count /\
          Seq.length s_cur + SZ.v kv == Seq.length (G.reveal s) /\
          // Content: first dst_end elements as a slice match seq_remove
          Seq.slice s_cur 0 (SZ.v dst_end) == G.reveal target /\
          // Capacity: established after first pop (kv > 0)
          (SZ.v kv > 0 ==>
            (Seq.length s_cur < SZ.v cap_cur \/ SZ.fits (SZ.v cap_cur + SZ.v cap_cur))) /\
          (not pc ==> SZ.v kv >= SZ.v count))
  {
    let kv = !k;
    if (SZ.lt kv count) {
      let _ = V.pop_back rv;
      let new_k = SZ.add kv 1sz;
      k := new_k;
      if (SZ.eq new_k count) {
        pop_cont := false
      }
    } else {
      pop_cont := false
    }
  };
  // After pop: s_cur has dst_end elements, slice 0..dst_end == s_cur == target
  with _kv1 _pc1 s_final _cap_final. _;
  Seq.lemma_eq_intro s_final (G.reveal target)
}

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"

fn range_vec_add (rv: range_vec_t) (offset: SZ.t) (len: SZ.t{SZ.v len > 0})
  (#repr: erased (Seq.seq Spec.interval))
  requires is_range_vec rv repr **
           pure (SZ.fits (SZ.v offset + SZ.v len) /\
                 Seq.length repr < max_range_vec_entries)
  ensures is_range_vec rv (Spec.add_range repr (SZ.v offset) (SZ.v len))
{
  unfold is_range_vec;
  with s cap. _;
  let sz = V.size rv;
  let off_plus_len = SZ.add offset len;

  // Phase 1: find insertion point (first i where high(rv[i]) >= offset)
  seq_all_valid_forall s;
  let mut idx = 0sz;
  let mut search = true;
  while (!search)
  invariant exists* iv sv s_cur cap_cur.
    R.pts_to idx iv ** R.pts_to search sv **
    V.is_vector rv s_cur cap_cur **
    pure (seq_all_valid s_cur /\
          s_cur == G.reveal s /\ cap_cur == G.reveal cap /\
          SZ.v iv <= Seq.length s_cur /\
          (forall (k:nat). k < Seq.length s_cur ==> range_valid (Seq.index s_cur k)) /\
          (forall (k:nat). k < SZ.v iv ==>
            SZ.v (Seq.index s_cur k).start + SZ.v (Seq.index s_cur k).len < SZ.v offset) /\
          // Exit: when done, either iv==sz or high(s[iv]) >= offset
          (not sv ==> (SZ.v iv == Seq.length s_cur \/
                       SZ.v (Seq.index s_cur (SZ.v iv)).start + SZ.v (Seq.index s_cur (SZ.v iv)).len >= SZ.v offset)))
  {
    let iv = !idx;
    if (SZ.lt iv sz) {
      let r = V.at rv iv;
      let high = SZ.add r.start r.len;
      if (SZ.lt high offset) {
        idx := SZ.add iv 1sz
      } else {
        search := false
      }
    } else {
      search := false
    }
  };

  let iv = !idx;

  if (SZ.eq sz 0sz || SZ.eq iv sz) {
    // Append at end (empty vec or all ranges are before offset)
    let r : range = { start = offset; len = len };
    // Prove spec facts while s is still live
    forall_high_below_to_spec s (SZ.v iv) (SZ.v offset);
    Spec.add_range_all_before repr (SZ.v offset) (SZ.v len);
    seq_to_spec_snoc s r;
    seq_all_valid_insert s (SZ.v iv) r;
    Spec.add_range_wf repr (SZ.v offset) (SZ.v len);
    vec_insert_at rv iv r;
    with s' cap'. _;
    snoc_is_seq_insert (G.reveal s) r (SZ.v iv);
    fold (is_range_vec rv (Spec.add_range repr (SZ.v offset) (SZ.v len)))
  } else {
    let first_r = V.at rv iv;
    if (SZ.lt off_plus_len first_r.start) {
      // No overlap — insert before iv
      let new_r : range = { start = offset; len = len };
      // Prove spec facts while s is still live
      forall_high_below_to_spec s (SZ.v iv) (SZ.v offset);
      seq_to_spec_index s (SZ.v iv);
      seq_all_valid_index s (SZ.v iv);
      Spec.add_range_insert_no_overlap repr (SZ.v offset) (SZ.v len) (SZ.v iv);
      seq_to_spec_insert s (SZ.v iv) new_r;
      seq_all_valid_insert s (SZ.v iv) new_r;
      Spec.add_range_wf repr (SZ.v offset) (SZ.v len);
      vec_insert_at rv iv new_r;
      with s' cap'. _;
      fold (is_range_vec rv (Spec.add_range repr (SZ.v offset) (SZ.v len)))
    } else {
      // Merge: compute merged bounds [merged_low, merged_high)
      let merged_low = (if SZ.lt offset first_r.start then offset else first_r.start);
      let first_high = SZ.add first_r.start first_r.len;
      let mh0_val = (if SZ.gt off_plus_len first_high then off_plus_len else first_high);
      let mut merged_high = mh0_val;

      // Ghost: capture initial mh0 and suffix_tail for merge_absorbed_high tracking
      let mh0 = G.hide (SZ.v mh0_val);
      let repr_snap = G.hide repr;

      // Extend merge rightward through overlapping/adjacent ranges
      let mut j = SZ.add iv 1sz;
      let mut merge_cont = true;
      while (!merge_cont)
      invariant exists* jv mh mc s_cur cap_cur.
        R.pts_to j jv ** R.pts_to merged_high mh ** R.pts_to merge_cont mc **
        V.is_vector rv s_cur cap_cur **
        pure (seq_all_valid s_cur /\
              s_cur == G.reveal s /\ cap_cur == G.reveal cap /\
              SZ.v jv > SZ.v iv /\ SZ.v jv <= Seq.length s_cur /\
              SZ.v mh > SZ.v merged_low /\
              SZ.fits (SZ.v mh) /\
              (forall (k:nat). k < Seq.length s_cur ==> range_valid (Seq.index s_cur k)) /\
              // Overlap: mh covers all ranges in [iv..jv)
              (forall (k:nat). k >= SZ.v iv /\ k < SZ.v jv ==>
                SZ.v mh >= SZ.v (Seq.index s_cur k).start) /\
              // mh0 covers ranges in (iv..jv) — for merge_full precondition
              (forall (k:nat). k > SZ.v iv /\ k < SZ.v jv ==>
                G.reveal mh0 >= SZ.v (Seq.index s_cur k).start) /\
              // Exit: when loop done, either jv==sz or mh < s[jv].start
              (not mc ==> (SZ.v jv == Seq.length s_cur \/
                           SZ.v mh < SZ.v (Seq.index s_cur (SZ.v jv)).start)) /\
              // Track: mh == merge_absorbed_high(suffix_tail, mh0, jv-iv-1)
              (let suffix_tail = Seq.slice (seq_to_spec s_cur) (SZ.v iv + 1) (Seq.length s_cur) in
               SZ.v mh == Spec.merge_absorbed_high suffix_tail (G.reveal mh0) (SZ.v jv - SZ.v iv - 1)))
      {
        let jv = !j;
        if (SZ.lt jv sz) {
          let r = V.at rv jv;
          let mh = !merged_high;
          if (SZ.gte mh r.start) {
            let r_high = SZ.add r.start r.len;
            // Use bridge lemma for loop invariant step
            Spec.range_map_wf_slice repr (SZ.v iv + 1);
            merge_loop_body_step s (SZ.v iv) (SZ.v jv) (SZ.v mh) (G.reveal mh0);
            if (SZ.gt r_high mh) { merged_high := r_high };
            j := SZ.add jv 1sz
          } else {
            merge_cont := false
          }
        } else {
          merge_cont := false
        }
      };

      // Write merged range at iv, remove subsumed ranges [iv+1..j)
      let jv = !j;
      let final_high = !merged_high;
      // Bounds are valid: final_high > merged_low from loop invariant
      let final_len = SZ.sub final_high merged_low;

      // Lift range-level facts to spec level BEFORE consuming s via V.set
      forall_high_below_to_spec s (SZ.v iv) (SZ.v offset);
      seq_to_spec_index s (SZ.v iv);
      seq_all_valid_index s (SZ.v iv);
      forall_overlap_to_spec s (SZ.v iv) (SZ.v jv) (SZ.v final_high);
      // Lift mh0 forall to spec level
      forall_overlap_to_spec s (SZ.v iv + 1) (SZ.v jv) (G.reveal mh0);
      // Connect our ghost mh0 to spec's computed mh0
      assert (pure (Spec.high (Seq.index repr (SZ.v iv)) == SZ.v first_high));
      assert (pure (G.reveal mh0 ==
        (if SZ.v offset + SZ.v len > Spec.high (Seq.index repr (SZ.v iv))
         then SZ.v offset + SZ.v len
         else Spec.high (Seq.index repr (SZ.v iv)))));
      // Exit condition: mh0 < repr[j].low (from final_high >= mh0 and final_high < s[j].start)
      Spec.merge_absorbed_high_mono
        (Seq.slice repr (SZ.v iv + 1) (Seq.length repr))
        (G.reveal mh0)
        (SZ.v jv - SZ.v iv - 1);
      exit_condition_to_spec s repr (SZ.v jv) (G.reveal mh0) (SZ.v final_high);

      // Call merge_full with explicit mh0 parameter
      Spec.add_range_merge_full_explicit repr (SZ.v offset) (SZ.v len) (SZ.v iv) (SZ.v jv) (G.reveal mh0);

      // Now do the imperative set
      let merged_r : range = { start = merged_low; len = final_len };
      V.set rv iv merged_r;

      // Handle remove case
      if (SZ.gt jv (SZ.add iv 1sz)) {
        let remove_count = SZ.sub jv (SZ.add iv 1sz);
        vec_remove_range rv (SZ.add iv 1sz) remove_count;
        with s_final cap_final. _;
        seq_upd_remove_spec s (SZ.v iv) (SZ.v jv) merged_r;
        Spec.add_range_wf repr (SZ.v offset) (SZ.v len);
        assert (pure (range_to_interval merged_r == Spec.({ low = SZ.v merged_low; count = SZ.v final_len })));
        fold (is_range_vec rv (Spec.add_range repr (SZ.v offset) (SZ.v len)))
      } else {
        // jv == iv + 1, no removal needed. V.set gives concrete V.is_vector rv (Seq.upd s iv merged_r) cap
        seq_upd_remove_spec s (SZ.v iv) (SZ.v jv) merged_r;
        Spec.add_range_wf repr (SZ.v offset) (SZ.v len);
        // range_to_interval merged_r matches the spec's merged interval
        assert (pure (range_to_interval merged_r == Spec.({ low = SZ.v merged_low; count = SZ.v final_len })));
        fold (is_range_vec rv (Spec.add_range repr (SZ.v offset) (SZ.v len)))
      }
    }
  }
}

#pop-options
