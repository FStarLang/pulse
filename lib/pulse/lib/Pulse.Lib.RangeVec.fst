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

(*** Predicate ***)

let range_vec_t = V.vector range

let is_range_vec (rv: range_vec_t) (repr: Seq.seq Spec.interval) : slprop =
  exists* (s: Seq.seq range) (cap: SZ.t).
    V.is_vector rv s cap **
    pure (seq_all_valid s /\
          seq_to_spec s == repr /\
          Spec.range_map_wf repr)

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

/// Helper: shift elements [i..n) right by 1, set position i to r
fn vec_insert_at (rv: range_vec_t) (i: SZ.t) (r: range)
  (#s: erased (Seq.seq range)) (#cap: erased SZ.t)
  requires V.is_vector rv s cap **
           pure (SZ.v i <= Seq.length s /\
                 (Seq.length s < SZ.v cap \/ SZ.fits (SZ.v cap + SZ.v cap)))
  ensures exists* (s': Seq.seq range) (cap': SZ.t).
    V.is_vector rv s' cap' **
    pure (Seq.length s' == Seq.length s + 1)
{
  V.push_back rv r;
  with cap1. _;
  let sz = V.size rv;
  if (SZ.gt sz 1sz && SZ.lt i (SZ.sub sz 1sz)) {
    let mut j = SZ.sub sz 1sz;
    let mut cont = true;
    while (!cont)
    invariant exists* jv cv s_cur cap_cur.
      R.pts_to j jv ** R.pts_to cont cv **
      V.is_vector rv s_cur cap_cur **
      pure (SZ.v jv >= SZ.v i /\ SZ.v jv < Seq.length s_cur /\
            Seq.length s_cur == Seq.length s + 1)
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
    V.set rv i r
  } else {
    ()
  }
}

/// Helper: remove count elements starting at position i
fn vec_remove_range (rv: range_vec_t) (i: SZ.t) (count: SZ.t)
  (#s: erased (Seq.seq range)) (#cap: erased SZ.t)
  requires V.is_vector rv s cap **
           pure (SZ.v i + SZ.v count <= Seq.length s /\ SZ.v count > 0)
  ensures exists* (s': Seq.seq range) (cap': SZ.t).
    V.is_vector rv s' cap' **
    pure (Seq.length s' + SZ.v count == Seq.length s)
{
  let sz = V.size rv;
  let dst_end = SZ.sub sz count;
  // Phase 1: shift elements left — for j from i to dst_end-1, set rv[j] = rv[j+count]
  let mut j = i;
  let mut shift_cont = true;
  while (!shift_cont)
  invariant exists* jv sc s_cur cap_cur.
    R.pts_to j jv ** R.pts_to shift_cont sc **
    V.is_vector rv s_cur cap_cur **
    pure (SZ.v jv >= SZ.v i /\ SZ.v jv <= SZ.v dst_end /\
          Seq.length s_cur == Seq.length s)
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
  // Phase 2: pop count elements from the end
  let mut k = 0sz;
  let mut pop_cont = true;
  while (!pop_cont)
  invariant exists* kv pc s_cur cap_cur.
    R.pts_to k kv ** R.pts_to pop_cont pc **
    V.is_vector rv s_cur cap_cur **
    pure (SZ.v kv <= SZ.v count /\
          Seq.length s_cur + SZ.v kv == Seq.length s /\
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
  }
}

#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"

fn range_vec_add (rv: range_vec_t) (offset: SZ.t) (len: SZ.t{SZ.v len > 0})
  (#repr: erased (Seq.seq Spec.interval))
  requires is_range_vec rv repr ** pure (SZ.fits (SZ.v offset + SZ.v len))
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
          (forall (k:nat). k < Seq.length s_cur ==> range_valid (Seq.index s_cur k)))
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
    admit (); // TODO: prove against Spec.add_range
    let r : range = { start = offset; len = len };
    vec_insert_at rv iv r;
    with s' cap'. _;
    Spec.add_range_wf repr (SZ.v offset) (SZ.v len);
    admit (); // TODO: seq_to_spec bridge
    fold (is_range_vec rv (Spec.add_range repr (SZ.v offset) (SZ.v len)))
  } else {
    let first_r = V.at rv iv;
    if (SZ.lt off_plus_len first_r.start) {
      // No overlap — insert before iv
      admit ();
      vec_insert_at rv iv ({ start = offset; len = len });
      with s' cap'. _;
      Spec.add_range_wf repr (SZ.v offset) (SZ.v len);
      admit ();
      fold (is_range_vec rv (Spec.add_range repr (SZ.v offset) (SZ.v len)))
    } else {
      // Merge: compute merged bounds [merged_low, merged_high)
      let merged_low = (if SZ.lt offset first_r.start then offset else first_r.start);
      let first_high = SZ.add first_r.start first_r.len;
      let mut merged_high = (if SZ.gt off_plus_len first_high then off_plus_len else first_high);

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
              SZ.v mh >= SZ.v merged_low /\
              SZ.fits (SZ.v mh) /\
              (forall (k:nat). k < Seq.length s_cur ==> range_valid (Seq.index s_cur k)))
      {
        let jv = !j;
        if (SZ.lt jv sz) {
          let r = V.at rv jv;
          let mh = !merged_high;
          if (SZ.gte mh r.start) {
            let r_high = SZ.add r.start r.len;
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
      admit (); // TODO: prove merged bounds are valid
      let final_len = SZ.sub final_high merged_low;
      V.set rv iv ({ start = merged_low; len = final_len });

      let num_remove = SZ.sub (SZ.sub jv iv) 1sz;
      if (SZ.gt num_remove 0sz) {
        vec_remove_range rv (SZ.add iv 1sz) num_remove
      };

      Spec.add_range_wf repr (SZ.v offset) (SZ.v len);
      admit (); // TODO: seq_to_spec bridge
      with s_final cap_final. _;
      fold (is_range_vec rv (Spec.add_range repr (SZ.v offset) (SZ.v len)))
    }
  }
}

#pop-options
