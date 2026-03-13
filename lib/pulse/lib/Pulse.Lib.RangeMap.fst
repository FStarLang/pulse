module Pulse.Lib.RangeMap

/// Range map backed by an AVL tree mapping Range intervals to unit (pure interval tracker).

#lang-pulse

open Pulse.Lib.Pervasives

module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = Pulse.Lib.RangeMap.Spec
module B = Pulse.Lib.Box
module T = Pulse.Lib.Spec.AVLTree
module AVL = Pulse.Lib.AVLTree
module G = FStar.Ghost
module R = Pulse.Lib.Reference
/// Concrete range type: [start, start+len)
type range = { start: SZ.t; len: SZ.t }

/// An entry is a range paired with unit (no byte data)
let entry = range & unit

(*** B1: Range comparison ***)

let range_cmp_fn (a b: range) : int =
  let av = SZ.v a.start in
  let bv = SZ.v b.start in
  if av < bv then (-1)
  else if av = bv then 0
  else 1

let range_cmp : T.cmp range = range_cmp_fn

(*** Helpers ***)

let range_valid (r: range) : prop =
  SZ.v r.len > 0 /\
  SZ.fits (SZ.v r.start + SZ.v r.len)

let entry_valid (e: entry) : prop =
  range_valid (fst e)

let rec list_valid (l: list entry) : Tot prop (decreases l) =
  match l with
  | [] -> True
  | hd :: tl -> entry_valid hd /\ list_valid tl

let range_to_interval (r: range)
  : Pure Spec.interval (requires range_valid r) (ensures fun _ -> True) =
  { Spec.low = SZ.v r.start; Spec.count = SZ.v r.len }

let mk_entry (s l: SZ.t) : entry = ({ start = s; len = l }, ())

let rec list_to_spec (l: list entry)
  : Pure (Seq.seq Spec.interval)
    (requires list_valid l)
    (ensures fun r -> True)
    (decreases l) =
  match l with
  | [] -> Seq.empty
  | hd :: tl -> Seq.cons (range_to_interval (fst hd)) (list_to_spec tl)

let rec seq_all_valid (s: Seq.seq entry)
  : Tot prop (decreases Seq.length s) =
  if Seq.length s = 0 then True
  else entry_valid (Seq.head s) /\ seq_all_valid (Seq.tail s)

let rec seq_to_spec (s: Seq.seq entry)
  : Pure (Seq.seq Spec.interval)
    (requires seq_all_valid s)
    (ensures fun r -> Seq.length r == Seq.length s)
    (decreases Seq.length s) =
  if Seq.length s = 0 then Seq.empty
  else Seq.cons (range_to_interval (fst (Seq.head s))) (seq_to_spec (Seq.tail s))

let seq_to_spec_head (s: Seq.seq entry)
  : Lemma (requires seq_all_valid s /\ Seq.length s > 0)
          (ensures Seq.head (seq_to_spec s) == range_to_interval (fst (Seq.head s))) = ()

let tree_wf (t: T.tree range unit) : prop =
  seq_all_valid (T.inorder t)

let tree_to_spec (t: T.tree range unit)
  : Pure (Seq.seq Spec.interval)
    (requires tree_wf t)
    (ensures fun r -> Seq.length r == Seq.length (T.inorder t)) =
  seq_to_spec (T.inorder t)

(*** seq ↔ list conversion ***)

let rec seq_to_list (s: Seq.seq entry)
  : Tot (list entry) (decreases Seq.length s) =
  if Seq.length s = 0 then []
  else Seq.head s :: seq_to_list (Seq.tail s)

let rec seq_to_list_valid (s: Seq.seq entry)
  : Lemma (requires seq_all_valid s)
          (ensures list_valid (seq_to_list s))
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else seq_to_list_valid (Seq.tail s)

let rec seq_to_list_spec (s: Seq.seq entry)
  : Lemma (requires seq_all_valid s)
          (ensures (seq_to_list_valid s; list_to_spec (seq_to_list s) == seq_to_spec s))
          (decreases Seq.length s) =
  if Seq.length s = 0 then (
    seq_to_list_valid s;
    assert (Seq.equal (list_to_spec (seq_to_list s)) (seq_to_spec s))
  ) else (
    seq_to_list_valid (Seq.tail s);
    seq_to_list_spec (Seq.tail s);
    seq_to_list_valid s
  )

(*** tree_min ↔ inorder head ***)

#push-options "--fuel 3 --z3rlimit 40"

let rec tree_min_head_inorder (t: T.tree range unit{T.Node? t})
  : Lemma (ensures Seq.length (T.inorder t) > 0 /\
                   T.tree_min t == Seq.head (T.inorder t))
          (decreases t) =
  match t with
  | T.Node dk dv T.Leaf r ->
    Seq.append_empty_l (Seq.cons (dk, dv) (T.inorder r));
    assert (Seq.equal (T.inorder t) (Seq.cons (dk, dv) (T.inorder r)))
  | T.Node dk dv l r ->
    tree_min_head_inorder l;
    Seq.lemma_head_append (T.inorder l) (Seq.cons (dk, dv) (T.inorder r))

#pop-options

(*** seq_to_spec indexing ***)

#push-options "--fuel 2 --ifuel 1"

let rec seq_all_valid_index (s: Seq.seq entry) (i: nat)
  : Lemma (requires seq_all_valid s /\ i < Seq.length s)
          (ensures entry_valid (Seq.index s i))
          (decreases Seq.length s) =
  if i = 0 then ()
  else seq_all_valid_index (Seq.tail s) (i - 1)

let rec seq_to_spec_index (s: Seq.seq entry) (i: nat)
  : Lemma (requires seq_all_valid s /\ i < Seq.length s)
          (ensures entry_valid (Seq.index s i) /\
                   Seq.index (seq_to_spec s) i == range_to_interval (fst (Seq.index s i)))
          (decreases Seq.length s) =
  seq_all_valid_index s i;
  if i = 0 then ()
  else seq_to_spec_index (Seq.tail s) (i - 1)

#pop-options

(*** tree_max ↔ spec last ***)

let tree_max_last_spec (t: T.tree range unit)
  : Lemma (requires T.Node? t /\ tree_wf t)
          (ensures (let s = T.inorder t in
                    Seq.length s > 0 /\
                    entry_valid (Seq.index s (Seq.length s - 1)) /\
                    Seq.index (tree_to_spec t) (Seq.length (tree_to_spec t) - 1) ==
                      range_to_interval (fst (Seq.index s (Seq.length s - 1))) /\
                    T.tree_max t == Seq.index s (Seq.length s - 1))) =
  T.tree_max_last_inorder t;
  let s = T.inorder t in
  let n = Seq.length s in
  seq_to_spec_index s (n - 1)

(*** Pure implementations ***)

#push-options "--z3rlimit_factor 4 --fuel 2 --ifuel 2"

let rec add_range_impl (l: list entry) (off len: SZ.t)
  : Pure (list entry)
    (requires list_valid l /\ SZ.v len > 0 /\ SZ.fits (SZ.v off + SZ.v len))
    (ensures fun r -> list_valid r /\
                      list_to_spec r == Spec.add_range (list_to_spec l) (SZ.v off) (SZ.v len))
    (decreases List.Tot.length l) =
  match l with
  | [] ->
    let e = mk_entry off len in
    assert (Seq.equal (list_to_spec [e])
                      (Spec.add_range (list_to_spec []) (SZ.v off) (SZ.v len)));
    [e]
  | hd :: tl ->
    let hd_low = (fst hd).start in
    let hd_count = (fst hd).len in
    let hd_high = SZ.add hd_low hd_count in
    let off_plus_len = SZ.add off len in
    let hd_spec = range_to_interval (fst hd) in
    let tl_spec = list_to_spec tl in
    assert (list_to_spec l == Seq.cons hd_spec tl_spec);
    assert (Seq.length (list_to_spec l) > 0);
    assert (Seq.index (list_to_spec l) 0 == hd_spec);
    assert (Seq.tail (list_to_spec l) `Seq.equal` tl_spec);
    assert (Spec.high hd_spec == SZ.v hd_high);
    if SZ.lt off_plus_len hd_low then (
      let e = mk_entry off len in
      assert (SZ.v off + SZ.v len < SZ.v hd_low);
      assert (SZ.v off_plus_len < hd_spec.Spec.low);
      assert (Seq.equal (list_to_spec (e :: l))
                        (Seq.cons (range_to_interval (fst e)) (list_to_spec l)));
      e :: l
    )
    else if SZ.lt hd_high off then (
      assert (Spec.high hd_spec < SZ.v off);
      let r = add_range_impl tl off len in
      assert (list_to_spec r == Spec.add_range tl_spec (SZ.v off) (SZ.v len));
      assert (Seq.equal (list_to_spec (hd :: r))
                        (Seq.cons hd_spec (list_to_spec r)));
      hd :: r
    )
    else (
      let merged_low = (if SZ.lt off hd_low then off else hd_low) in
      let merged_high = (if SZ.gt off_plus_len hd_high then off_plus_len else hd_high) in
      assert (SZ.v merged_high > SZ.v merged_low);
      let new_len = SZ.sub merged_high merged_low in
      assert (SZ.v new_len > 0);
      assert (SZ.fits (SZ.v merged_low + SZ.v new_len));
      add_range_impl tl merged_low new_len
    )

#pop-options

(*** Rebuild: list → tree ***)

let rec list_to_tree_fwd (l: list entry) (acc: T.tree range unit)
  : Tot (T.tree range unit) (decreases l) =
  match l with
  | [] -> acc
  | hd :: tl -> list_to_tree_fwd tl (T.insert_avl range_cmp acc (fst hd) (snd hd))

let rec list_to_seq (l: list entry)
  : Tot (Seq.seq entry) (decreases l) =
  match l with
  | [] -> Seq.empty
  | hd :: tl -> Seq.cons hd (list_to_seq tl)

let rec list_sorted (l: list entry) : prop =
  match l with
  | [] -> True
  | [_] -> True
  | a :: b :: rest -> range_cmp_fn (fst a) (fst b) < 0 /\ list_sorted (b :: rest)

let rec fold_sorted_insert (l: list entry) (s: Seq.seq entry)
  : Tot (Seq.seq entry) (decreases l) =
  match l with
  | [] -> s
  | hd :: tl -> fold_sorted_insert tl (T.sorted_insert range_cmp hd s)

#push-options "--fuel 3 --z3rlimit 60"

/// Helper: in a sorted sequence, if last < k then head < k
let rec sorted_head_lt (s: Seq.seq entry) (k: entry)
  : Lemma (requires T.sorted range_cmp s /\ Seq.length s > 0 /\
                    range_cmp_fn (fst (Seq.index s (Seq.length s - 1))) (fst k) < 0)
          (ensures range_cmp_fn (fst (Seq.head s)) (fst k) < 0)
          (decreases Seq.length s) =
  if Seq.length s = 1 then ()
  else sorted_head_lt (Seq.tail s) k

let rec sorted_insert_snoc (k: entry) (s: Seq.seq entry)
  : Lemma (requires T.sorted range_cmp s /\
                    (Seq.length s = 0 \/ range_cmp_fn (fst (Seq.index s (Seq.length s - 1))) (fst k) < 0))
          (ensures T.sorted_insert range_cmp k s == Seq.snoc s k)
          (decreases Seq.length s) =
  if Seq.length s = 0 then
    assert (Seq.equal (T.sorted_insert range_cmp k s) (Seq.snoc s k))
  else (
    sorted_head_lt s k;
    assert (range_cmp_fn (fst (Seq.head s)) (fst k) < 0);
    if Seq.length s = 1 then
      assert (Seq.equal (T.sorted_insert range_cmp k s) (Seq.snoc s k))
    else (
      sorted_insert_snoc k (Seq.tail s);
      assert (Seq.equal (Seq.snoc s k) (Seq.cons (Seq.head s) (Seq.snoc (Seq.tail s) k)))
    )
  )

let rec sorted_snoc (s: Seq.seq entry) (k: entry)
  : Lemma (requires T.sorted range_cmp s /\
                    (Seq.length s = 0 \/ range_cmp_fn (fst (Seq.index s (Seq.length s - 1))) (fst k) < 0))
          (ensures T.sorted range_cmp (Seq.snoc s k))
          (decreases Seq.length s) =
  let s' = Seq.snoc s k in
  if Seq.length s = 0 then ()
  else if Seq.length s = 1 then (
    sorted_head_lt s k
  )
  else (
    sorted_snoc (Seq.tail s) k;
    assert (Seq.index s' 0 == Seq.index s 0);
    assert (Seq.index s' 1 == Seq.index s 1);
    assert (Seq.equal (Seq.tail s') (Seq.snoc (Seq.tail s) k))
  )

let rec fold_sorted_insert_is_append (l: list entry) (s: Seq.seq entry)
  : Lemma (requires list_sorted l /\ T.sorted range_cmp s /\
                    (Seq.length s = 0 \/ List.Tot.length l = 0 \/
                     range_cmp_fn (fst (Seq.index s (Seq.length s - 1))) (fst (List.Tot.hd l)) < 0))
          (ensures fold_sorted_insert l s == Seq.append s (list_to_seq l))
          (decreases l) =
  match l with
  | [] -> assert (Seq.equal (Seq.append s (list_to_seq [])) s)
  | [hd] ->
    sorted_insert_snoc hd s;
    assert (Seq.equal (Seq.snoc s hd) (Seq.append s (Seq.create 1 hd)));
    assert (Seq.equal (list_to_seq [hd]) (Seq.create 1 hd))
  | hd :: tl ->
    sorted_insert_snoc hd s;
    sorted_snoc s hd;
    assert (Seq.index (Seq.snoc s hd) (Seq.length (Seq.snoc s hd) - 1) == hd);
    fold_sorted_insert_is_append tl (Seq.snoc s hd);
    Seq.append_assoc s (Seq.create 1 hd) (list_to_seq tl);
    assert (Seq.equal (Seq.snoc s hd) (Seq.append s (Seq.create 1 hd)));
    assert (Seq.equal (Seq.cons hd (list_to_seq tl)) (Seq.append (Seq.create 1 hd) (list_to_seq tl)));
    assert (Seq.equal (list_to_seq (hd :: tl)) (Seq.cons hd (list_to_seq tl)))

let rec list_to_tree_fwd_inorder (l: list entry) (acc: T.avl range unit range_cmp)
  : Lemma (ensures T.inorder (list_to_tree_fwd l acc) == fold_sorted_insert l (T.inorder acc))
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl ->
    T.insert_avl_inorder range_cmp acc (fst hd) (snd hd);
    T.insert_avl_proof range_cmp acc (fst hd) (snd hd);
    list_to_tree_fwd_inorder tl (T.insert_avl range_cmp acc (fst hd) (snd hd))

let list_to_tree_fwd_correct (l: list entry)
  : Lemma (requires list_sorted l)
          (ensures T.inorder (list_to_tree_fwd l T.Leaf) == list_to_seq l) =
  list_to_tree_fwd_inorder l T.Leaf;
  fold_sorted_insert_is_append l Seq.empty;
  assert (Seq.equal (Seq.append Seq.empty (list_to_seq l)) (list_to_seq l))

let rec list_to_tree_fwd_avl (l: list entry) (acc: T.avl range unit range_cmp)
  : Lemma (ensures T.is_avl range_cmp (list_to_tree_fwd l acc))
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl ->
    T.insert_avl_proof range_cmp acc (fst hd) (snd hd);
    list_to_tree_fwd_avl tl (T.insert_avl range_cmp acc (fst hd) (snd hd))

let rec list_to_tree_fwd_snoc_gen (l: list entry) (x: entry) (acc: T.tree range unit)
  : Lemma (ensures list_to_tree_fwd (List.Tot.append l [x]) acc ==
                   T.insert_avl range_cmp (list_to_tree_fwd l acc) (fst x) (snd x))
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl -> list_to_tree_fwd_snoc_gen tl x (T.insert_avl range_cmp acc (fst hd) (snd hd))

let list_to_tree_fwd_snoc (l: list entry) (x: entry)
  : Lemma (ensures list_to_tree_fwd (List.Tot.append l [x]) T.Leaf ==
                   T.insert_avl range_cmp (list_to_tree_fwd l T.Leaf) (fst x) (snd x)) =
  list_to_tree_fwd_snoc_gen l x T.Leaf

#pop-options

(*** list_to_seq ↔ seq_to_spec bridge ***)

let rec list_to_seq_spec_eq (l: list entry)
  : Lemma (requires list_valid l)
          (ensures seq_all_valid (list_to_seq l) /\
                   seq_to_spec (list_to_seq l) == list_to_spec l)
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl ->
    list_to_seq_spec_eq tl;
    let s = list_to_seq (hd :: tl) in
    assert (Seq.head s == hd);
    assert (Seq.equal (Seq.tail s) (list_to_seq tl))

(*** Extract-rebuild bridge lemmas ***)

/// Lemma 1: sorted_remove of head element gives tail
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"

let sorted_remove_head (#k #v: Type) (cmp: T.cmp k) (s: Seq.seq (k & v))
  : Lemma (requires Seq.length s > 0)
          (ensures Seq.equal (T.sorted_remove cmp (fst (Seq.head s)) s) (Seq.tail s)) =
  let hd = Seq.head s in
  assert (cmp (fst hd) (fst hd) == 0);
  ()

#pop-options

/// Lemma 2: delete_min removes minimum (leftmost) element from BST
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

let delete_min_is_tail_inorder (t: T.tree range unit)
  : Lemma (requires T.is_bst range_cmp t /\ T.no_dup_tree range_cmp t /\ T.Node? t)
          (ensures Seq.equal 
                    (T.inorder (T.delete_avl range_cmp t (fst (T.tree_min t))))
                    (Seq.tail (T.inorder t))) =
  tree_min_head_inorder t;
  T.delete_avl_inorder range_cmp t (fst (T.tree_min t));
  sorted_remove_head range_cmp (T.inorder t);
  ()

#pop-options

/// Lemma 3: list_valid from seq_valid
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"

let rec list_valid_from_seq_valid (l: list entry)
  : Lemma (requires seq_all_valid (list_to_seq l))
          (ensures list_valid l)
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl ->
    // seq_all_valid (list_to_seq (hd :: tl))
    // ==> seq_all_valid (Seq.cons hd (list_to_seq tl))
    // ==> entry_valid (Seq.head (Seq.cons hd ...)) /\ seq_all_valid (Seq.tail (Seq.cons hd ...))
    // ==> entry_valid hd /\ seq_all_valid (list_to_seq tl)
    assert (Seq.head (list_to_seq (hd :: tl)) == hd);
    assert (Seq.equal (Seq.tail (list_to_seq (hd :: tl))) (list_to_seq tl));
    list_valid_from_seq_valid tl

#pop-options

/// Lemma 4: range_map_wf implies list_sorted (length >= 2 case)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

let rec range_map_wf_list_sorted (l: list entry)
  : Lemma (requires list_valid l /\ 
                    Spec.range_map_wf (list_to_spec l) /\
                    List.Tot.length l >= 2)
          (ensures list_sorted l)
          (decreases l) =
  match l with
  | [] -> ()  // Impossible: length >= 2
  | [_] -> ()  // Impossible: length >= 2
  | a :: b :: rest ->
    // We need to show: range_cmp_fn a b < 0 /\ list_sorted (b :: rest)
    
    // From range_map_wf (list_to_spec (a :: b :: rest)):
    // Seq.index (list_to_spec l) 0 is range_to_interval a
    // Seq.index (list_to_spec l) 1 is range_to_interval b
    let spec_seq = list_to_spec l in
    assert (Seq.length spec_seq >= 2);
    
    let a_spec = range_to_interval (fst a) in
    let b_spec = range_to_interval (fst b) in
    
    assert (Seq.index spec_seq 0 == a_spec);
    assert (Seq.index spec_seq 1 == b_spec);
    
    // range_map_wf says: separated (index 0) (index 1)
    // separated means: high a_spec < b_spec.low
    assert (Spec.high a_spec < b_spec.Spec.low);
    assert (Spec.high a_spec == a_spec.Spec.low + a_spec.Spec.count);
    assert (a_spec.Spec.low == SZ.v (fst a).start);
    assert (a_spec.Spec.count == SZ.v (fst a).len);
    assert (b_spec.Spec.low == SZ.v (fst b).start);
    
    assert (SZ.v (fst a).start + SZ.v (fst a).len < SZ.v (fst b).start);
    assert (SZ.v (fst a).len > 0);
    assert (SZ.v (fst a).start < SZ.v (fst b).start);
    
    assert (range_cmp_fn (fst a) (fst b) == -1);
    assert (range_cmp_fn (fst a) (fst b) < 0);
    
    // Now prove list_sorted (b :: rest)
    match rest with
    | [] -> ()  // list_sorted [b] is True by definition
    | c :: _ ->
      // Need to prove list_sorted (b :: c :: ...)
      // This requires: Spec.range_map_wf (list_to_spec (b :: c :: ...))
      // Which follows from Spec.range_map_wf (list_to_spec (a :: b :: c :: ...))
      
      // range_map_wf (list_to_spec l) implies range_map_wf (Seq.tail (list_to_spec l))
      assert (Seq.equal (Seq.tail spec_seq) (list_to_spec (b :: rest)));
      
      // Use induction
      range_map_wf_list_sorted (b :: rest)

#pop-options

/// Lemma 5: range_map_wf implies list_sorted (all cases)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

let range_map_wf_list_sorted_full (l: list entry)
  : Lemma (requires list_valid l /\ Spec.range_map_wf (list_to_spec l))
          (ensures list_sorted l) =
  match l with
  | [] -> ()  // list_sorted [] is True
  | [_] -> ()  // list_sorted [_] is True
  | _ :: _ :: _ ->
    // Length >= 2, use the main lemma
    range_map_wf_list_sorted l

#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

/// Bridge: list_sorted implies T.sorted_strict on list_to_seq
let rec list_sorted_to_sorted_strict (l: list entry)
  : Lemma (requires list_sorted l)
          (ensures T.sorted_strict range_cmp (list_to_seq l))
          (decreases l) =
  match l with
  | [] -> ()
  | [_] -> ()
  | a :: b :: rest ->
    list_sorted_to_sorted_strict (b :: rest);
    assert (Seq.head (list_to_seq l) == a);
    assert (Seq.index (list_to_seq l) 1 == b);
    assert (Seq.equal (Seq.tail (list_to_seq l)) (list_to_seq (b :: rest)))

#pop-options

(*** Validity preservation lemmas ***)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"

/// M2: Removing an element from a valid seq preserves validity
let rec seq_all_valid_sorted_remove (cmp: T.cmp range) (k: range)
  (s: Seq.seq entry)
  : Lemma (requires seq_all_valid s)
          (ensures seq_all_valid (T.sorted_remove cmp k s))
          (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else if cmp (fst (Seq.head s)) k = 0 then ()
  else (
    seq_all_valid_sorted_remove cmp k (Seq.tail s);
    let result = T.sorted_remove cmp k s in
    assert (Seq.length result > 0);
    assert (Seq.head result == Seq.head s);
    assert (Seq.equal (Seq.tail result) (T.sorted_remove cmp k (Seq.tail s)))
  )

/// M3: list_valid implies seq_all_valid on list_to_seq
let rec list_valid_to_seq_all_valid (l: list entry)
  : Lemma (requires list_valid l)
          (ensures seq_all_valid (list_to_seq l))
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl ->
    list_valid_to_seq_all_valid tl;
    assert (Seq.head (list_to_seq (hd :: tl)) == hd);
    assert (Seq.equal (Seq.tail (list_to_seq (hd :: tl))) (list_to_seq tl))

#pop-options

(*** Extraction/rebuild helper lemmas ***)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"

/// Helper: cons head (tail s) == s for non-empty sequences
let cons_head_tail (s: Seq.seq entry)
  : Lemma (requires Seq.length s > 0)
          (ensures Seq.equal (Seq.cons (Seq.head s) (Seq.tail s)) s) = ()

/// list_to_seq distributes over list append
let rec list_to_seq_append (l1 l2: list entry)
  : Lemma (ensures Seq.equal (list_to_seq (List.Tot.append l1 l2))
                              (Seq.append (list_to_seq l1) (list_to_seq l2)))
          (decreases l1) =
  match l1 with
  | [] -> ()
  | hd :: tl -> list_to_seq_append tl l2

/// After extracting min and prepending, the append invariant is maintained
let extract_step_invariant
  (acc_old: list entry)
  (ft_cur: T.tree range unit)
  (original_inorder: Seq.seq entry)
  : Lemma (requires 
      T.is_bst range_cmp ft_cur /\ T.no_dup_tree range_cmp ft_cur /\ T.Node? ft_cur /\
      Seq.append (list_to_seq (List.Tot.rev acc_old)) (T.inorder ft_cur) == original_inorder)
    (ensures (
      let min = T.tree_min ft_cur in
      let ft_new = T.delete_avl range_cmp ft_cur (fst min) in
      Seq.append (list_to_seq (List.Tot.rev (min :: acc_old))) (T.inorder ft_new) == original_inorder))
  = let min = T.tree_min ft_cur in
    let ft_new = T.delete_avl range_cmp ft_cur (fst min) in
    delete_min_is_tail_inorder ft_cur;
    tree_min_head_inorder ft_cur;
    List.Tot.Properties.rev_append [min] acc_old;
    assert (List.Tot.rev (min :: acc_old) == List.Tot.append (List.Tot.rev acc_old) [min]);
    list_to_seq_append (List.Tot.rev acc_old) [min];
    assert (Seq.equal (list_to_seq [min]) (Seq.create 1 min));
    Seq.append_assoc (list_to_seq (List.Tot.rev acc_old)) (Seq.create 1 min) (T.inorder ft_new);
    cons_head_tail (T.inorder ft_cur);
    assert (Seq.equal (Seq.append (Seq.create 1 min) (T.inorder ft_new)) (T.inorder ft_cur))

#pop-options

(*** Range set type and predicate ***)

let range_map_t = B.box (AVL.tree_t range unit)

/// Tracks whether the extraction loop should continue.
/// When b = false, the tree must be empty (Leaf).
[@@no_mkeys]
let extract_cont (b: bool) (ft: T.tree range unit) : slprop =
  pure (b == not (T.is_empty ft))

let is_range_map (rs: range_map_t) (repr: Seq.seq Spec.interval) : slprop =
  exists* (ct: AVL.tree_t range unit) (t: T.tree range unit).
    B.pts_to rs ct **
    AVL.is_tree ct t **
    pure (T.is_bst range_cmp t /\
          T.no_dup_tree range_cmp t /\
          tree_wf t /\
          tree_to_spec t == repr /\
          Spec.range_map_wf repr)

(*** Pulse operations ***)

fn range_map_create ()
  requires emp
  returns rs: range_map_t
  ensures is_range_map rs (Seq.empty #Spec.interval)
{
  let ct = AVL.create range unit;
  let rs = B.alloc ct;
  fold (is_range_map rs (Seq.empty #Spec.interval));
  rs
}

fn range_map_free (rs: range_map_t) (#repr: erased (Seq.seq Spec.interval))
  requires is_range_map rs repr
  ensures emp
{
  unfold is_range_map;
  with ct t. _;
  let h = B.op_Bang rs;
  AVL.free h;
  B.free rs
}

/// Get contiguous coverage length from a given base offset
fn range_map_contiguous_from (rs: range_map_t) (base: SZ.t) (#repr: erased (Seq.seq Spec.interval))
  requires is_range_map rs repr
  returns n: SZ.t
  ensures is_range_map rs repr ** pure (SZ.v n == Spec.contiguous_from repr (SZ.v base))
{
  unfold is_range_map;
  with ct t. _;
  let h = B.op_Bang rs;
  let b = AVL.is_empty h;
  if b {
    fold (is_range_map rs repr);
    0sz
  } else {
    let min_pair = AVL.find_min range_cmp h;
    tree_min_head_inorder t;
    seq_to_spec_head (T.inorder t);
    let r = fst min_pair;
    let r_high = SZ.add r.start r.len;
    if (SZ.lte r.start base && SZ.lt base r_high) {
      fold (is_range_map rs repr);
      SZ.sub r_high base
    } else {
      fold (is_range_map rs repr);
      0sz
    }
  }
}

fn range_map_max_endpoint (rs: range_map_t) (#repr: erased (Seq.seq Spec.interval))
  requires is_range_map rs repr
  returns n: SZ.t
  ensures is_range_map rs repr ** pure (SZ.v n == Spec.range_map_max_endpoint repr)
{
  unfold is_range_map;
  with ct t. _;
  let h = B.op_Bang rs;
  let b = AVL.is_empty h;
  if b {
    fold (is_range_map rs repr);
    0sz
  } else {
    let max_pair = AVL.find_max range_cmp h;
    tree_max_last_spec t;
    let r = fst max_pair;
    let result = SZ.add r.start r.len;
    fold (is_range_map rs repr);
    result
  }
}

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"

fn range_map_add (rs: range_map_t) (offset: SZ.t) (len: SZ.t{SZ.v len > 0})
  (#repr: erased (Seq.seq Spec.interval))
  requires is_range_map rs repr ** pure (SZ.fits (SZ.v offset + SZ.v len))
  ensures is_range_map rs (Spec.add_range repr (SZ.v offset) (SZ.v len))
{
  unfold is_range_map;
  with ct t. _;
  
  let h = B.op_Bang rs;
  
  let mut acc: list entry = [];
  let mut tree = h;
  let initial_empty = AVL.is_empty h;
  
  assert (pure (Seq.equal (Seq.append (list_to_seq (List.Tot.rev ([] #entry))) (T.inorder (G.reveal t))) (T.inorder (G.reveal t))));
  
  fold (extract_cont (not initial_empty) (G.reveal t));
  
  while (
    let tree_ref = !tree;
    let acc_ref = !acc;
    with b_old ft_cur. unfold (extract_cont b_old ft_cur);
    let is_emp = AVL.is_empty tree_ref;
    
    if (not is_emp) {
      let min = AVL.find_min range_cmp tree_ref;
      tree_min_head_inorder ft_cur;
      
      let tree' = AVL.delete_avl range_cmp tree_ref (fst min);
      T.delete_avl_preserves_bst range_cmp ft_cur (fst min);
      T.delete_avl_preserves_no_dup_tree range_cmp ft_cur (fst min);
      T.delete_avl_inorder range_cmp ft_cur (fst min);
      seq_all_valid_sorted_remove range_cmp (fst min) (T.inorder ft_cur);
      delete_min_is_tail_inorder ft_cur;
      
      acc := min :: acc_ref;
      extract_step_invariant acc_ref ft_cur (T.inorder (G.reveal t));
      
      tree := tree';
      
      let e = AVL.is_empty tree';
      fold (extract_cont (not e) (T.delete_avl range_cmp ft_cur (fst (T.tree_min ft_cur))));
      not e
    } else {
      fold (extract_cont false ft_cur);
      false
    }
  )
  invariant b. exists* tree_val acc_val ft_cur.
    R.pts_to tree tree_val **
    R.pts_to acc acc_val **
    AVL.is_tree tree_val ft_cur **
    extract_cont b ft_cur **
    pure (T.is_bst range_cmp ft_cur /\
          T.no_dup_tree range_cmp ft_cur /\
          tree_wf ft_cur /\
          Seq.append (list_to_seq (List.Tot.rev acc_val)) (T.inorder ft_cur) == T.inorder (G.reveal t))
  { () };
  
  with tree_val acc_val ft_cur. _;
  unfold (extract_cont false ft_cur);
  
  // false == not (T.is_empty ft_cur) → T.is_empty ft_cur → ft_cur == Leaf
  Seq.append_empty_r (list_to_seq (List.Tot.rev acc_val));
  let tree_final = !tree;
  AVL.free tree_final;
  
  let acc_final = !acc;
  let extracted = List.Tot.rev acc_final;
  
  assert (pure (list_to_seq extracted == T.inorder (G.reveal t)));
  list_valid_from_seq_valid extracted;
  list_to_seq_spec_eq extracted;
  
  Spec.add_range_wf repr (SZ.v offset) (SZ.v len);
  let transformed = add_range_impl extracted offset len;
  
  range_map_wf_list_sorted_full transformed;
  list_valid_to_seq_all_valid transformed;
  list_to_tree_fwd_correct transformed;
  list_to_tree_fwd_avl transformed T.Leaf;
  
  let mut new_tree = AVL.create range unit;
  let mut remaining = transformed;
  let mut processed_add: list entry = [];
  
  while (
    let r = !remaining;
    Cons? r
  )
  invariant exists* new_tree_val remaining_val ft_new proc_val.
    R.pts_to new_tree new_tree_val **
    R.pts_to remaining remaining_val **
    R.pts_to processed_add proc_val **
    AVL.is_tree new_tree_val ft_new **
    pure (ft_new == list_to_tree_fwd proc_val T.Leaf /\
          T.is_avl range_cmp ft_new /\
          List.Tot.append proc_val remaining_val == transformed)
  {
    with new_tree_val remaining_val ft_new proc_val. _;
    
    let new_tree_curr = !new_tree;
    let remaining_curr = !remaining;
    let proc_curr = !processed_add;
    
    let Cons hd tl = remaining_curr;
    
    let new_tree' = AVL.insert_avl range_cmp new_tree_curr (fst hd) (snd hd);
    T.insert_avl_proof range_cmp ft_new (fst hd) (snd hd);
    
    list_to_tree_fwd_snoc proc_curr hd;
    List.Tot.Properties.append_assoc proc_curr [hd] tl;
    
    remaining := tl;
    new_tree := new_tree';
    processed_add := List.Tot.append proc_curr [hd]
  };
  
  with new_tree_val remaining_val ft_new proc_val. _;
  
  assert (pure (List.Tot.append proc_val [] == transformed));
  List.Tot.Properties.append_l_nil proc_val;
  
  let final_tree = !new_tree;
  B.op_Colon_Equals rs final_tree;
  
  // is_bst from is_avl
  list_to_tree_fwd_correct transformed;
  list_to_tree_fwd_avl transformed T.Leaf;
  
  // no_dup_tree from sorted_strict + bst
  list_sorted_to_sorted_strict transformed;
  T.bst_strict_sorted_no_dup range_cmp (list_to_tree_fwd transformed T.Leaf);
  
  // tree_wf: seq_all_valid (T.inorder ft_new)
  list_valid_to_seq_all_valid transformed;
  
  // tree_to_spec: chain through list_to_spec
  list_to_seq_spec_eq transformed;
  
  fold (is_range_map rs (Spec.add_range repr (SZ.v offset) (SZ.v len)))
}

#pop-options
