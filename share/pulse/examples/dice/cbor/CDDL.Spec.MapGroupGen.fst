module CDDL.Spec.MapGroupGen
include CDDL.Spec.Base
module Cbor = CBOR.Spec
module U8 = FStar.UInt8
module U64 = FStar.UInt64

let rec is_sublist_of
  (#t: Type)
  (l1 l2: list t)
: Tot prop
  (decreases l2)
= match l1, l2 with
  | [], _ -> True
  | _, [] -> False
  | a1 :: q1, a2 :: q2 ->
    (a1 == a2 /\ q1 `is_sublist_of` q2) \/
    l1 `is_sublist_of` q2

let rec is_sublist_of_length
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (requires (is_sublist_of l1 l2))
  (ensures (List.Tot.length l1 <= List.Tot.length l2))
  (decreases l2)
  [SMTPat (is_sublist_of l1 l2)]
= match l1, l2 with
  | [], _ -> ()
  | a1 :: q1, a2 :: q2 ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 == a2 /\ q1 `is_sublist_of` q2)
    then is_sublist_of_length q1 q2
    else is_sublist_of_length l1 q2

let rec is_sublist_of_length_eq
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (requires (
    is_sublist_of l1 l2 /\
    List.Tot.length l1 == List.Tot.length l2
  ))
  (ensures l1 == l2)
  (decreases l2)
= match l1, l2 with
  | [], _ -> ()
  | a1 :: q1, a2 :: q2 -> is_sublist_of_length_eq q1 q2

let rec is_sublist_of_refl
  (#t: Type)
  (l: list t)
: Lemma
  (l `is_sublist_of` l)
  [SMTPat (l `is_sublist_of` l)]
= match l with
  | [] -> ()
  | a :: q -> is_sublist_of_refl q

let rec is_sublist_of_trans
  (#t: Type)
  (l1 l2 l3: list t)
: Lemma
  (requires (
    is_sublist_of l1 l2 /\
    is_sublist_of l2 l3
  ))
  (ensures (
    is_sublist_of l1 l3
  ))
  (decreases l3)
  [SMTPatOr [
    [SMTPat (is_sublist_of l1 l2); SMTPat (is_sublist_of l2 l3)];
    [SMTPat (is_sublist_of l1 l3); SMTPat (is_sublist_of l2 l3)];
    [SMTPat (is_sublist_of l1 l3); SMTPat (is_sublist_of l1 l2)];
  ]]
= match l1, l2, l3 with
  | [], _, _ -> ()
  | a1 :: q1, a2 :: q2, a3 :: q3 ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a2 == a3 /\ q2 `is_sublist_of` q3)
    then begin
      if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 == a2 /\ q1 `is_sublist_of` q2)
      then is_sublist_of_trans q1 q2 q3
      else is_sublist_of_trans l1 q2 q3
    end
    else begin
      is_sublist_of_trans l1 l2 q3
    end

let rec is_sublist_of_append_right_intro
  (#t: Type)
  (l1 l2 l: list t)
: Lemma
  (requires is_sublist_of l1 l2)
  (ensures is_sublist_of (l1 `List.Tot.append` l) (l2 `List.Tot.append` l))
  (decreases (List.Tot.length l2 + List.Tot.length l))
= match l1, l2, l with
  | _, _, [] -> List.Tot.append_l_nil l1; List.Tot.append_l_nil l2
  | _, [], _ -> ()
  | [], a2 :: q2, _ -> is_sublist_of_append_right_intro [] q2 l
  | a1 :: q1, a2 :: q2, a :: q ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 == a2 /\ is_sublist_of q1 q2)
    then is_sublist_of_append_right_intro q1 q2 l
    else is_sublist_of_append_right_intro l1 q2 l

let rec is_sublist_of_append_right_elim
  (#t: Type)
  (l1 l2 l: list t)
: Lemma
  (requires is_sublist_of (l1 `List.Tot.append` l) (l2 `List.Tot.append` l))
  (ensures is_sublist_of l1 l2)
  (decreases (List.Tot.length l2 + List.Tot.length l))
= match l1, l2, l with
  | _, _, [] -> List.Tot.append_l_nil l1; List.Tot.append_l_nil l2
  | _, [], _ -> List.Tot.append_length l1 l
  | [], a2 :: q2, _ -> is_sublist_of_append_right_intro [] q2 l
  | a1 :: q1, a2 :: q2, a :: q ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 == a2 /\ is_sublist_of (q1 `List.Tot.append` l) (q2 `List.Tot.append` l))
    then is_sublist_of_append_right_elim q1 q2 l
    else is_sublist_of_append_right_elim l1 q2 l

let is_sublist_of_append_right
  (#t: Type)
  (l1 l2 l: list t)
: Lemma
  (is_sublist_of (l1 `List.Tot.append` l) (l2 `List.Tot.append` l) <==>
    is_sublist_of l1 l2)
  [SMTPat (is_sublist_of (l1 `List.Tot.append` l) (l2 `List.Tot.append` l))]
= Classical.move_requires (is_sublist_of_append_right_elim l1 l2) l;
  Classical.move_requires (is_sublist_of_append_right_intro l1 l2) l

let rec is_sublist_of_append_left_intro
  (#t: Type)
  (l l1 l2: list t)
: Lemma
  (requires (is_sublist_of l1 l2))
  (ensures (is_sublist_of (l `List.Tot.append` l1) (l `List.Tot.append` l2)))
  (decreases l)
  [SMTPat (is_sublist_of (l `List.Tot.append` l1) (l `List.Tot.append` l2))]
= match l with
  | [] -> ()
  | a :: q -> is_sublist_of_append_left_intro q l1 l2

let is_sublist_of_append_intro
  (#t: Type)
  (l1 l2: list t)
  (l1' l2': list t)
: Lemma
  (requires (
    is_sublist_of l1 l1' /\ is_sublist_of l2 l2'
  ))
  (ensures (
    is_sublist_of (l1 `List.Tot.append` l2) (l1' `List.Tot.append` l2')
  ))
= assert (is_sublist_of (l1 `List.Tot.append` l2) (l1' `List.Tot.append` l2))

let list_remove_sublist_is_sublist_of
  (#t: Type)
  (l1: list t)
  (a: list t)
  (l2: list t)
: Lemma
  (ensures ((l1 `List.Tot.append` l2) `is_sublist_of` (l1 `List.Tot.append` (a `List.Tot.append` l2))))
= assert ([] `is_sublist_of` a);
  assert (([] `List.Tot.append` l2) `is_sublist_of` (a `List.Tot.append` l2))

let list_remove_is_sublist_of
  (#t: Type)
  (l1: list t)
  (a: t)
  (l2: list t)
: Lemma
  (ensures ((l1 `List.Tot.append` l2) `is_sublist_of` (l1 `List.Tot.append` (a :: l2))))
= list_remove_sublist_is_sublist_of l1 [a] l2

let rec list_for_all_is_sublist_of
  (#t: Type)
  (p: (t -> bool))
  (l1 l2: list t)
: Lemma
    (requires
      l1 `is_sublist_of` l2 /\
      List.Tot.for_all p l2
    )
    (ensures (List.Tot.for_all p l1))
    (decreases l2)
= match l1, l2 with
  | [], _ -> ()
  | a1 :: q1, a2 :: q2 ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 == a2 /\ is_sublist_of q1 q2)
    then list_for_all_is_sublist_of p q1 q2
    else list_for_all_is_sublist_of p l1 q2

let rec list_memP_is_sublist_of
  (#t: Type)
  (x: t)
  (l1 l2: list t)
: Lemma
  (requires
    l1 `is_sublist_of` l2 /\
    List.Tot.memP x l1
  )
  (ensures List.Tot.memP x l2)
  (decreases l2)
= match l1, l2 with
  | a1 :: q1, a2 :: q2 ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a2 == x)
    then ()
    else if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 == a2 /\ is_sublist_of q1 q2)
    then list_memP_is_sublist_of x q1 q2
    else list_memP_is_sublist_of x l1 q2

let rec list_no_repeats_p_is_sublist_of
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (requires
    l1 `is_sublist_of` l2 /\
    List.Tot.no_repeats_p l2
  )
  (ensures List.Tot.no_repeats_p l1)
  (decreases l2)
= match l1, l2 with
  | [], _ -> ()
  | a1 :: q1, a2 :: q2 ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 == a2 /\ is_sublist_of q1 q2)
    then begin
      Classical.move_requires (list_memP_is_sublist_of a2 q1) q2;
      list_no_repeats_p_is_sublist_of q1 q2
    end else
      list_no_repeats_p_is_sublist_of l1 q2

let rec list_map_is_sublist_of
  (#t #t': Type)
  (f: t -> t')
  (l1 l2: list t)
: Lemma
  (requires l1 `is_sublist_of` l2)
  (ensures List.Tot.map f l1 `is_sublist_of` List.Tot.map f l2)
  (decreases l2)
= match l1, l2 with
  | [], _ -> ()
  | a1 :: q1, a2 :: q2 ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 == a2 /\ is_sublist_of q1 q2)
    then list_map_is_sublist_of f q1 q2
    else list_map_is_sublist_of f l1 q2

let rec list_filter_is_sublist_of_intro
  (#t: Type)
  (f: t -> bool)
  (l: list t)
: Lemma
  (ensures (List.Tot.filter f l `is_sublist_of` l))
  (decreases l)
  [SMTPat (List.Tot.filter f l)]
= match l with
  | [] -> ()
  | a :: q -> list_filter_is_sublist_of_intro f q

let notp
  (#t: Type)
  (p: (t -> Tot bool))
  (x: t)
: Tot bool
= not (p x)

let rec list_filter_and_extract
  (#t: Type)
  (f: (t -> Tot bool))
  (l: list t)
: Pure (option (list t & t & list t))
    (requires True)
    (ensures fun res -> match res with
      | None -> List.Tot.for_all (notp f) l
      | Some (l1, x, l2) ->
        List.Tot.for_all (notp f) l1 /\
        f x /\
        l == l1 `List.Tot.append` (x :: l2)
    )
= match l with
  | [] -> None
  | a :: q ->
    if f a
    then Some ([], a, q)
    else begin match list_filter_and_extract f q with
    | None -> None
    | Some (l1, x, l2) ->
      Some (a :: l1, x, l2)
    end

let map_group_post
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (res: FStar.GSet.set (list (Cbor.raw_data_item & Cbor.raw_data_item)))
: Tot prop
=
      forall (l': list (Cbor.raw_data_item & Cbor.raw_data_item)) .
      FStar.GSet.mem l' res ==> l' `is_sublist_of` l

let map_group : Type0 =
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item)) -> Ghost (FStar.GSet.set (list (Cbor.raw_data_item & Cbor.raw_data_item)))
    (requires True)
    (ensures fun res -> map_group_post l res)

let map_group_always_false : map_group =
  fun _ -> FStar.GSet.empty

let map_group_end : map_group =
  fun l -> if Nil? l then FStar.GSet.singleton l else FStar.GSet.empty

let map_group_nop : map_group =
  fun l -> FStar.GSet.singleton l

let map_group_match_item_witness_pred (key value: typ) (l l': list (Cbor.raw_data_item & Cbor.raw_data_item)) (x: (list (Cbor.raw_data_item & Cbor.raw_data_item) & (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item))) : Tot prop =
  let (l1, (k, v), l2) = x in
      l == l1 `List.Tot.append` ((k, v) :: l2) /\
      l' == l1 `List.Tot.append` l2 /\
      key k /\
      value v
 
let map_group_match_item_witness_pred_is_sublist_of (key value: typ) (l l': list (Cbor.raw_data_item & Cbor.raw_data_item)) x : Lemma
  (requires (map_group_match_item_witness_pred key value l l' x))
  (ensures (l' `is_sublist_of` l))
  [SMTPat (map_group_match_item_witness_pred key value l l' x)]
= let (l1, kv, l2) = x in
  list_remove_is_sublist_of l1 kv l2

let map_group_match_item (key value: typ) : map_group =
  fun l -> FStar.GSet.comprehend (fun l' ->
    FStar.StrongExcludedMiddle.strong_excluded_middle (exists x .
      map_group_match_item_witness_pred key value l l' x
  ))

let gset_map_witness_pred (#t1 #t2: Type) (f: t1 -> GTot t2) (s: FStar.GSet.set t1) x2 x1 : GTot prop =
  x2 == f x1 /\ FStar.GSet.mem x1 s

let gset_map (#t1 #t2: Type) (f: t1 -> GTot t2) (s: FStar.GSet.set t1) : FStar.GSet.set t2 =
  FStar.GSet.comprehend (fun x2 -> FStar.StrongExcludedMiddle.strong_excluded_middle (exists x1 .
    gset_map_witness_pred f s x2 x1
  ))

let matches_map_group_entry
  (key value: typ)
  (x: (Cbor.raw_data_item & Cbor.raw_data_item))
: GTot bool
= key (fst x) && value (snd x)

module Pull = FStar.Ghost.Pull

let map_group_match_item_alt (key value: typ) (l: list (Cbor.raw_data_item & Cbor.raw_data_item)) : GTot (FStar.GSet.set (list (Cbor.raw_data_item & Cbor.raw_data_item))) =
  match list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry key value)) l with
  | None -> FStar.GSet.empty
  | Some (l1, x, l2) -> FStar.GSet.union (FStar.GSet.singleton (l1 `List.Tot.append` l2)) (gset_map (List.Tot.append (l1 `List.Tot.append` [x])) (map_group_match_item key value l2))

let map_group_match_item_alt_map_group_match_item
  (key value: typ) (l l': list (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (FStar.GSet.mem l' (map_group_match_item_alt key value l) ==> FStar.GSet.mem l' (map_group_match_item key value l))
= if FStar.GSet.mem l' (map_group_match_item_alt key value l)
  then begin
    let Some (l1, x, l2) = list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry key value)) l in
    if FStar.StrongExcludedMiddle.strong_excluded_middle (l' == l1 `List.Tot.append` l2)
    then assert (map_group_match_item_witness_pred key value l l' (l1, x, l2))
    else begin
      let l2' = FStar.IndefiniteDescription.indefinite_description_ghost _ (gset_map_witness_pred (List.Tot.append (l1 `List.Tot.append` [x])) (map_group_match_item key value l2) l') in
      let (ll2', x', lr2') = FStar.IndefiniteDescription.indefinite_description_ghost _ (map_group_match_item_witness_pred key value l2 l2') in
      List.Tot.append_assoc l1 [x] (ll2' `List.Tot.append` (x' :: lr2'));
      List.Tot.append_assoc (l1 `List.Tot.append` [x]) ll2' (x' :: lr2');
      List.Tot.append_assoc (l1 `List.Tot.append` [x]) ll2' lr2';
      assert (map_group_match_item_witness_pred key value l l' ((l1 `List.Tot.append` [x]) `List.Tot.append` ll2', x', lr2'))
    end
  end

let rec list_filter_and_extract_length
  (#t: Type)
  (f: t -> bool)
  (ll1: list t)
  (lr1: list t)
  (ll2: list t)
  (x2: t)
  (lr2: list t)
: Lemma
  (requires
    ll1 `List.Tot.append` lr1 == ll2 `List.Tot.append` (x2 :: lr2) /\
    List.Tot.for_all (notp f) ll1 /\
    f x2
  )
  (ensures
    List.Tot.length ll1 <= List.Tot.length ll2
  )
  (decreases ll1)
= match ll1 with
  | [] -> ()
  | a1 :: ql1 ->
    begin match ll2 with
    | [] -> () // contradiction
    | _ :: ql2 -> list_filter_and_extract_length f ql1 lr1 ql2 x2 lr2
    end

let rec list_extract_prefix
  (#t: Type)
  (ll1: list t)
  (lr1: list t)
  (ll2: list t)
  (lr2: list t)
: Pure (list t)
  (requires
    ll1 `List.Tot.append` lr1 == ll2 `List.Tot.append` lr2 /\
    List.Tot.length ll1 <= List.Tot.length ll2
  )
  (ensures fun ll' -> ll2 == ll1 `List.Tot.append` ll')
  (decreases ll1)
= match ll1, ll2 with
  | [], _ -> ll2
  | a1 :: ql1, a2 :: ql2 -> list_extract_prefix ql1 lr1 ql2 lr2

#restart-solver
let map_group_match_item_map_group_match_item_alt
  (key value: typ) (l l': list (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (FStar.GSet.mem l' (map_group_match_item key value l) ==> FStar.GSet.mem l' (map_group_match_item_alt key value l))
= if FStar.GSet.mem l' (map_group_match_item key value l)
  then begin
    let (ll', x', lr') = FStar.IndefiniteDescription.indefinite_description_ghost _ (map_group_match_item_witness_pred key value l l') in
    List.Tot.for_all_append (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value))) ll' (x' :: lr');
    let Some (ll, x, lr) = list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry key value)) l in
    list_filter_and_extract_length (FStar.Ghost.Pull.pull (matches_map_group_entry key value)) ll (x :: lr) ll' x' lr';
    if List.Tot.length ll = List.Tot.length ll'
    then List.Tot.append_length_inv_head ll (x :: lr) ll' (x' :: lr')
    else begin
      List.Tot.append_assoc ll [x] lr;
      List.Tot.append_length ll [x];
      let lp = list_extract_prefix (ll `List.Tot.append` [x]) lr ll' (x' :: lr') in
      List.Tot.append_assoc (ll `List.Tot.append` [x]) lp (x' :: lr');
      List.Tot.append_inv_head (ll `List.Tot.append` [x]) lr (lp `List.Tot.append` (x' :: lr'));
      assert (map_group_match_item_witness_pred key value lr (lp `List.Tot.append` lr') (lp, x', lr'));
      List.Tot.append_assoc (ll `List.Tot.append` [x]) lp lr';
      assert (gset_map_witness_pred (List.Tot.append (ll `List.Tot.append` [x])) (map_group_match_item key value lr) l' (lp `List.Tot.append` lr'))
    end
  end

let map_group_equiv
  (m1 m2: map_group)
: Tot prop
= forall l . m1 l == m2 l

let map_group_match_item_alt_correct
  (key value: typ) (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (map_group_match_item_alt key value l == map_group_match_item key value l)
= Classical.forall_intro (map_group_match_item_map_group_match_item_alt key value l);
  Classical.forall_intro (map_group_match_item_alt_map_group_match_item key value l);
  assert (map_group_match_item_alt key value l `FStar.GSet.equal` map_group_match_item key value l)

let map_group_choice (m1 m2: map_group) : map_group =
  fun l ->
    // greedy PEG semantics for `//`
    let res1 = m1 l in
    if FStar.StrongExcludedMiddle.strong_excluded_middle (res1 == FStar.GSet.empty)
    then m2 l
    else res1

let map_group_zero_or_one (m: map_group) : map_group =
  map_group_choice m map_group_nop

let gset_collect_witness_pred (#t1 #t2: Type) (f: t1 -> GTot (FStar.GSet.set t2)) (s: FStar.GSet.set t1) x2 x1 : GTot prop =
  FStar.GSet.mem x1 s /\ FStar.GSet.mem x2 (f x1)

// a.k.a. "big union"
let gset_collect (#t1 #t2: Type) (f: t1 -> GTot (FStar.GSet.set t2)) (s: FStar.GSet.set t1) : FStar.GSet.set t2 =
  FStar.GSet.comprehend (fun x2 -> FStar.StrongExcludedMiddle.strong_excluded_middle (exists x1 .
    gset_collect_witness_pred f s x2 x1
  ))

let mk_cut (cut: typ) : Tot (FStar.GSet.set _) =
  FStar.GSet.comprehend (List.Tot.for_all (notp (Pull.pull (matches_map_group_entry cut any))))

let map_group_concat (cut: typ) (m1 m2: map_group) : map_group =
  fun l -> gset_collect m2 (FStar.GSet.intersect (mk_cut cut) (m1 l))

let bound_map_group
  (l0: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (m: (l: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.length l < List.Tot.length l0 }) ->
  Ghost (FStar.GSet.set (list (Cbor.raw_data_item & Cbor.raw_data_item)))
    (requires True)
    (ensures fun l' -> map_group_post l l')
  )
: map_group
= fun l -> if List.Tot.length l >= List.Tot.length l0 then FStar.GSet.singleton l else m l

// greedy PEG semantics for `*`
let rec map_group_zero_or_more
  (m: map_group)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Ghost (FStar.GSet.set (list (Cbor.raw_data_item & Cbor.raw_data_item)))
    (requires True)
    (ensures fun l' -> map_group_post l l')
    (decreases (List.Tot.length l))
= let res1 = m l in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (res1 == FStar.GSet.empty)
  then FStar.GSet.singleton l
  else gset_collect (bound_map_group l (map_group_zero_or_more m)) res1

let map_group_one_or_more (m: map_group) : map_group =
  // cuts must not be applied between iterations
  map_group_concat t_always_false m (map_group_zero_or_more m)

let map_group_match_item_for
  (k: Cbor.raw_data_item)
  (ty: typ)
: Tot map_group
= map_group_match_item (t_literal k) ty

let rec list_ghost_assoc_memP
  (#key #value: Type)
  (k: key)
  (l: list (key & value))
: Lemma
  (ensures (Some? (Cbor.list_ghost_assoc k l) <==> List.Tot.memP k (List.Tot.map fst l)))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> list_ghost_assoc_memP k q

let rec list_filter_and_extract_matches_map_group_entry_literal_memP_intro
  (k: Cbor.raw_data_item)
  (ty: typ)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (ensures (Some? (list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty)) l) ==> List.Tot.memP k (List.Tot.map fst l)))
  (decreases l)
= if Some? (list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty)) l)
  then
    let k'v' :: l' = l in
    list_filter_and_extract_matches_map_group_entry_literal_memP_intro k ty l'

let rec list_filter_and_extract_assoc
  (k: Cbor.raw_data_item)
  (ty: typ)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst l)))
  (ensures (match Cbor.list_ghost_assoc k l, list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty)) l with
  | None, None -> ~ (List.Tot.memP k (List.Tot.map fst l))
  | None, Some _ -> False
  | Some v, None -> ~ (ty v)
  | Some v, Some (ll, (k', v'), lr) ->
    k == k' /\
    v == v' /\
    ty v /\
    (~ (List.Tot.memP k (List.Tot.map fst ll))) /\
    (~ (List.Tot.memP k (List.Tot.map fst lr)))
  ))
  (decreases l)
= 
  list_ghost_assoc_memP k l;
  let f = FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty) in
  match l with
  | [] -> ()
  | (k', v') :: l' -> 
    list_filter_and_extract_assoc k ty l';
    list_ghost_assoc_memP k l';
    list_filter_and_extract_matches_map_group_entry_literal_memP_intro k ty l'

let map_group_match_item_for_no_repeats_none
  (k: Cbor.raw_data_item)
  (ty: typ)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst l) /\
    (~ (List.Tot.memP k (List.Tot.map fst l)))
  ))
  (ensures (
    map_group_match_item_for k ty l == FStar.GSet.empty
  ))
= map_group_match_item_alt_correct (t_literal k) ty l;
  list_filter_and_extract_assoc k ty l;
  list_ghost_assoc_memP k l

let is_sublist_of_suffix
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (ensures (l2 `is_sublist_of` (l1 `List.Tot.append` l2)))
= is_sublist_of_append_right_intro [] l1 l2

let is_sublist_of_prefix
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (ensures (l1 `is_sublist_of` (l1 `List.Tot.append` l2)))
= List.Tot.append_l_nil l1;
  is_sublist_of_append_left_intro l1 [] l2

let map_group_match_item_for_no_repeats
  (k: Cbor.raw_data_item)
  (ty: typ)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst l)))
  (ensures (
    map_group_match_item_for k ty l `FStar.GSet.equal` begin match list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty)) l with
    | None -> FStar.GSet.empty
    | Some (ll, _, lr) -> FStar.GSet.singleton (ll `List.Tot.append` lr)
    end
  ))
= map_group_match_item_alt_correct (t_literal k) ty l;
  list_filter_and_extract_assoc k ty l;
  match list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty)) l with
  | None -> ()
  | Some (ll, k'v', lr) ->
    List.Tot.append_length ll lr;
    is_sublist_of_suffix ll (k'v' :: lr);
    is_sublist_of_trans lr (k'v' :: lr) l;
    list_map_is_sublist_of fst lr l;
    list_no_repeats_p_is_sublist_of (List.Tot.map fst lr) (List.Tot.map fst l);
    map_group_match_item_for_no_repeats_none k ty lr

let t_map (g: map_group) : typ =
  fun x -> match x with
  | Cbor.Map m -> 
    FStar.StrongExcludedMiddle.strong_excluded_middle (List.Tot.no_repeats_p (List.Tot.map fst m)) &&
    FStar.GSet.mem [] (g m)
  | _ -> false

