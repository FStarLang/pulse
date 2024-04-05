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

val is_sublist_of_length
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (requires (is_sublist_of l1 l2))
  (ensures (List.Tot.length l1 <= List.Tot.length l2))
  (decreases l2)
  [SMTPat (is_sublist_of l1 l2)]

val is_sublist_of_refl
  (#t: Type)
  (l: list t)
: Lemma
  (l `is_sublist_of` l)
  [SMTPat (l `is_sublist_of` l)]

val is_sublist_of_trans
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
  [SMTPatOr [
    [SMTPat (is_sublist_of l1 l2); SMTPat (is_sublist_of l2 l3)];
    [SMTPat (is_sublist_of l1 l3); SMTPat (is_sublist_of l2 l3)];
    [SMTPat (is_sublist_of l1 l3); SMTPat (is_sublist_of l1 l2)];
  ]]

val is_sublist_of_append_right
  (#t: Type)
  (l1 l2 l: list t)
: Lemma
  (is_sublist_of (l1 `List.Tot.append` l) (l2 `List.Tot.append` l) <==>
    is_sublist_of l1 l2)
  [SMTPat (is_sublist_of (l1 `List.Tot.append` l) (l2 `List.Tot.append` l))]

val is_sublist_of_append_left_intro
  (#t: Type)
  (l l1 l2: list t)
: Lemma
  (requires (is_sublist_of l1 l2))
  (ensures (is_sublist_of (l `List.Tot.append` l1) (l `List.Tot.append` l2)))
  [SMTPat (is_sublist_of (l `List.Tot.append` l1) (l `List.Tot.append` l2))]

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

val list_filter_is_sublist_of_intro
  (#t: Type)
  (f: t -> bool)
  (l: list t)
: Lemma
  (ensures (List.Tot.filter f l `is_sublist_of` l))
  (decreases l)
  [SMTPat (List.Tot.filter f l)]

let notp
  (#t: Type)
  (p: (t -> Tot bool))
  (x: t)
: Tot bool
= not (p x)

val is_sublist_of_suffix
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (ensures (l2 `is_sublist_of` (l1 `List.Tot.append` l2)))
  [SMTPat (l1 `List.Tot.append` l2)]

val is_sublist_of_prefix
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (ensures (l1 `is_sublist_of` (l1 `List.Tot.append` l2)))
  [SMTPat (l1 `List.Tot.append` l2)]

let cbor_map_pred (l: list (Cbor.raw_data_item & Cbor.raw_data_item)) : Tot prop =
  List.Tot.no_repeats_p (List.Tot.map fst l)

let cbor_map : Type0 = (l: list (Cbor.raw_data_item & Cbor.raw_data_item) { cbor_map_pred l })

val cbor_map_is_sublist_of
  (l1 l2: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (requires
    l1 `is_sublist_of` l2
  )
  (ensures cbor_map_pred l2 ==> cbor_map_pred l1)
  [SMTPat (l1 `is_sublist_of` l2)]

[@@erasable]
val map_group : Type0

val map_group_always_false : map_group

val map_group_end : map_group

val map_group_nop : map_group

val map_group_match_item (key value: typ) : map_group

let matches_map_group_entry
  (key value: typ)
  (x: (Cbor.raw_data_item & Cbor.raw_data_item))
: GTot bool
= key (fst x) && value (snd x)

val map_group_choice (m1 m2: map_group) : map_group

let map_group_zero_or_one (m: map_group) : map_group =
  map_group_choice m map_group_nop

val map_group_concat (m1 m2: map_group) : map_group

val map_group_concat_assoc (m1 m2 m3: map_group) : Lemma
  (map_group_concat m1 (map_group_concat m2 m3) == map_group_concat (map_group_concat m1 m2) m3)

val map_group_mk_cut (cut: typ) : map_group

val map_group_zero_or_more
  (m: map_group)
: map_group

let map_group_one_or_more (m: map_group) : map_group =
  map_group_concat m (map_group_zero_or_more m)

let map_group_match_item_for
  (k: Cbor.raw_data_item)
  (ty: typ)
: Tot map_group
= map_group_match_item (t_literal k) ty

[@@erasable]
noeq
type map_group_result =
| MapGroupFail
| MapGroupDet of cbor_map
| MapGroupNonDet

let map_group_result_prop (l: cbor_map) (r: map_group_result) : Tot prop =
  match r with
  | MapGroupDet m -> m `is_sublist_of` l
  | _ -> True

val apply_map_group_det (m: map_group) (l: cbor_map) : Pure map_group_result
  (requires True)
  (ensures fun r -> map_group_result_prop l r)

val apply_map_group_det_always_false (l: cbor_map) : Lemma
  (apply_map_group_det map_group_always_false l == MapGroupFail)

val apply_map_group_det_end (l: cbor_map) : Lemma
  (apply_map_group_det map_group_end l == (if Nil? l then MapGroupDet l else MapGroupFail))

val apply_map_group_det_nop (l: cbor_map) : Lemma
  (apply_map_group_det map_group_nop l == MapGroupDet l)

val apply_map_group_det_map_group_equiv (m1 m2: map_group) : Lemma
  (requires
    (forall l . ~ (MapGroupNonDet? (apply_map_group_det m1 l))) /\
    (forall l . apply_map_group_det m1 l == apply_map_group_det m2 l)
  )
  (ensures m1 == m2)

val apply_map_group_det_choice (m1 m2: map_group) (l: cbor_map) : Lemma
  (match apply_map_group_det m1 l with
  | MapGroupFail -> apply_map_group_det (m1 `map_group_choice` m2) l == apply_map_group_det m2 l
  | MapGroupDet l1 -> apply_map_group_det (m1 `map_group_choice` m2) l == MapGroupDet l1
  | _ -> True
  )

val apply_map_group_det_concat (m1 m2: map_group) (l: cbor_map) : Lemma
  (match apply_map_group_det m1 l with
  | MapGroupFail -> apply_map_group_det (m1 `map_group_concat` m2) l == MapGroupFail
  | MapGroupDet l1 -> apply_map_group_det (m1 `map_group_concat` m2) l == apply_map_group_det m2 l1
  | _ -> True)

val apply_map_group_det_match_item_for
  (k: Cbor.raw_data_item)
  (ty: typ)
  (l: cbor_map)
: Lemma
  (apply_map_group_det (map_group_match_item_for k ty) l == (match Cbor.list_ghost_assoc k l with
  | None ->  MapGroupFail
  | Some x ->
    if ty x
    then MapGroupDet (List.Tot.filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty))) l)
    else MapGroupFail
  ))

val apply_map_group_det_zero_or_more_match_item
  (key value: typ)
  (l: cbor_map)
: Lemma
  (apply_map_group_det (map_group_zero_or_more (map_group_match_item key value)) l ==
    MapGroupDet (List.Tot.filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value))) l)
  )

val matches_map_group (g: map_group) (m: cbor_map) : GTot bool

val matches_map_group_det (g: map_group) (m: cbor_map) : Lemma
  (match apply_map_group_det g m with
  | MapGroupFail -> ~ (matches_map_group g m)
  | MapGroupDet m' -> matches_map_group g m <==> m' == []
  | _ -> True)

let t_map (g: map_group) : typ =
  fun x -> match x with
  | Cbor.Map m -> 
    FStar.StrongExcludedMiddle.strong_excluded_middle (List.Tot.no_repeats_p (List.Tot.map fst m)) &&
    matches_map_group g m
  | _ -> false
