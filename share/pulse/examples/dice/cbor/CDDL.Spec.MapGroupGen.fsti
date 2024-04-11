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

[@@erasable]
val ghost_map (key value: Type0) : Type0

val apply_ghost_map (#key #value: Type0) (m: ghost_map key value) (k: key) : GTot (option value)

val ghost_map_ext (#key #value: Type0) (m1 m2: ghost_map key value) : Lemma
  (requires forall x . apply_ghost_map m1 x == apply_ghost_map m2 x)
  (ensures m1 == m2)

let ghost_map_mem (#key #value: Type) (kv: (key & value)) (f: ghost_map key value) : Tot prop =
  apply_ghost_map f (fst kv) == Some (snd kv)

val ghost_map_equiv (#key #value: Type) (f1 f2: ghost_map key value) : Lemma
  (requires (forall kv . ghost_map_mem kv f1 <==> ghost_map_mem kv f2))
  (ensures f1 == f2)

let ghost_map_defined (#key #value: Type) (k: key) (f: ghost_map key value) : Tot prop =
  Some? (apply_ghost_map f k)

let ghost_map_disjoint (#key #value1 #value2: Type) (f1: ghost_map key value1) (f2: ghost_map key value2) : Tot prop =
  (forall k . ~ (ghost_map_defined k f1 /\ ghost_map_defined k f2))

val ghost_map_empty (#key #value: Type) : Tot (ghost_map key value)

val apply_ghost_map_empty (#key #value: Type) (k: key) : Lemma
  (apply_ghost_map (ghost_map_empty #key #value) k == None)
  [SMTPat (apply_ghost_map (ghost_map_empty #key #value) k)]

val ghost_map_singleton (#key #value: Type) (k: key) (v: value) : Tot (ghost_map key value)

val apply_ghost_map_singleton (#key #value: Type) (k: key) (v: value) (k': key) : Lemma
  (let res = apply_ghost_map (ghost_map_singleton k v) k' in
    (k == k' ==> res == Some v) /\ ((~ (k == k')) ==> res == None))
  [SMTPat (apply_ghost_map (ghost_map_singleton k v) k')]

val ghost_map_union (#key #value: Type) (m1 m2: ghost_map key value) : Tot (ghost_map key value)

val apply_ghost_map_union (#key #value: Type) (m1 m2: ghost_map key value) (k: key) : Lemma
  (apply_ghost_map (ghost_map_union m1 m2) k == begin match apply_ghost_map m1 k with
    | Some v -> Some v
    | None -> apply_ghost_map m2 k
  end)
  [SMTPat (apply_ghost_map (ghost_map_union m1 m2) k)]

let ghost_map_disjoint_mem_union (#key #value: Type) (m1 m2: ghost_map key value) (xv: (key & value)) : Lemma
  (requires ghost_map_disjoint m1 m2)
  (ensures ghost_map_mem xv (m1 `ghost_map_union` m2) <==> ghost_map_mem xv m1 \/ ghost_map_mem xv m2)
= ()

let ghost_map_disjoint_mem_union' (#key #value: Type) (m1 m2: ghost_map key value) (_: squash (ghost_map_disjoint m1 m2)) : Lemma
  (ensures forall xv . ghost_map_mem xv (m1 `ghost_map_union` m2) <==> ghost_map_mem xv m1 \/ ghost_map_mem xv m2)
= ()

val ghost_map_disjoint_union (#key #value: Type) (m1 m2: ghost_map key value) : Lemma
  (requires ghost_map_disjoint m1 m2)
  (ensures m1 `ghost_map_union` m2 == m2 `ghost_map_union` m1)

let map_group_item_post
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (l': (ghost_map Cbor.raw_data_item Cbor.raw_data_item & list (Cbor.raw_data_item & Cbor.raw_data_item)))
: Tot prop
=
  (snd l' `is_sublist_of` l) /\
  (forall x . ~ (ghost_map_defined x (fst l') /\ List.Tot.memP x (List.Tot.map fst (snd l')))) /\
  (forall x . (ghost_map_mem x (fst l') \/ List.Tot.memP x (snd l')) <==> List.Tot.memP x l)

let cbor_map_pred (l: list (Cbor.raw_data_item & Cbor.raw_data_item)) : Tot prop =
  List.Tot.no_repeats_p (List.Tot.map fst l)

let cbor_map : Type0 = (l: list (Cbor.raw_data_item & Cbor.raw_data_item) { cbor_map_pred l })

val map_group_item_post_prop
  (l: cbor_map)
  (l': (ghost_map Cbor.raw_data_item Cbor.raw_data_item & list (Cbor.raw_data_item & Cbor.raw_data_item)))
: Lemma
  (requires (map_group_item_post l l'))
  (ensures (
    List.Tot.no_repeats_p (List.Tot.map fst (snd l')) /\
    (forall xy . ~ (ghost_map_mem xy (fst l') /\ List.Tot.memP xy (snd l'))) /\
    (forall x . Cbor.list_ghost_assoc x l == begin match apply_ghost_map (fst l') x with
    | Some y -> Some y
    | None -> Cbor.list_ghost_assoc x (snd l')
    end) /\
    (forall x . Cbor.list_ghost_assoc x l == begin match Cbor.list_ghost_assoc x (snd l') with
    | Some y -> Some y
    | None -> apply_ghost_map (fst l') x
    end)
  ))
  [SMTPat (map_group_item_post l l')]

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

val map_group_nop : map_group

val map_group_end : map_group

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

val map_group_mk_cut_gen
  (cut: (Cbor.raw_data_item & Cbor.raw_data_item) -> bool)
: map_group

let map_group_mk_cut (cut: typ) : map_group =
  map_group_mk_cut_gen (notp (FStar.Ghost.Pull.pull (matches_map_group_entry cut any)))

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

val ghost_map_filter
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m: ghost_map key value)
: ghost_map key value

val apply_ghost_map_filter
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m: ghost_map key value)
  (k: key)
: Lemma
  (apply_ghost_map (ghost_map_filter f m) k == begin match apply_ghost_map m k with
    | None -> None
    | Some v -> if f (k, v) then Some v else None
  end)
  [SMTPat (apply_ghost_map (ghost_map_filter f m) k)]

let ghost_map_filter_ext
  (#key #value: Type)
  (f1 f2: (key & value) -> GTot bool)
  (m: ghost_map key value)
: Lemma
  (requires forall x . f1 x == f2 x)
  (ensures ghost_map_filter f1 m == ghost_map_filter f2 m)
= ghost_map_equiv (ghost_map_filter f1 m) (ghost_map_filter f2 m)

val ghost_map_of_list
  (#key #value: Type)
  (l: list (key & value))
: ghost_map key value

val apply_ghost_map_of_list
  (#key #value: Type)
  (l: list (key & value))
  (k: key)
: Lemma
  (apply_ghost_map (ghost_map_of_list l) k == Cbor.list_ghost_assoc k l)
  [SMTPat (apply_ghost_map (ghost_map_of_list l) k)]

val ghost_map_of_list_singleton
  (#key #value: Type)
  (kv: (key & value))
: Lemma
  (ghost_map_of_list [kv] == ghost_map_singleton (fst kv) (snd kv))
  [SMTPat (ghost_map_of_list [kv])]

val ghost_map_of_list_append
  (#key #value: Type)
  (l1 l2: list (key & value))
: Lemma
  (ghost_map_of_list (List.Tot.append l1 l2) == ghost_map_of_list l1 `ghost_map_union` ghost_map_of_list l2)

val ghost_map_of_list_mem_gen
  (#key #value: Type)
  (l: list (key & value))
  (prf: squash (List.Tot.no_repeats_p (List.Tot.map fst l)))
  (x: (key & value))
: Lemma
  (ghost_map_mem x (ghost_map_of_list l) <==> List.Tot.memP x l)

let ghost_map_of_list_mem
  (l: cbor_map)
  (x: (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (ghost_map_mem x (ghost_map_of_list l) <==> List.Tot.memP x l)
= ghost_map_of_list_mem_gen l () x

val ghost_map_filter_of_list
  (f: _ -> bool)
  (l: cbor_map)
: Lemma
  (ghost_map_filter f (ghost_map_of_list l) == ghost_map_of_list (List.Tot.filter f l))

val map_group_zero_or_more_zero_or_one_eq
  (m: map_group)
: Lemma
  (map_group_zero_or_more (map_group_zero_or_one m) == map_group_zero_or_more m)

[@@erasable]
noeq
type map_group_result =
| MapGroupFail
| MapGroupDet:
  (consumed: ghost_map Cbor.raw_data_item Cbor.raw_data_item) ->
  (remaining: cbor_map) ->
  map_group_result
| MapGroupNonDet

let map_group_result_prop (l: cbor_map) (r: map_group_result) : Tot prop =
  match r with
  | MapGroupDet c m -> map_group_item_post l (c, m)
  | _ -> True

val apply_map_group_det (m: map_group) (l: cbor_map) : Pure map_group_result
  (requires True)
  (ensures fun r -> map_group_result_prop l r)

val apply_map_group_det_always_false (l: cbor_map) : Lemma
  (apply_map_group_det map_group_always_false l == MapGroupFail)
  [SMTPat (apply_map_group_det map_group_always_false l)]

val apply_map_group_det_nop (l: cbor_map) : Lemma
  (apply_map_group_det map_group_nop l == MapGroupDet ghost_map_empty l)
  [SMTPat (apply_map_group_det map_group_nop l)]

val apply_map_group_det_end (l: cbor_map) : Lemma
  (apply_map_group_det map_group_end l == (if Nil? l then MapGroupDet ghost_map_empty l else MapGroupFail))
  [SMTPat (apply_map_group_det map_group_end l)]

val apply_map_group_det_map_group_equiv (m1 m2: map_group) : Lemma
  (requires
    (forall l . ~ (MapGroupNonDet? (apply_map_group_det m1 l))) /\
    (forall l . apply_map_group_det m1 l == apply_map_group_det m2 l)
  )
  (ensures m1 == m2)

let apply_map_group_det_map_group_equiv0 (m1 m2: map_group)
  (prf1: (l: cbor_map) -> Lemma
    (~ (MapGroupNonDet? (apply_map_group_det m1 l)))
  )
  (prf2: (l: cbor_map) -> Lemma
    (apply_map_group_det m1 l == apply_map_group_det m2 l)
  )
: Lemma
  (ensures m1 == m2)
= Classical.forall_intro prf1;
  Classical.forall_intro prf2;
  apply_map_group_det_map_group_equiv m1 m2

val apply_map_group_det_choice (m1 m2: map_group) (l: cbor_map) : Lemma
  (match apply_map_group_det m1 l with
  | MapGroupFail -> apply_map_group_det (m1 `map_group_choice` m2) l == apply_map_group_det m2 l
  | MapGroupDet c1 l1 -> apply_map_group_det (m1 `map_group_choice` m2) l == MapGroupDet c1 l1
  | _ -> True
  )
  [SMTPat (apply_map_group_det (map_group_choice m1 m2) l)]

val apply_map_group_det_concat (m1 m2: map_group) (l: cbor_map) : Lemma
  (match apply_map_group_det m1 l with
  | MapGroupFail -> apply_map_group_det (m1 `map_group_concat` m2) l == MapGroupFail
  | MapGroupDet c1 l1 ->
    apply_map_group_det (m1 `map_group_concat` m2) l == begin match apply_map_group_det m2 l1 with
    | MapGroupDet c2 l2 -> MapGroupDet (c1 `ghost_map_union` c2) l2
    | res -> res
    end
  | _ -> True)
  [SMTPat (apply_map_group_det (map_group_concat m1 m2) l)]

val apply_map_group_det_mk_cut_gen
  (cut: (Cbor.raw_data_item & Cbor.raw_data_item) -> bool)
  (l: cbor_map)
: Lemma
  (apply_map_group_det (map_group_mk_cut_gen cut) l == (
    if List.Tot.for_all cut l
    then MapGroupDet ghost_map_empty l
    else MapGroupFail
  ))
  [SMTPat (apply_map_group_det (map_group_mk_cut_gen cut) l)]

let apply_map_group_det_mk_cut (cut: typ) (l: cbor_map) : Lemma
  (apply_map_group_det (map_group_mk_cut cut) l == (
    if List.Tot.for_all (notp (FStar.Ghost.Pull.pull (matches_map_group_entry cut any))) l
    then MapGroupDet ghost_map_empty l
    else MapGroupFail
  ))
= ()

val apply_map_group_det_match_item_for
  (k: Cbor.raw_data_item)
  (ty: typ)
  (l: cbor_map)
: Lemma
  (apply_map_group_det (map_group_match_item_for k ty) l == (match Cbor.list_ghost_assoc k l with
  | None ->  MapGroupFail
  | Some x ->
    if ty x
    then MapGroupDet (ghost_map_singleton k x) (List.Tot.filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty))) l)
    else MapGroupFail
  ))
  [SMTPat (apply_map_group_det (map_group_match_item_for k ty) l)]

val map_group_filter
  (f: (Cbor.raw_data_item & Cbor.raw_data_item) -> bool)
: map_group

val apply_map_group_det_filter
  (f: (Cbor.raw_data_item & Cbor.raw_data_item) -> bool)
  (l: cbor_map)
: Lemma
  (apply_map_group_det (map_group_filter f) l ==
    MapGroupDet (ghost_map_filter (notp f) (ghost_map_of_list l)) (List.Tot.filter f l)
  )
  [SMTPat (apply_map_group_det (map_group_filter f) l)]

let andp (#t: Type) (p1 p2: t -> bool) (x: t) : bool =
  p1 x && p2 x

let rec list_filter_filter (#t: Type) (p1 p2: t -> bool) (l: list t) : Lemma
  (ensures (List.Tot.filter p2 (List.Tot.filter p1 l) == List.Tot.filter (andp p1 p2) l))
  (decreases l)
//  [SMTPat (List.Tot.filter p2 (List.Tot.filter p1 l))]
= match l with
  | [] -> ()
  | a :: q -> list_filter_filter p1 p2 q

val map_group_filter_filter (p1 p2: (Cbor.raw_data_item & Cbor.raw_data_item) -> bool) : Lemma
  (map_group_filter p1 `map_group_concat` map_group_filter p2 == map_group_filter (andp p1 p2))
  [SMTPat (map_group_filter p1 `map_group_concat` map_group_filter p2)]

let rec list_filter_ext (#t: Type) (p1 p2: t -> bool) (l: list t) : Lemma
  (requires forall (x: t) . List.Tot.memP x l ==> p1 x == p2 x)
  (ensures List.Tot.filter p1 l == List.Tot.filter p2 l)
  (decreases l)
= match l with
  | [] -> ()
  | a :: q -> list_filter_ext p1 p2 q

let map_group_filter_ext (p1 p2: _ -> bool) : Lemma
  (requires forall x . p1 x == p2 x)
  (ensures map_group_filter p1 == map_group_filter p2)
= Classical.forall_intro (Classical.move_requires (list_filter_ext p1 p2));
  Classical.forall_intro (Classical.move_requires (ghost_map_filter_ext (notp p1) (notp p2)));
  apply_map_group_det_map_group_equiv
    (map_group_filter p1)
    (map_group_filter p2)

let list_filter_filter_comm (#t: Type) (p1 p2: t -> bool) (l: list t) : Lemma
  (List.Tot.filter p2 (List.Tot.filter p1 l) == List.Tot.filter p1 (List.Tot.filter p2 l))
//  [SMTPat (List.Tot.filter p2 (List.Tot.filter p1 l))]
= list_filter_filter p1 p2 l;
  list_filter_filter p2 p1 l;
  list_filter_ext (andp p1 p2) (andp p2 p1) l

let list_filter_implies_1 (#t: Type) (p1 p2: t -> bool) (l: list t) : Lemma
  (requires (forall (x: t) . (List.Tot.memP x l /\ p1 x) ==> p2 x))
  (ensures List.Tot.filter p2 (List.Tot.filter p1 l) == List.Tot.filter p1 l)
= list_filter_filter p1 p2 l;
  list_filter_ext p1 (andp p1 p2) l

let list_filter_implies_2 (#t: Type) (p1 p2: t -> bool) (l: list t) : Lemma
  (requires (forall (x: t) . (List.Tot.memP x l /\ p1 x) ==> p2 x))
  (ensures List.Tot.filter p1 (List.Tot.filter p2 l) == List.Tot.filter p1 l)
= list_filter_filter_comm p1 p2 l;
  list_filter_implies_1 p1 p2 l

val map_group_zero_or_one_match_item_filter (key value: typ) (p: (Cbor.raw_data_item & Cbor.raw_data_item) -> bool) : Lemma
  (requires (
    forall x . p x ==> notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value)) x
  ))
  (ensures
    map_group_zero_or_one (map_group_match_item key value) `map_group_concat` map_group_filter p == map_group_filter p
  )
  [SMTPat (map_group_zero_or_one (map_group_match_item key value) `map_group_concat` map_group_filter p)]

val map_group_zero_or_more_match_item_filter (key value: typ) : Lemma
  (map_group_zero_or_more (map_group_match_item key value) ==
    map_group_filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value)))
  )
  [SMTPat (map_group_zero_or_more (map_group_match_item key value))]

let map_group_zero_or_more_match_item_choice_left
  (key1 key2 value: typ)
: Lemma
  (map_group_zero_or_more (map_group_match_item (key1 `t_choice` key2) value) ==
    map_group_zero_or_more (map_group_match_item key1 value) `map_group_concat`
    map_group_zero_or_more (map_group_match_item key2 value)
  )
= map_group_filter_ext
    (notp (FStar.Ghost.Pull.pull (matches_map_group_entry (key1 `t_choice` key2) value)))
    (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key1 value)) `andp`
      notp (FStar.Ghost.Pull.pull (matches_map_group_entry key2 value))
    )

val map_group_zero_or_more_map_group_match_item_for
  (key: Cbor.raw_data_item)
  (value: typ)
: Lemma
  (map_group_zero_or_more (map_group_match_item_for key value) ==
    map_group_zero_or_one (map_group_match_item_for key value)
  )

val matches_map_group (g: map_group) (m: cbor_map) : GTot bool

val matches_map_group_det (g: map_group) (m: cbor_map) : Lemma
  (match apply_map_group_det g m with
  | MapGroupFail -> ~ (matches_map_group g m)
  | MapGroupDet _ m' -> matches_map_group g m <==> m' == []
  | _ -> True)

let t_map (g: map_group) : typ =
  fun x -> match x with
  | Cbor.Map m -> 
    FStar.StrongExcludedMiddle.strong_excluded_middle (List.Tot.no_repeats_p (List.Tot.map fst m)) &&
    matches_map_group g m
  | _ -> false
