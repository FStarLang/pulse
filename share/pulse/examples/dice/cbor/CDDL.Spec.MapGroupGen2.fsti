module CDDL.Spec.MapGroupGen2
include CDDL.Spec.Base
module Cbor = CBOR.Spec
module U8 = FStar.UInt8
module U64 = FStar.UInt64

let notp_g
  (#t: Type)
  (p: (t -> GTot bool))
  (x: t)
: GTot bool
= not (p x)

let notp
  (#t: Type)
  (p: (t -> Tot bool))
  (x: t)
: Tot bool
= not (p x)

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

let ghost_map_defined_alt
  (#key #value: Type) (k: key) (f: ghost_map key value)
: Lemma
  (ghost_map_defined k f <==> (exists v . ghost_map_mem (k, v) f))
  [SMTPat (ghost_map_defined k f)]
= match apply_ghost_map f k with
  | None -> ()
  | Some _ -> ()

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

let ghost_map_union_empty_l (#key #value: Type) (m: ghost_map key value) : Lemma
  (ghost_map_union ghost_map_empty m == m)
  [SMTPat (ghost_map_union ghost_map_empty m)]
= ghost_map_ext (ghost_map_union ghost_map_empty m) m

let ghost_map_union_empty_r (#key #value: Type) (m: ghost_map key value) : Lemma
  (ghost_map_union m ghost_map_empty == m)
  [SMTPat (ghost_map_union m ghost_map_empty)]
= ghost_map_ext (ghost_map_union m ghost_map_empty) m

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

val ghost_map_length (#key #value: Type) (m: ghost_map key value) : GTot nat

val ghost_map_length_empty (key value: Type) : Lemma
  (ghost_map_length (ghost_map_empty #key #value) == 0)
  [SMTPat (ghost_map_length (ghost_map_empty #key #value))]

val ghost_map_length_singleton (#key #value: Type) (k: key) (v: value) : Lemma
  (ghost_map_length (ghost_map_singleton k v) == 1)
  [SMTPat (ghost_map_length (ghost_map_singleton k v))]

val ghost_map_length_disjoint_union (#key #value: Type) (m1 m2: ghost_map key value) : Lemma
  (requires ghost_map_disjoint m1 m2)
  (ensures (ghost_map_length (ghost_map_union m1 m2) == ghost_map_length m1 + ghost_map_length m2))
  [SMTPat (ghost_map_length (ghost_map_union m1 m2))]

let map_group_item_post
  (l: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
  (l': (ghost_map Cbor.raw_data_item Cbor.raw_data_item & ghost_map Cbor.raw_data_item Cbor.raw_data_item))
: Tot prop
=
  fst l' `ghost_map_disjoint` snd l' /\
  (fst l' `ghost_map_union` snd l') == l

[@@erasable]
val map_group : Type0

val map_group_always_false : map_group

val map_group_nop : map_group

val map_group_end : map_group

val map_group_match_item (cut: bool) (key value: typ) : map_group

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

val map_group_zero_or_more
  (m: map_group)
: map_group

let map_group_one_or_more (m: map_group) : map_group =
  map_group_concat m (map_group_zero_or_more m)

let map_group_match_item_for
  (cut: bool)
  (k: Cbor.raw_data_item)
  (ty: typ)
: Tot map_group
= map_group_match_item cut (t_literal k) ty

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

let ghost_map_mem_filter
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m: ghost_map key value)
  (x: (key & value))
: Lemma
  (ghost_map_mem x (ghost_map_filter f m) <==> ghost_map_mem x m /\ f x)
= ()

let ghost_map_filter_for_all
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m: ghost_map key value)
: Lemma
  (requires forall x . ghost_map_mem x m ==> f x)
  (ensures ghost_map_filter f m == m)
= ghost_map_equiv (ghost_map_filter f m) m

let ghost_map_filter_ext
  (#key #value: Type)
  (f1 f2: (key & value) -> GTot bool)
  (m: ghost_map key value)
: Lemma
  (requires forall x . f1 x == f2 x)
  (ensures ghost_map_filter f1 m == ghost_map_filter f2 m)
= ghost_map_equiv (ghost_map_filter f1 m) (ghost_map_filter f2 m)

let ghost_map_disjoint_union_filter
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m1 m2: ghost_map key value)
: Lemma
  (requires ghost_map_disjoint m1 m2)
  (ensures (ghost_map_filter f (ghost_map_union m1 m2) == ghost_map_filter f m1 `ghost_map_union` ghost_map_filter f m2))
= ghost_map_ext
    (ghost_map_filter f (ghost_map_union m1 m2))
    (ghost_map_filter f m1 `ghost_map_union` ghost_map_filter f m2)

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

val ghost_map_of_list_mem
  (#key #value: Type)
  (l: list (key & value) { List.Tot.no_repeats_p (List.Tot.map fst l) })
  (x: (key & value))
: Lemma
  (ghost_map_mem x (ghost_map_of_list l) <==> List.Tot.memP x l)

val ghost_map_filter_of_list
  (#key #value: Type)
  (f: _ -> bool)
  (l: list (key & value) { List.Tot.no_repeats_p (List.Tot.map fst l) })
: Lemma
  (ghost_map_filter f (ghost_map_of_list l) == ghost_map_of_list (List.Tot.filter f l))

val ghost_map_length_of_list
  (#key #value: Type)
  (l: list (key & value))
: Lemma
  (requires List.Tot.no_repeats_p (List.Tot.map fst l))
  (ensures ghost_map_length (ghost_map_of_list l) == List.Tot.length l)
  [SMTPat (ghost_map_length (ghost_map_of_list l))]

val map_group_zero_or_more_zero_or_one_eq
  (m: map_group)
: Lemma
  (map_group_zero_or_more (map_group_zero_or_one m) == map_group_zero_or_more m)

[@@erasable]
noeq
type map_group_result =
| MapGroupCutFail
| MapGroupFail
| MapGroupDet:
  (consumed: ghost_map Cbor.raw_data_item Cbor.raw_data_item) ->
  (remaining: ghost_map Cbor.raw_data_item Cbor.raw_data_item) ->
  map_group_result
| MapGroupNonDet

let map_group_result_prop (l: ghost_map Cbor.raw_data_item Cbor.raw_data_item) (r: map_group_result) : Tot prop =
  match r with
  | MapGroupDet c m -> map_group_item_post l (c, m)
  | _ -> True

val apply_map_group_det (m: map_group) (l: ghost_map Cbor.raw_data_item Cbor.raw_data_item) : Pure map_group_result
  (requires True)
  (ensures fun r -> map_group_result_prop l r)

val apply_map_group_det_always_false (l: ghost_map Cbor.raw_data_item Cbor.raw_data_item) : Lemma
  (apply_map_group_det map_group_always_false l == MapGroupFail)
  [SMTPat (apply_map_group_det map_group_always_false l)]

val apply_map_group_det_nop (l: ghost_map Cbor.raw_data_item Cbor.raw_data_item) : Lemma
  (apply_map_group_det map_group_nop l == MapGroupDet ghost_map_empty l)
  [SMTPat (apply_map_group_det map_group_nop l)]

val apply_map_group_det_end (l: ghost_map Cbor.raw_data_item Cbor.raw_data_item) : Lemma
  (apply_map_group_det map_group_end ghost_map_empty == MapGroupDet ghost_map_empty l /\
    ((~ (l == ghost_map_empty)) ==> apply_map_group_det map_group_end l == MapGroupFail)
  )
  [SMTPat (apply_map_group_det map_group_end l)]

val apply_map_group_det_map_group_equiv (m1 m2: map_group) : Lemma
  (requires
    (forall l . ~ (MapGroupNonDet? (apply_map_group_det m1 l))) /\
    (forall l . apply_map_group_det m1 l == apply_map_group_det m2 l)
  )
  (ensures m1 == m2)

let apply_map_group_det_map_group_equiv0 (m1 m2: map_group)
  (prf1: (l: ghost_map Cbor.raw_data_item Cbor.raw_data_item) -> Lemma
    (~ (MapGroupNonDet? (apply_map_group_det m1 l)))
  )
  (prf2: (l: ghost_map Cbor.raw_data_item Cbor.raw_data_item) -> Lemma
    (apply_map_group_det m1 l == apply_map_group_det m2 l)
  )
: Lemma
  (ensures m1 == m2)
= Classical.forall_intro prf1;
  Classical.forall_intro prf2;
  apply_map_group_det_map_group_equiv m1 m2

val apply_map_group_det_choice (m1 m2: map_group) (l: ghost_map Cbor.raw_data_item Cbor.raw_data_item) : Lemma
  (match apply_map_group_det m1 l with
  | MapGroupCutFail -> apply_map_group_det (m1 `map_group_choice` m2) l == MapGroupCutFail
  | MapGroupFail -> apply_map_group_det (m1 `map_group_choice` m2) l == apply_map_group_det m2 l
  | MapGroupDet c1 l1 -> apply_map_group_det (m1 `map_group_choice` m2) l == MapGroupDet c1 l1
  | _ -> True
  )
  [SMTPat (apply_map_group_det (map_group_choice m1 m2) l)]

val apply_map_group_det_concat (m1 m2: map_group) (l: ghost_map Cbor.raw_data_item Cbor.raw_data_item) : Lemma
  (match apply_map_group_det m1 l with
  | MapGroupCutFail -> apply_map_group_det (m1 `map_group_concat` m2) l == MapGroupCutFail
  | MapGroupFail -> apply_map_group_det (m1 `map_group_concat` m2) l == MapGroupFail
  | MapGroupDet c1 l1 ->
    apply_map_group_det (m1 `map_group_concat` m2) l == begin match apply_map_group_det m2 l1 with
    | MapGroupDet c2 l2 -> MapGroupDet (c1 `ghost_map_union` c2) l2
    | res -> res
    end
  | _ -> True)
  [SMTPat (apply_map_group_det (map_group_concat m1 m2) l)]

val apply_map_group_det_match_item_for
  (cut: bool)
  (k: Cbor.raw_data_item)
  (ty: typ)
  (l: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Lemma
  (apply_map_group_det (map_group_match_item_for cut k ty) l == (match apply_ghost_map l k with
  | None ->  MapGroupFail
  | Some x ->
    if ty x
    then MapGroupDet (ghost_map_singleton k x) (ghost_map_filter (notp_g (matches_map_group_entry (t_literal k) ty)) l)
    else if cut
    then MapGroupCutFail
    else MapGroupFail
  ))
  [SMTPat (apply_map_group_det (map_group_match_item_for cut k ty) l)]

val map_group_filter
  (f: (Cbor.raw_data_item & Cbor.raw_data_item) -> GTot bool)
: map_group

val apply_map_group_det_filter
  (f: (Cbor.raw_data_item & Cbor.raw_data_item) -> GTot bool)
  (l: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Lemma
  (apply_map_group_det (map_group_filter f) l ==
    MapGroupDet (ghost_map_filter (notp_g f) l) (ghost_map_filter f l)
  )
  [SMTPat (apply_map_group_det (map_group_filter f) l)]

let andp_g (#t: Type) (p1 p2: t -> GTot bool) (x: t) : GTot bool =
  p1 x && p2 x

let andp (#t: Type) (p1 p2: t -> Tot bool) (x: t) : Tot bool =
  p1 x && p2 x

let rec list_filter_filter (#t: Type) (p1 p2: t -> bool) (l: list t) : Lemma
  (ensures (List.Tot.filter p2 (List.Tot.filter p1 l) == List.Tot.filter (andp p1 p2) l))
  (decreases l)
//  [SMTPat (List.Tot.filter p2 (List.Tot.filter p1 l))]
= match l with
  | [] -> ()
  | a :: q -> list_filter_filter p1 p2 q

let ghost_map_filter_filter
  (#key #value: Type)
  (p1 p2: (key & value) -> GTot bool)
  (f: ghost_map key value)
: Lemma
  (ghost_map_filter p2 (ghost_map_filter p1 f) == ghost_map_filter (p1 `andp_g` p2) f)
= ghost_map_equiv
    (ghost_map_filter p2 (ghost_map_filter p1 f))
    (ghost_map_filter (p1 `andp_g` p2) f)

let ghost_map_filter_implies
  (#key #value: Type)
  (p1 p2: (key & value) -> GTot bool)
  (f: ghost_map key value)
: Lemma
  (requires (forall kv . p1 kv ==> p2 kv))
  (ensures (ghost_map_filter p2 (ghost_map_filter p1 f) == ghost_map_filter p1 f))
= ghost_map_filter_filter p1 p2 f;
  ghost_map_filter_ext p1 (p1 `andp_g` p2) f

val map_group_filter_filter (p1 p2: (Cbor.raw_data_item & Cbor.raw_data_item) -> GTot bool) : Lemma
  (map_group_filter p1 `map_group_concat` map_group_filter p2 == map_group_filter (andp_g p1 p2))
  [SMTPat (map_group_filter p1 `map_group_concat` map_group_filter p2)]

let rec list_filter_ext (#t: Type) (p1 p2: t -> bool) (l: list t) : Lemma
  (requires forall (x: t) . List.Tot.memP x l ==> p1 x == p2 x)
  (ensures List.Tot.filter p1 l == List.Tot.filter p2 l)
  (decreases l)
= match l with
  | [] -> ()
  | a :: q -> list_filter_ext p1 p2 q

let map_group_filter_ext (p1 p2: _ -> GTot bool) : Lemma
  (requires forall x . p1 x == p2 x)
  (ensures map_group_filter p1 == map_group_filter p2)
=
  Classical.forall_intro (Classical.move_requires (ghost_map_filter_ext (notp_g p1) (notp_g p2)));
  Classical.forall_intro (Classical.move_requires (ghost_map_filter_ext p1 p2));
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
    forall x . p x ==> notp_g (matches_map_group_entry key value) x
  ))
  (ensures
    map_group_zero_or_one (map_group_match_item false key value) `map_group_concat` map_group_filter p == map_group_filter p
  )
  [SMTPat (map_group_zero_or_one (map_group_match_item false key value) `map_group_concat` map_group_filter p)]

val map_group_zero_or_more_match_item_filter (key value: typ) : Lemma
  (map_group_zero_or_more (map_group_match_item false key value) ==
    map_group_filter (notp_g (matches_map_group_entry key value))
  )
  [SMTPat (map_group_zero_or_more (map_group_match_item false key value))]

let map_group_zero_or_more_match_item_choice_left
  (key1 key2 value: typ)
: Lemma
  (map_group_zero_or_more (map_group_match_item false (key1 `t_choice` key2) value) ==
    map_group_zero_or_more (map_group_match_item false key1 value) `map_group_concat`
    map_group_zero_or_more (map_group_match_item false key2 value)
  )
= map_group_filter_ext
    (notp_g (matches_map_group_entry (key1 `t_choice` key2) value))
    (notp_g (matches_map_group_entry key1 value) `andp_g`
      notp_g (matches_map_group_entry key2 value)
    )

val map_group_zero_or_more_map_group_match_item_for
  (key: Cbor.raw_data_item)
  (value: typ)
: Lemma
  (map_group_zero_or_more (map_group_match_item_for false key value) ==
    map_group_zero_or_one (map_group_match_item_for false key value)
  )

val matches_map_group (g: map_group) (m: list (Cbor.raw_data_item & Cbor.raw_data_item)) : GTot bool

val matches_map_group_det (g: map_group) (m: list (Cbor.raw_data_item & Cbor.raw_data_item)) : Lemma
  (match apply_map_group_det g (ghost_map_of_list m) with
  | MapGroupCutFail
  | MapGroupFail -> ~ (matches_map_group g m)
  | MapGroupDet _ m' -> matches_map_group g m <==> m' == ghost_map_empty
  | _ -> True)
  [SMTPat (matches_map_group g m)]

val t_map (g: map_group) : typ

val t_map_eq
  (g: map_group)
  (x: Cbor.raw_data_item)
: Lemma
  (t_map g x == true <==> begin match x with
    | Cbor.Map m ->
      List.Tot.no_repeats_p (List.Tot.map fst m) /\
      matches_map_group g m
    | _ -> False
  end)
  [SMTPat (t_map g x)]


let det_map_group = (m: map_group { forall l . ~ (MapGroupNonDet? (apply_map_group_det m l)) })

let map_group_parser_spec_arg
  (source: det_map_group)
  (#target: Type0)
  (target_size: target -> nat)
: Tot Type0
= (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { // list needed because I need to preserve the order of elements when parsing a table
    List.Tot.no_repeats_p (List.Tot.map fst x) /\
    begin match apply_map_group_det source (ghost_map_of_list x) with
    | MapGroupDet _ rem -> rem == ghost_map_empty
    | _ -> False
    end
  })

let map_group_parser_spec_ret
  (source: det_map_group)
  (#target: Type0)
  (target_size: target -> nat)
  (x: map_group_parser_spec_arg source target_size)
: Tot Type0
= (y: target { 
    target_size y == List.Tot.length x
  })

let map_group_parser_spec
  (source: det_map_group)
  (#target: Type0)
  (target_size: target -> nat)
: Type0
= (x: map_group_parser_spec_arg source target_size) -> GTot (map_group_parser_spec_ret source target_size x)

let map_group_serializer_spec
  (#source: det_map_group)
  (#target: Type0)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source target_size)
  (target_guard: (Cbor.raw_data_item & Cbor.raw_data_item) -> Tot prop) // to take cuts into account. This implies that it is the responsibility of the designer of the target type to make sure entries violating cuts are not introduced.
: Type0
= (x: target) -> GTot (y: list (Cbor.raw_data_item & Cbor.raw_data_item) {
    List.Tot.no_repeats_p (List.Tot.map fst y) /\
    matches_map_group source y /\
    p y == x /\
    (forall z . List.Tot.memP z y ==> target_guard z)
  })

let map_group_target_serializable
  (#target: Type0)
  (target_size: target -> nat)
: Tot Type0
= (x: target { target_size x < pow2 64 })

let parser_spec_map_group
  (#source: det_map_group)
  (#target: Type0)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source target_size)
: Tot (parser_spec (t_map source) (map_group_target_serializable target_size))
= fun x ->
    let Cbor.Map a = x in
    let res = p a in
    res

let serializer_spec_map_group
  (#source: det_map_group)
  (#target: Type0)
  (#target_size: target -> nat)
  (#p: map_group_parser_spec source target_size)
  (#target_guard: (Cbor.raw_data_item & Cbor.raw_data_item) -> Tot prop)
  (s: map_group_serializer_spec p target_guard)
: Tot (serializer_spec (parser_spec_map_group p))
= fun x -> Cbor.Map (s x)

let map_group_parser_spec_bij
  (#source: det_map_group)
  (#target1: Type0)
  (#target_size1: target1 -> nat)
  (f: map_group_parser_spec source target_size1)
  (#target2: Type0)
  (target_size2: target2 -> nat)
  (bij: bijection target1 target2 {
    forall x2 . target_size2 x2 == target_size1 (bij.bij_to_from x2)
  })
: Tot (map_group_parser_spec source target_size2)
= fun x -> bij.bij_from_to (f x)

let map_group_serializer_spec_bij
  (#source: det_map_group)
  (#target1: Type0)
  (#target_size1: target1 -> nat)
  (#f: map_group_parser_spec source target_size1)
  (#target_guard: (Cbor.raw_data_item & Cbor.raw_data_item) -> Tot prop)
  (s: map_group_serializer_spec f target_guard)
  (#target2: Type0)
  (target_size2: target2 -> nat)
  (bij: bijection target1 target2 {
    forall x2 . target_size2 x2 == target_size1 (bij.bij_to_from x2)
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_bij f target_size2 bij) target_guard)
= fun x -> s (bij.bij_to_from x)

let map_group_parser_spec_match_item_for
  (cut: bool)
  (k: Cbor.raw_data_item)
  (#ty: typ)
  (#target: Type)
  (p: parser_spec ty target)
  (target_size: target -> nat {
    forall x . target_size x == 1
  })
: Tot (map_group_parser_spec (map_group_match_item_for cut k ty) target_size)
= fun x ->
  ghost_map_length_of_list x;
  let Some v = Cbor.list_ghost_assoc k x in
  p v

let map_group_serializer_spec_match_item_for
  (#cut: bool)
  (#k: Cbor.raw_data_item)
  (#ty: typ)
  (#target: Type)
  (#p: parser_spec ty target)
  (s: serializer_spec p)
  (target_size: target -> nat {
    forall x . target_size x == 1
  })
  (target_guard: (Cbor.raw_data_item & Cbor.raw_data_item) -> Tot prop {
    forall v . ty v ==> target_guard (k, v)
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_match_item_for cut k p target_size) target_guard)
= fun x ->
  let v = s x in
  let res = [k, v] in
  let mres = ghost_map_of_list res in
  ghost_map_equiv mres (ghost_map_singleton k v);
  let MapGroupDet _ rem = apply_map_group_det (map_group_match_item_for cut k ty) mres in
  ghost_map_equiv rem ghost_map_empty;
  res

let map_group_parser_spec_concat_shrinkable
  (g: map_group)
: Tot prop
= forall x . match apply_map_group_det g x with
  | MapGroupDet consumed rem ->
    forall rem1 rem2 . (
      rem1 `ghost_map_disjoint` rem2 /\
      rem1 `ghost_map_union` rem2 == rem
    ) ==>
    apply_map_group_det g (consumed `ghost_map_union` rem1) == MapGroupDet consumed rem1
  | MapGroupFail -> // necessary for compatibility with `//` . NOTE: This does not hold for things like (?((k1=>t1)(k2=>t2)))(k1=>t'), so we will need some independence conditions, see below.
    forall x1 x2 . x == x1 `ghost_map_union` x2 ==>
    (MapGroupFail? (apply_map_group_det g x1) \/ MapGroupCutFail? (apply_map_group_det g x1))
  | _ -> True

#restart-solver
let map_group_parser_spec_concat_shrinkable_intro
  (g: map_group)
  (prf: (x: _) -> (rem1: _) -> (rem2: _) -> Lemma
    (requires (
      match apply_map_group_det g x with
      | MapGroupDet consumed rem ->
        rem1 `ghost_map_disjoint` rem2 /\
        rem1 `ghost_map_union` rem2 == rem /\
        consumed `ghost_map_disjoint` rem1 /\
        consumed `ghost_map_disjoint` rem2
      | _ -> False
    ))
    (ensures (
      match apply_map_group_det g x with
      | MapGroupDet consumed _ ->
        apply_map_group_det g (consumed `ghost_map_union` rem1) == MapGroupDet consumed rem1
      | _ -> True
    ))
  )
  (prf2: (x1: _) -> (x2: _) -> Lemma
    (requires MapGroupFail? (apply_map_group_det g (x1 `ghost_map_union` x2)))
    (ensures MapGroupFail? (apply_map_group_det g x1) \/ MapGroupCutFail? (apply_map_group_det g x1))
  )
(*
  (prf3: (x1: _) -> (x2: _) -> Lemma
    (requires MapGroupCutFail? (apply_map_group_det g x1))
    (ensures MapGroupCutFail? (apply_map_group_det g (x1 `ghost_map_union` x2)))
  )
*)  
: Lemma
  (map_group_parser_spec_concat_shrinkable g)
= Classical.forall_intro_3 (fun rem1 rem2 -> Classical.move_requires (prf rem1 rem2));
  Classical.forall_intro_2 (fun x1 -> Classical.move_requires (prf2 x1));
//  Classical.forall_intro_2 (fun x1 -> Classical.move_requires (prf3 x1));
  ()

let map_group_parser_spec_concat_shrinkable_match_item_for
  (cut: bool)
  (k: Cbor.raw_data_item)
  (ty: typ)
: Lemma
  (map_group_parser_spec_concat_shrinkable
    (map_group_match_item_for cut k ty)
  )
= map_group_parser_spec_concat_shrinkable_intro (map_group_match_item_for cut k ty) (fun x rem1 rem2 ->
    let MapGroupDet consumed rem = apply_map_group_det (map_group_match_item_for cut k ty) x in
    let Some v = apply_ghost_map x k in
    assert (consumed == ghost_map_singleton k v);
    assert (apply_ghost_map consumed k == Some v);
    assert (apply_ghost_map (consumed `ghost_map_union` rem1) k == Some v);
    ghost_map_disjoint_union_filter (notp_g (matches_map_group_entry (t_literal k) ty)) rem1 rem2;
    ghost_map_disjoint_union_filter (notp_g (matches_map_group_entry (t_literal k) ty)) consumed rem1;
    ghost_map_equiv
      (ghost_map_filter (notp_g (matches_map_group_entry (t_literal k) ty)) consumed)
      ghost_map_empty;
    ghost_map_filter_implies
      (notp_g (matches_map_group_entry (t_literal k) ty))
      (notp_g (matches_map_group_entry (t_literal k) ty))
      rem1;
    assert (ghost_map_filter (notp_g (matches_map_group_entry (t_literal k) ty)) (consumed `ghost_map_union` rem1) == ghost_map_filter (notp_g (matches_map_group_entry (t_literal k) ty)) consumed `ghost_map_union` ghost_map_filter (notp_g (matches_map_group_entry (t_literal k) ty)) rem1);
    assert (ghost_map_filter (notp_g (matches_map_group_entry (t_literal k) ty)) consumed == ghost_map_empty);
    ghost_map_filter_for_all (notp_g (matches_map_group_entry (t_literal k) ty)) rem1;
    assert (ghost_map_filter (notp_g (matches_map_group_entry (t_literal k) ty)) rem1 == rem1);
    assert (ghost_map_filter (notp_g (matches_map_group_entry (t_literal k) ty)) (consumed `ghost_map_union` rem1) == ghost_map_empty `ghost_map_union` rem1);
    assert (apply_map_group_det (map_group_match_item_for cut k ty) (consumed `ghost_map_union` rem1) == MapGroupDet consumed rem1);
    ()
  )
  (fun x1 x2 -> ())
//  (fun x1 x2 -> ())

let map_group_parser_spec_concat_shrinkable_elim
  (g: map_group)
  (x: _)
  (rem1: _)
  (rem2: _)
: Lemma
    (requires (
      map_group_parser_spec_concat_shrinkable g /\
      begin match apply_map_group_det g x with
      | MapGroupDet consumed rem ->
        rem1 `ghost_map_disjoint` rem2 /\
        rem1 `ghost_map_union` rem2 == rem
      | _ -> False
      end
    ))
    (ensures (
      match apply_map_group_det g x with
      | MapGroupDet consumed _ ->
        consumed `ghost_map_disjoint` rem1 /\
        consumed `ghost_map_disjoint` rem2 /\
        apply_map_group_det g (consumed `ghost_map_union` rem1) == MapGroupDet consumed rem1
      | _ -> True
    ))
= ()

let map_group_parser_spec_concat_shrinkable_elim_weak
  (g: map_group)
  (x: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Lemma
  (requires map_group_parser_spec_concat_shrinkable g /\
    MapGroupDet? (apply_map_group_det g x)
  )
  (ensures (match apply_map_group_det g x with
  | MapGroupDet consumed rem ->
    apply_map_group_det g consumed == MapGroupDet consumed ghost_map_empty
  | _ -> True
  ))
= let MapGroupDet _ rem = apply_map_group_det g x in
  map_group_parser_spec_concat_shrinkable_elim g x ghost_map_empty rem

val list_extract_from_ghost_map
  (#key #value: Type)
  (l: list (key & value) {
    List.Tot.no_repeats_p (List.Tot.map fst l)
  })
  (g': ghost_map key value { forall x . ghost_map_mem x g' ==> ghost_map_mem x (ghost_map_of_list l) })
: GTot (l' : list (key & value) {
    List.Tot.no_repeats_p (List.Tot.map fst l') /\
    ghost_map_of_list l' == g'
  })

let map_group_parser_spec_concat
  (#source1: det_map_group)
  (#target1: Type)
  (#target_size1: target1 -> nat)
  (p1: map_group_parser_spec source1 target_size1 {
    map_group_parser_spec_concat_shrinkable source1
  })
  (#source2: det_map_group)
  (#target2: Type)
  (#target_size2: target2 -> nat)
  (p2: map_group_parser_spec source2 target_size2)
  (target_size: (target1 & target2) -> nat {
    forall x . target_size x == target_size1 (fst x) + target_size2 (snd x)
  })
: Tot (map_group_parser_spec (map_group_concat source1 source2) target_size)
= fun l ->
  let MapGroupDet consumed1 rem1 = apply_map_group_det source1 (ghost_map_of_list l) in
  let l1 = list_extract_from_ghost_map l consumed1 in
  map_group_parser_spec_concat_shrinkable_elim_weak source1 (ghost_map_of_list l);
  let res1 = p1 l1 in
  let l2 = list_extract_from_ghost_map l rem1 in
  let res2 = p2 l2 in
  List.Tot.append_length l1 l2;
  ghost_map_length_of_list l1;
  ghost_map_length_of_list l2;
  ghost_map_length_disjoint_union consumed1 rem1;
  (res1, res2)

let map_group_parser_spec_concat_extensible
  (g1: map_group)
  (target_guard2: (Cbor.raw_data_item & Cbor.raw_data_item) -> Tot prop)
: Tot prop
= map_group_parser_spec_concat_shrinkable g1 /\ (
  forall l1 l2 .
    (forall x2 . ghost_map_mem x2 l2 ==> target_guard2 x2) ==>
    begin match apply_map_group_det g1 l1 with
    | MapGroupDet _ rem1 ->
      rem1 == ghost_map_empty ==> (
        ghost_map_disjoint l1 l2 /\
        apply_map_group_det g1 (l1 `ghost_map_union` l2) == MapGroupDet l1 l2
      )
    | MapGroupCutFail ->
      MapGroupCutFail? (apply_map_group_det g1 (l1 `ghost_map_union` l2))
    | MapGroupFail ->
      MapGroupFail? (apply_map_group_det g1 (l1 `ghost_map_union` l2))
    | _ -> True
    end
  )

let map_group_parser_spec_concat_extensible_intro
  (g1: map_group)
  (target_guard2: (Cbor.raw_data_item & Cbor.raw_data_item) -> Tot prop)
  (prf: (l1: _) -> (l2: _) -> Lemma
    (requires (
      (forall x2 . ghost_map_mem x2 l2 ==> target_guard2 x2) /\
      begin match apply_map_group_det g1 l1 with
      | MapGroupDet _ rem1 ->
        rem1 == ghost_map_empty /\
        (forall x2 . ghost_map_mem x2 l2 ==> target_guard2 x2)
      | MapGroupNonDet -> False
      | _ -> True
      end
    ))
    (ensures (
      let res = apply_map_group_det g1 (l1 `ghost_map_union` l2) in
      begin match apply_map_group_det g1 l1 with
      | MapGroupDet _ _ ->
        ghost_map_disjoint l1 l2 /\
        res == MapGroupDet l1 l2
      | MapGroupCutFail -> MapGroupCutFail? res
      | MapGroupFail -> MapGroupFail? res
      | _ -> True
      end
    ))
  )
: Lemma
  (requires map_group_parser_spec_concat_shrinkable g1)
  (ensures map_group_parser_spec_concat_extensible g1 target_guard2)
= Classical.forall_intro_2 (fun l1 -> Classical.move_requires (prf l1))

let map_group_parser_spec_concat_extensible_match_item_for
  (cut: bool)
  (k: Cbor.raw_data_item)
  (ty: typ)
  (target_guard: (Cbor.raw_data_item & Cbor.raw_data_item) -> prop)
: Lemma
  (requires
    (forall x . target_guard x ==> (~ (fst x == k)))
  )
  (ensures map_group_parser_spec_concat_extensible
    (map_group_match_item_for cut k ty) target_guard
  )
= map_group_parser_spec_concat_shrinkable_match_item_for cut k ty;
  map_group_parser_spec_concat_extensible_intro
    (map_group_match_item_for cut k ty)
    target_guard
    (fun l1 l2 ->
      match apply_ghost_map l1 k with
      | Some v ->
        if ty v
        then begin
          assert (l1 == ghost_map_singleton k v);
          assert (ghost_map_disjoint l1 l2);
          assert (MapGroupDet?(apply_map_group_det
            (map_group_match_item_for cut k ty)
            (l1 `ghost_map_union` l2)));
          let MapGroupDet l1' l2' = apply_map_group_det
            (map_group_match_item_for cut k ty)
            (l1 `ghost_map_union` l2) in
          assert (l1 == l1');
          ghost_map_disjoint_union_filter (notp_g (matches_map_group_entry (t_literal k) ty)) l1 l2;
          ghost_map_ext (ghost_map_filter (notp_g (matches_map_group_entry (t_literal k) ty)) l1) ghost_map_empty;
          ghost_map_filter_for_all (notp_g (matches_map_group_entry (t_literal k) ty)) l2;
          assert (l2 == l2')
        end else begin
          ()
        end
      | _ ->
        assert (~ (ghost_map_defined k l2))
    )

val list_extract_from_ghost_map_append_l
  (#key #value: Type)
  (l1: list (key & value) {
    List.Tot.no_repeats_p (List.Tot.map fst l1)
  })
  (l2: list (key & value) {
    List.Tot.no_repeats_p (List.Tot.map fst l2)
  })
: Lemma
  (requires
    ghost_map_disjoint (ghost_map_of_list l1) (ghost_map_of_list l2)
  )
  (ensures
    List.Tot.no_repeats_p (List.Tot.map fst (l1 `List.Tot.append` l2)) /\
    (forall x . ghost_map_mem x (ghost_map_of_list l1) ==> ghost_map_mem x (ghost_map_of_list (l1 `List.Tot.append` l2))) /\
    list_extract_from_ghost_map
      (l1 `List.Tot.append` l2)
      (ghost_map_of_list l1)
    == l1
  )

val list_extract_from_ghost_map_append_r
  (#key #value: Type)
  (l1: list (key & value) {
    List.Tot.no_repeats_p (List.Tot.map fst l1)
  })
  (l2: list (key & value) {
    List.Tot.no_repeats_p (List.Tot.map fst l2)
  })
: Lemma
  (requires
    ghost_map_disjoint (ghost_map_of_list l1) (ghost_map_of_list l2)
  )
  (ensures
    List.Tot.no_repeats_p (List.Tot.map fst (l1 `List.Tot.append` l2)) /\
    (forall x . ghost_map_mem x (ghost_map_of_list l2) ==> ghost_map_mem x (ghost_map_of_list (l1 `List.Tot.append` l2))) /\
    list_extract_from_ghost_map
      (l1 `List.Tot.append` l2)
      (ghost_map_of_list l2)
    == l2
  )

let map_group_parser_spec_concat_extensible_elim
  (g1: map_group)
  (target_guard2: (Cbor.raw_data_item & Cbor.raw_data_item) -> Tot prop {
    map_group_parser_spec_concat_extensible g1 target_guard2
  })
  (l1: _)
  (consumed1: _ {
    apply_map_group_det g1 l1 == MapGroupDet consumed1 ghost_map_empty
  })
  (l2: _)
  (sq: squash (forall x2 . ghost_map_mem x2 l2 ==> target_guard2 x2))
: Lemma (
    ghost_map_disjoint l1 l2 /\
    apply_map_group_det g1 (l1 `ghost_map_union` l2) == MapGroupDet l1 l2
  )
= ()

let map_group_serializer_spec_concat
  (#source1: det_map_group)
  (#target1: Type)
  (#target_size1: target1 -> nat)
  (#p1: map_group_parser_spec source1 target_size1)
  (#target_guard1: (Cbor.raw_data_item & Cbor.raw_data_item) -> Tot prop)
  (s1: map_group_serializer_spec p1 target_guard1)
  (#source2: det_map_group)
  (#target2: Type)
  (#target_size2: target2 -> nat)
  (#p2: map_group_parser_spec source2 target_size2)
  (#target_guard2: (Cbor.raw_data_item & Cbor.raw_data_item) -> Tot prop)
  (s2: map_group_serializer_spec p2 target_guard2 {
    map_group_parser_spec_concat_extensible source1 target_guard2
  })
  (target_size: (target1 & target2) -> nat {
    forall x . target_size x == target_size1 (fst x) + target_size2 (snd x)
  })
  (target_guard: (Cbor.raw_data_item & Cbor.raw_data_item) -> Tot prop {
    forall x . (target_guard1 x \/ target_guard2 x) ==> target_guard x
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_concat p1 p2 target_size) target_guard)
= fun x ->
    let (x1, x2) = x in
    let l1 = s1 x1 in
    let l2 = s2 x2 in
    List.Tot.append_length l1 l2;
    ghost_map_of_list_append l1 l2;
    let res = l1 `List.Tot.append` l2 in
    let MapGroupDet consumed1 _ = apply_map_group_det source1 (ghost_map_of_list l1) in
    Classical.forall_intro (ghost_map_of_list_mem l2);
    let sq : squash (forall x2 . ghost_map_mem x2 (ghost_map_of_list l2) ==> target_guard2 x2) = () in
    map_group_parser_spec_concat_extensible_elim source1 target_guard2 (ghost_map_of_list l1) consumed1 (ghost_map_of_list l2) sq;
    list_extract_from_ghost_map_append_l l1 l2;
    list_extract_from_ghost_map_append_r l1 l2;
    Classical.forall_intro (List.Tot.append_memP l1 l2);
    res

let rec map_group_parser_spec_zero_or_more'
  (#source: det_map_group)
  (#target: Type)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source target_size {
    map_group3_concat_unique_strong source source
  })
  (target_size' : list target -> nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
  (x: map_group_parser_spec_arg (map_group3_zero_or_more source) target_size')
: GTot (map_group_parser_spec_ret (map_group3_zero_or_more source) target_size' x)
  (decreases (List.Tot.length x))
= match source x with
  | None ->
    assert (x == []);
    let res : list target = [] in
    assert (Nil? res);
    assert (target_size' res == 0);
    res
  | Some (l1, l2) ->
    if Nil? l1
    then []
    else begin
      map_group3_concat_unique_weak_zero_or_more_right source source;
      List.Tot.append_length l1 l2;
      let q = map_group_parser_spec_zero_or_more' p target_size' l2 in
      p l1 :: q
    end

let map_group_parser_spec_zero_or_more
  (#source: det_map_group)
  (#target: Type)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source target_size {
    map_group3_concat_unique_strong source source
  })
  (target_size' : list target -> nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
: Tot (map_group_parser_spec (map_group3_zero_or_more source) target_size')
= map_group_parser_spec_zero_or_more' p target_size'

let nonempty_map_group : Type0 =
  (a: map_group {
    forall l . match a l with
    | Some (consumed, _) -> Cons? consumed
    | _ -> True
  })

let rec map_group_serializer_spec_zero_or_more'
  (#source: nonempty_map_group)
  (#target: Type)
  (#target_size: target -> nat)
  (#p: map_group_parser_spec source target_size)
  (s: map_group_serializer_spec p {
    map_group3_concat_unique_strong source source
  })
  (target_size' : list target -> nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
  (x: list target)
: GTot (y: map_group_parser_spec_arg (map_group3_zero_or_more source) target_size' {
    map_group_parser_spec_zero_or_more p target_size' y == x
  })
  (decreases x)
= match x with
  | [] -> []
  | a :: q ->
    map_group3_concat_unique_weak_zero_or_more_right source source;
    let l1 = s a in
    let l2 = map_group_serializer_spec_zero_or_more' s target_size' q in
    let res = l1 `List.Tot.append` l2 in
    res

let map_group_serializer_spec_zero_or_more
  (#source: nonempty_map_group)
  (#target: Type)
  (#target_size: target -> nat)
  (#p: map_group_parser_spec source target_size)
  (s: map_group_serializer_spec p {
    map_group3_concat_unique_strong source source
  })
  (target_size' : list target -> nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_zero_or_more p target_size'))
= map_group_serializer_spec_zero_or_more' s target_size'

let nelist (a: Type) : Type0 = (l: list a { Cons? l })

let map_group_parser_spec_one_or_more
  (#source: det_map_group)
  (#target: Type)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source target_size {
    map_group3_concat_unique_strong source source
  })
  (target_size1 : list target -> nat {
    forall (l: list target) . target_size1 l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size1 (List.Tot.tl l))
  })
  (target_size2 : nelist target -> nat {
    forall (l: nelist target) . target_size2 l == target_size1 l
  })
: Tot (map_group_parser_spec (map_group3_one_or_more source) target_size2)
= fun x ->
  map_group3_concat_unique_weak_zero_or_more_right source source;
  let Some (l1, l2) = source x in
  List.Tot.append_length l1 l2;
  p l1 :: map_group_parser_spec_zero_or_more p target_size1 l2

let map_group_serializer_spec_one_or_more
  (#source: nonempty_map_group)
  (#target: Type)
  (#target_size: target -> nat)
  (#p: map_group_parser_spec source target_size)
  (s: map_group_serializer_spec p {
    map_group3_concat_unique_strong source source
  })
  (target_size1 : list target -> nat {
    forall (l: list target) . target_size1 l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size1 (List.Tot.tl l))
  })
  (target_size2 : nelist target -> nat {
    forall (l: nelist target) . target_size2 l == target_size1 l
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_one_or_more p target_size1 target_size2))
= fun x ->
  map_group3_concat_unique_weak_zero_or_more_right source source;
  let hd :: tl = x in
  let l1 = s hd in
  let l2 = map_group_serializer_spec_zero_or_more s target_size1 tl in
  List.Tot.append_length l1 l2;
  l1 `List.Tot.append` l2

let map_group_parser_spec_choice
  (#source1: det_map_group)
  (#target1: Type0)
  (#target_size1: target1 -> nat)
  (p1: map_group_parser_spec source1 target_size1)
  (#source2: det_map_group)
  (#target2: Type0)
  (#target_size2: target2 -> nat)
  (p2: map_group_parser_spec source2 target_size2)
  (target_size: (target1 `either` target2) -> nat {
    forall x . target_size x == begin match x with
    | Inl y -> target_size1 y
    | Inr y -> target_size2 y
    end
  })
: Tot (map_group_parser_spec (source1 `map_group3_choice` source2) target_size)
= fun x ->
    if Some? (source1 x)
    then Inl (p1 x)
    else Inr (p2 x)

let map_group_serializer_spec_choice
  (#source1: det_map_group)
  (#target1: Type0)
  (#target_size1: target1 -> nat)
  (#p1: map_group_parser_spec source1 target_size1)
  (s1: map_group_serializer_spec p1)
  (#source2: det_map_group)
  (#target2: Type0)
  (#target_size2: target2 -> nat)
  (#p2: map_group_parser_spec source2 target_size2)
  (s2: map_group_serializer_spec p2 { source1 `map_group3_disjoint` source2 }) // disjointness needed to avoid the CBOR object serialized from one case to be parsed into the other case
  (target_size: (target1 `either` target2) -> nat {
    forall x . target_size x == begin match x with
    | Inl y -> target_size1 y
    | Inr y -> target_size2 y
    end
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_choice p1 p2 target_size))
= fun x -> match x with
  | Inl y -> s1 y
  | Inr y -> s2 y

let map_group_parser_spec_zero_or_one
  (#source: det_map_group)
  (#target: Type)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source target_size)
  (target_size': option target -> nat {
    forall x . target_size' x == begin match x with
    | None -> 0
    | Some x -> target_size x
    end
  })
: Tot (map_group_parser_spec (map_group3_zero_or_one source) target_size')
= fun x ->
    if Some? (source x)
    then Some (p x)
    else None

let map_group_serializer_spec_zero_or_one
  (#source: nonempty_map_group) // needed because the empty case must map to None only
  (#target: Type)
  (#target_size: target -> nat)
  (#p: map_group_parser_spec source target_size)
  (s: map_group_serializer_spec p)
  (target_size': option target -> nat {
    forall x . target_size' x == begin match x with
    | None -> 0
    | Some x -> target_size x
    end
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_zero_or_one p target_size'))
= fun x ->
    match x with
    | None -> []
    | Some y -> s y
