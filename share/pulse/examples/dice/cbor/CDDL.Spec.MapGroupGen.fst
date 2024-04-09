module CDDL.Spec.MapGroupGen

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
  [SMTPat (l1 `is_sublist_of` l2)]
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

let is_sublist_of_suffix
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (ensures (l2 `is_sublist_of` (l1 `List.Tot.append` l2)))
  [SMTPat (l1 `List.Tot.append` l2)]
= is_sublist_of_append_right_intro [] l1 l2

let is_sublist_of_prefix
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (ensures (l1 `is_sublist_of` (l1 `List.Tot.append` l2)))
  [SMTPat (l1 `List.Tot.append` l2)]
= List.Tot.append_l_nil l1;
  is_sublist_of_append_left_intro l1 [] l2

let map_group_item_post
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (l': (list (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item)))
: Tot prop
=
        (snd l' `is_sublist_of` l) /\
        List.Tot.length (fst l') + List.Tot.length (snd l') == List.Tot.length l /\
        (forall x . (List.Tot.memP x (fst l') \/ List.Tot.memP x (snd l')) <==> List.Tot.memP x l)

let rec list_memP_extract
  (#t: Type)
  (x: t)
  (l: list t)
: Ghost (list t & list t)
  (requires FStar.List.Tot.memP x l)
  (ensures fun (ll, lr) ->
    l == ll `List.Tot.append` (x :: lr)
  )
= let a :: q = l in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (a == x)
  then ([], q)
  else
    let (ll, lr) = list_memP_extract x q in
    (a :: ll, lr)

let ghost_neq (#t: Type) (l2: t) : Tot (Ghost.erased (t -> bool)) =
  FStar.Ghost.Pull.pull (fun l1 -> FStar.StrongExcludedMiddle.strong_excluded_middle (~ (l1 == l2)))

let ghost_neq_equiv (#t: Type) (l2: t) (l1: t) : Lemma
  (Ghost.reveal (ghost_neq l2) l1 <==> (~ (l1 == l2)))
//  [SMTPat (Ghost.reveal (ghost_neq l2) l1)]
= ()

let rec list_memP_filter (#t: Type) (f: t -> bool) (l: list t) (x: t) : Lemma
  (ensures List.Tot.memP x (List.Tot.filter f l) <==> List.Tot.memP x l /\ f x)
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> list_memP_filter f q x

let rec list_filter_eq_length
  (#t: Type)
  (f: t -> bool)
  (l: list t)
: Lemma
  (requires (List.Tot.length (List.Tot.filter f l) == List.Tot.length l))
  (ensures (List.Tot.filter f l == l))
= match l with
  | [] -> ()
  | a :: q -> list_filter_eq_length f q

#restart-solver
let rec list_memP_equiv_no_repeats // this is actually some form of the pigeon-hole principle
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (requires (
    List.Tot.no_repeats_p l1 /\
    (forall x . List.Tot.memP x l1 <==> List.Tot.memP x l2) /\
    List.Tot.length l1 >= List.Tot.length l2
  ))
  (ensures (
    List.Tot.length l1 == List.Tot.length l2 /\
    List.Tot.no_repeats_p l2
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | a :: q ->
    let (ll, lr) = list_memP_extract a l2 in
    List.Tot.append_length ll (a :: lr);
    List.Tot.append_length ll lr;
    let q2 = List.Tot.filter (ghost_neq a) (ll `List.Tot.append` lr) in
    list_filter_is_sublist_of_intro (ghost_neq a) (ll `List.Tot.append` lr);
    is_sublist_of_length q2 (ll `List.Tot.append` lr);
    let prf
      (x: t)
    : Lemma
      (List.Tot.memP x q <==> List.Tot.memP x q2)
    = list_memP_filter (ghost_neq a) (ll `List.Tot.append` lr) x;
      List.Tot.append_memP ll lr x;
      List.Tot.append_memP ll (a :: lr) x;
      ghost_neq_equiv a x;
      assert (Ghost.reveal (ghost_neq a) x <==> ~ (x == a));
      assert (List.Tot.memP x q2 <==> (List.Tot.memP x ll \/ List.Tot.memP x lr) /\ Ghost.reveal (ghost_neq a) x);
      assert (List.Tot.memP x q2 <==> (List.Tot.memP x ll \/ List.Tot.memP x lr) /\ ~ (x == a))
    in
    Classical.forall_intro prf;
    list_memP_equiv_no_repeats q q2;
    list_filter_eq_length (ghost_neq a) (ll `List.Tot.append` lr);
    assert (q2 == ll `List.Tot.append` lr);
    assert (List.Tot.no_repeats_p (a :: q2));
    List.Tot.no_repeats_p_append_permut [] [] ll [a] lr

let list_memP_map
  (#a #b: Type)
  (f: a -> Tot b)
  (l: list a)
  (y: b)
: Lemma
  (ensures (List.Tot.memP y (List.Tot.map f l) <==> (exists (x : a) . List.Tot.memP x l /\ f x == y)))
= Classical.move_requires (List.Tot.memP_map_elim f y) l;
  Classical.forall_intro (fun x -> Classical.move_requires (List.Tot.memP_map_intro f x) l)

let rec list_ghost_assoc_memP_strong
  (#key #value: Type)
  (k: key)
  (v: value)
  (l: list (key & value))
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst l)))
  (ensures (Cbor.list_ghost_assoc k l == Some v <==> List.Tot.memP (k, v) l))
  (decreases l)
= match l with
  | [] -> ()
  | (k', v') :: q ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
    then Classical.forall_intro (list_memP_map fst q)
    else list_ghost_assoc_memP_strong k v q

let list_ghost_assoc_memP_strong'
  (#key #value: Type)
  (l: list (key & value))
  (sq: squash (List.Tot.no_repeats_p (List.Tot.map fst l)))
: Lemma
  (ensures (forall k v . Cbor.list_ghost_assoc k l == Some v <==> List.Tot.memP (k, v) l))
= Classical.forall_intro_2 (fun k v -> Classical.move_requires (list_ghost_assoc_memP_strong k v) l)

#restart-solver
let map_group_item_post_prop
  (l: cbor_map)
  (l': (list (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item)))
: Lemma
  (requires (map_group_item_post l l'))
  (ensures (
    List.Tot.no_repeats_p (List.Tot.map fst (fst l' `List.Tot.append` snd l')) /\
    List.Tot.no_repeats_p (List.Tot.map fst (fst l')) /\
    List.Tot.no_repeats_p (List.Tot.map fst (snd l')) /\
    (forall x . Cbor.list_ghost_assoc x (fst l' `List.Tot.append` snd l') == Cbor.list_ghost_assoc x l)
  ))
  [SMTPat (map_group_item_post l l')]
=
  Classical.forall_intro (List.Tot.append_memP (fst l') (snd l'));
  Classical.forall_intro (list_memP_map fst l);
  Classical.forall_intro (list_memP_map fst (fst l' `List.Tot.append` snd l'));
  List.Tot.map_append fst (fst l') (snd l');
  list_memP_equiv_no_repeats (List.Tot.map fst l) (List.Tot.map fst (fst l' `List.Tot.append` snd l'));
  assert (List.Tot.no_repeats_p (List.Tot.map fst (fst l' `List.Tot.append` snd l')));
  list_no_repeats_p_is_sublist_of (List.Tot.map fst (fst l')) (List.Tot.map fst (fst l' `List.Tot.append` snd l'));
  assert (List.Tot.no_repeats_p (List.Tot.map fst (fst l')));
  list_no_repeats_p_is_sublist_of (List.Tot.map fst (snd l')) (List.Tot.map fst (fst l' `List.Tot.append` snd l'));
  assert (List.Tot.no_repeats_p (List.Tot.map fst (snd l')));
  let prf x y : Lemma
    (Cbor.list_ghost_assoc x (fst l' `List.Tot.append` snd l') == Some y <==> Cbor.list_ghost_assoc x l == Some y)
  = list_ghost_assoc_memP_strong' l ();
    list_ghost_assoc_memP_strong' (fst l' `List.Tot.append` snd l') ();
    List.Tot.append_memP (fst l') (snd l') (x, y)
  in
  let prf x : Lemma
    (Cbor.list_ghost_assoc x (fst l' `List.Tot.append` snd l') == Cbor.list_ghost_assoc x l)
  = Classical.forall_intro (prf x)
  in
  Classical.forall_intro prf;
  assert (forall x . Cbor.list_ghost_assoc x (fst l' `List.Tot.append` snd l') == Cbor.list_ghost_assoc x l)

let map_group_post
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (res: FStar.GSet.set (list (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item)))
: Tot prop
=
      forall (l': (list (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item))) .
      FStar.GSet.mem l' res ==>  map_group_item_post l l'

let cbor_map_is_sublist_of
  (l1 l2: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (requires
    l1 `is_sublist_of` l2
  )
  (ensures cbor_map_pred l2 ==> cbor_map_pred l1)
  [SMTPat (l1 `is_sublist_of` l2)]
= Classical.move_requires (list_map_is_sublist_of fst l1) l2

module FE = FStar.FunctionalExtensionality

let map_group_codom
  (l: cbor_map)
: Tot Type0
= (res: FStar.GSet.set (list (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item)) {
      map_group_post l res
  })

let map_group : Type0 =
  FE.restricted_g_t
    (cbor_map)
    (map_group_codom)

let map_group_always_false : map_group =
  FE.on_dom_g cbor_map #map_group_codom
    (fun _ -> FStar.GSet.empty)

let map_group_end : map_group =
  FE.on_dom_g cbor_map #map_group_codom
    (fun l -> if Nil? l then FStar.GSet.singleton ([], l) else FStar.GSet.empty)

let map_group_nop : map_group =
  FE.on_dom_g cbor_map #map_group_codom
    (fun l -> FStar.GSet.singleton ([], l))

let map_group_match_item_witness_pred (key value: typ) (l: list (Cbor.raw_data_item & Cbor.raw_data_item)) (l': (list (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item))) (x: (list (Cbor.raw_data_item & Cbor.raw_data_item) & (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item))) : Tot prop =
  let (l1, (k, v), l2) = x in
      l == l1 `List.Tot.append` ((k, v) :: l2) /\
      fst l' == [k, v] /\
      snd l' == l1 `List.Tot.append` l2 /\
      key k /\
      value v

let pred2_equiv_trans
  (#t #t': Type)
  (p1 p2 p3: t -> t' -> prop)
: Lemma
  (requires (
    (forall x x' . p1 x x' <==> p2 x x') /\
    (forall x x' . p2 x x' <==> p3 x x')
  ))
  (ensures (
    (forall x x' . p1 x x' <==> p3 x x')
  ))
= ()

#restart-solver
let map_group_match_item_witness_pred_is_sublist_of (key value: typ) (l: cbor_map) l' x : Lemma
  (requires (map_group_match_item_witness_pred key value l l' x))
  (ensures (
    map_group_item_post l l'
  ))
  [SMTPat (map_group_match_item_witness_pred key value l l' x)]
=
  let (l1, kv, l2) = x in
  list_remove_is_sublist_of l1 kv l2;
  assert (snd l' `is_sublist_of` l);
  List.Tot.append_assoc l1 [kv] l2;
  List.Tot.append_length l1 l2;
  assert (List.Tot.length (fst l') + List.Tot.length (snd l') == List.Tot.length l);
  Classical.forall_intro (List.Tot.append_memP l1 (kv :: l2));
  Classical.forall_intro (List.Tot.append_memP l1 l2);
  assert (forall x . (List.Tot.memP x (fst l') \/ List.Tot.memP x (snd l')) <==> List.Tot.memP x l)

let map_group_match_item_comprehend
  (key value: typ)
  (l: cbor_map)
  l'
: GTot bool
=
    FStar.StrongExcludedMiddle.strong_excluded_middle (exists x .
      map_group_match_item_witness_pred key value l l' x
    )

let map_group_match_item (key value: typ) : map_group =
  FE.on_dom_g cbor_map #map_group_codom
    (fun l -> FStar.GSet.comprehend (map_group_match_item_comprehend key value l))

let map_group_match_item_elim (key value: typ) (l: cbor_map) l' : Ghost _
  (requires (FStar.GSet.mem l' (map_group_match_item key value l)))
  (ensures (fun x -> map_group_match_item_witness_pred key value l l' x))
= FStar.IndefiniteDescription.indefinite_description_ghost _ (map_group_match_item_witness_pred key value l l')

let gset_map_witness_pred (#t1 #t2: Type) (f: t1 -> GTot t2) (s: FStar.GSet.set t1) x2 x1 : GTot prop =
  x2 == f x1 /\ FStar.GSet.mem x1 s

let gset_map (#t1 #t2: Type) (f: t1 -> GTot t2) (s: FStar.GSet.set t1) : FStar.GSet.set t2 =
  FStar.GSet.comprehend (fun x2 -> FStar.StrongExcludedMiddle.strong_excluded_middle (exists x1 .
    gset_map_witness_pred f s x2 x1
  ))

let map_group_match_item_alt_r
  l0
  (ll, lr)
= (ll, List.Tot.append l0 lr)

let map_group_match_item_alt (key value: typ) (l: cbor_map) : GTot _ =
  match list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry key value)) l with
  | None -> FStar.GSet.empty
  | Some (l1, x, l2) ->
    FStar.GSet.union (FStar.GSet.singleton ([x], l1 `List.Tot.append` l2)) (gset_map (map_group_match_item_alt_r (l1 `List.Tot.append` [x])) (map_group_match_item key value l2))

#push-options "--z3rlimit 32"

#restart-solver
let map_group_match_item_alt_map_group_match_item
  (key value: typ) (l: cbor_map) l'
: Lemma
  (FStar.GSet.mem l' (map_group_match_item_alt key value l) ==> FStar.GSet.mem l' (map_group_match_item key value l))
= if FStar.GSet.mem l' (map_group_match_item_alt key value l)
  then begin
    let Some (l1, x, l2) = list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry key value)) l in
    if FStar.StrongExcludedMiddle.strong_excluded_middle (l' == ([x], l1 `List.Tot.append` l2))
    then assert (map_group_match_item_witness_pred key value l l' (l1, x, l2))
    else begin
      let l2' = FStar.IndefiniteDescription.indefinite_description_ghost _ (gset_map_witness_pred (map_group_match_item_alt_r (l1 `List.Tot.append` [x])) (map_group_match_item key value l2) l') in
      let (ll2', x', lr2') = FStar.IndefiniteDescription.indefinite_description_ghost _ (map_group_match_item_witness_pred key value l2 l2') in
      List.Tot.append_assoc l1 [x] (ll2' `List.Tot.append` (x' :: lr2'));
      List.Tot.append_assoc (l1 `List.Tot.append` [x]) ll2' (x' :: lr2');
      List.Tot.append_assoc (l1 `List.Tot.append` [x]) ll2' lr2';
      assert (map_group_match_item_witness_pred key value l l' ((l1 `List.Tot.append` [x]) `List.Tot.append` ll2', x', lr2'))
    end
  end

#pop-options

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

#push-options "--z3rlimit 16"

#restart-solver
let map_group_match_item_map_group_match_item_alt
  (key value: typ) (l: cbor_map) l'
: Lemma
  (FStar.GSet.mem l' (map_group_match_item key value l) ==> FStar.GSet.mem l' (map_group_match_item_alt key value l))
= if FStar.GSet.mem l' (map_group_match_item key value l)
  then begin
    let (ll', x', lr') = FStar.IndefiniteDescription.indefinite_description_ghost _ (map_group_match_item_witness_pred key value l l') in
    List.Tot.for_all_append (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value))) ll' (x' :: lr');
    let Some (ll, x, lr) = list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry key value)) l in
    list_filter_and_extract_length (FStar.Ghost.Pull.pull (matches_map_group_entry key value)) ll (x :: lr) ll' x' lr';
    assert (List.Tot.length ll <= List.Tot.length ll');
    if List.Tot.length ll = List.Tot.length ll'
    then List.Tot.append_length_inv_head ll (x :: lr) ll' (x' :: lr')
    else begin
      assert (List.Tot.length ll + 1 <= List.Tot.length ll');
      List.Tot.append_assoc ll [x] lr;
      List.Tot.append_length ll [x];
      let lp = list_extract_prefix (ll `List.Tot.append` [x]) lr ll' (x' :: lr') in
      List.Tot.append_assoc (ll `List.Tot.append` [x]) lp (x' :: lr');
      List.Tot.append_inv_head (ll `List.Tot.append` [x]) lr (lp `List.Tot.append` (x' :: lr'));
      assert (map_group_match_item_witness_pred key value lr ([x'], lp `List.Tot.append` lr') (lp, x', lr'));
      List.Tot.append_assoc (ll `List.Tot.append` [x]) lp lr';
      assert (gset_map_witness_pred (map_group_match_item_alt_r (ll `List.Tot.append` [x])) (map_group_match_item key value lr) l' ([x'], lp `List.Tot.append` lr'))
    end
  end

#pop-options

let map_group_equiv
  (m1 m2: map_group)
: Tot prop
= forall l . m1 l `FStar.GSet.equal` m2 l

let map_group_equiv_eq
  (m1 m2: map_group)
: Lemma
  (map_group_equiv m1 m2 <==> m1 == m2)
  [SMTPat (map_group_equiv m1 m2)]
= assert (FE.feq_g m1 m2 <==> m1 == m2)

let map_group_match_item_alt_correct
  (key value: typ) (l: cbor_map)
: Lemma
  (map_group_match_item_alt key value l == map_group_match_item key value l)
= Classical.forall_intro (map_group_match_item_map_group_match_item_alt key value l);
  Classical.forall_intro (map_group_match_item_alt_map_group_match_item key value l);
  assert (map_group_match_item_alt key value l `FStar.GSet.equal` map_group_match_item key value l)

let map_group_choice (m1 m2: map_group) : map_group =
  FE.on_dom_g cbor_map #map_group_codom (fun l ->
    // greedy PEG semantics for `//`
    let res1 = m1 l in
    if FStar.StrongExcludedMiddle.strong_excluded_middle (res1 == FStar.GSet.empty)
    then m2 l
    else res1
  )

let map_group_cut (cut: typ) (m: map_group) : map_group =
  FE.on_dom_g cbor_map #map_group_codom (fun l -> 
    if List.Tot.for_all (notp (FStar.Ghost.Pull.pull (matches_map_group_entry cut any))) l
    then m l
    else FStar.GSet.empty
  )

let map_group_concat_witness_pred
  (m1 m2: map_group)
  (l: cbor_map)
  (l': (list (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item)))
  (l1l2: (list (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item)) & (list (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item)))
: Tot prop
= let (l1, l2) = l1l2 in
  FStar.GSet.mem l1 (m1 l) /\
  FStar.GSet.mem l2 (m2 (snd l1)) /\
  l' == (fst l1 `List.Tot.append` fst l2, snd l2)

let map_group_concat_witness_pred_correct
  (m1 m2: map_group)
  (l: cbor_map)
  (l': (list (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item)))
  (l1l2: (list (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item)) & (list (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item)))
: Lemma
  (requires map_group_concat_witness_pred m1 m2 l l' l1l2)
  (ensures map_group_item_post l l')
  [SMTPat (map_group_concat_witness_pred m1 m2 l l' l1l2)]
= let (l1, l2) = l1l2 in
  assert (snd l' `is_sublist_of` l);
  List.Tot.append_length (fst l1) (fst l2);
  assert (List.Tot.length (fst l') + List.Tot.length (snd l') == List.Tot.length l);
  Classical.forall_intro (List.Tot.append_memP (fst l1) (fst l2));
  assert (forall x . (List.Tot.memP x (fst l') \/ List.Tot.memP x (snd l')) <==> List.Tot.memP x l)

let map_group_concat (m1 m2: map_group) : map_group =
  FE.on_dom_g cbor_map #map_group_codom
    (fun l -> FStar.GSet.comprehend (fun l' -> FStar.StrongExcludedMiddle.strong_excluded_middle (exists l1l2 . map_group_concat_witness_pred m1 m2 l l' l1l2)))
  
let map_group_concat_elim (m1 m2: map_group) (l: cbor_map) l' : Ghost _
  (requires FStar.GSet.mem l' (map_group_concat m1 m2 l))
  (ensures fun l1l2 ->
    map_group_concat_witness_pred m1 m2 l l' l1l2
  )
= FStar.IndefiniteDescription.indefinite_description_ghost _ (fun l1l2 -> map_group_concat_witness_pred m1 m2 l l' l1l2)

let map_group_equiv_intro
  (m1 m2: map_group)
  (prf12: (l: cbor_map) ->
    (l': _) ->
    Lemma
    (requires FStar.GSet.mem l' (m1 l))
    (ensures FStar.GSet.mem l' (m2 l))
  )
  (prf21: (l: cbor_map) ->
    (l': _) ->
    Lemma
    (requires FStar.GSet.mem l' (m2 l))
    (ensures FStar.GSet.mem l' (m1 l))
  )
: Lemma
  (map_group_equiv m1 m2)
= Classical.forall_intro_2 (fun l l' -> Classical.move_requires (prf12 l) l');
  Classical.forall_intro_2 (fun l l' -> Classical.move_requires (prf21 l) l')

#push-options "--z3rlimit 16"

#restart-solver
let map_group_concat_assoc' (m1 m2 m3: map_group) : Lemma
  (map_group_concat m1 (map_group_concat m2 m3) `map_group_equiv` map_group_concat (map_group_concat m1 m2) m3)
= map_group_equiv_intro
    (map_group_concat m1 (map_group_concat m2 m3))
    (map_group_concat (map_group_concat m1 m2) m3)
    (fun l l' -> 
      let (l1, l23) = map_group_concat_elim m1 (map_group_concat m2 m3) l l' in
      let (l2, l3) = map_group_concat_elim m2 m3 (snd l1) l23 in
      assert (FStar.GSet.mem l1 (m1 l));
      assert (FStar.GSet.mem l2 (m2 (snd l1)));
      assert (FStar.GSet.mem l3 (m3 (snd l2)));
      let l12 = (fst l1 `List.Tot.append` fst l2, snd l2) in
      assert (map_group_concat_witness_pred m1 m2 l l12 (l1, l2));
      List.Tot.append_assoc (fst l1) (fst l2) (fst l3);
      assert (map_group_concat_witness_pred (map_group_concat m1 m2) m3 l l' (l12, l3))
    )
    (fun l l' -> 
      let (l12, l3) = map_group_concat_elim (map_group_concat m1 m2) m3 l l' in
      let (l1, l2) = map_group_concat_elim m1 m2 l l12 in
      let l23 = (fst l2 `List.Tot.append` fst l3, snd l3) in
      assert (map_group_concat_witness_pred m2 m3 (snd l1) l23 (l2, l3));
      List.Tot.append_assoc (fst l1) (fst l2) (fst l3);
      assert (map_group_concat_witness_pred m1 (map_group_concat m2 m3) l l' (l1, l23))
    )

#pop-options

let map_group_concat_assoc m1 m2 m3 =
  map_group_concat_assoc' m1 m2 m3

let map_group_mk_cut (cut: typ) : map_group =
  FE.on_dom_g cbor_map #map_group_codom (fun l -> 
    if List.Tot.for_all (notp (FStar.Ghost.Pull.pull (matches_map_group_entry cut any))) l
    then FStar.GSet.singleton ([], l)
    else FStar.GSet.empty
  )

let list_append_l_nil
  (#t: Type)
  (l: list t)
: Lemma
  (l `List.Tot.append` [] == l)
  [SMTPat (l `List.Tot.append` [])]
= List.Tot.append_l_nil l

#restart-solver
let map_group_concat_nop_l
  (m: map_group)
: Lemma
  (map_group_concat map_group_nop m == m)
= map_group_equiv_intro
    (map_group_concat map_group_nop m)
    m
    (fun l l' -> ())
    (fun l l' -> 
      assert (map_group_concat_witness_pred map_group_nop m l l' (([], l), l'))
    )

let map_group_concat_nop_r
  (m: map_group)
: Lemma
  (map_group_concat m map_group_nop == m)
= map_group_equiv_intro
    (map_group_concat m map_group_nop)
    m
    (fun l l' -> ())
    (fun l l' -> 
      assert (map_group_concat_witness_pred m map_group_nop l l' (l', ([], snd l')))
    )

#restart-solver
let map_group_cut_eq
  (cut: typ)
  (m: map_group)
: Lemma
  (map_group_cut cut m == (map_group_mk_cut cut `map_group_concat` m))
= map_group_equiv_intro
    (map_group_cut cut m)
    (map_group_mk_cut cut `map_group_concat` m)
    (fun l l' ->
       assert (map_group_concat_witness_pred (map_group_mk_cut cut) m l l' (([], l), l'))
    )
    (fun l l' -> ())

let bound_map_group
  (l0: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (m: (l: cbor_map { List.Tot.length l < List.Tot.length l0 }) ->
  Ghost _
    (requires True)
    (ensures fun l' -> map_group_post l l')
  )
: map_group
= FE.on_dom_g cbor_map #map_group_codom
    (fun l -> if List.Tot.length l >= List.Tot.length l0 then FStar.GSet.singleton ([], l) else m l)

let bound_map_group_ext
  (l0: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (m1 m2: (l: cbor_map { List.Tot.length l < List.Tot.length l0 }) ->
  Ghost _
    (requires True)
    (ensures fun l' -> map_group_post l l')
  )
: Lemma
  (requires forall (l: cbor_map { List.Tot.length l < List.Tot.length l0 }) .
    m1 l == m2 l
  )
  (ensures bound_map_group l0 m1 == bound_map_group l0 m2)
= map_group_equiv_intro (bound_map_group l0 m1) (bound_map_group l0 m2)
    (fun l l' -> ())
    (fun l l' -> ())

// greedy PEG semantics for `*`
let rec map_group_zero_or_more'
  (m: map_group)
  (l: cbor_map)
: GTot (l': _ {
    map_group_post l l'
  })
  (decreases (List.Tot.length l))
= let res1 = m l in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (res1 == FStar.GSet.empty)
  then FStar.GSet.singleton ([], l)
  else map_group_concat m (bound_map_group l (map_group_zero_or_more' m)) l

let map_group_zero_or_more m =
  FE.on_dom_g cbor_map #map_group_codom (map_group_zero_or_more' m)

let map_group_zero_or_more_eq
  (m: map_group)
  (l: cbor_map)
: Lemma
  (ensures (map_group_zero_or_more m l == (let res1 = m l in
    if FStar.StrongExcludedMiddle.strong_excluded_middle (res1 == FStar.GSet.empty)
    then FStar.GSet.singleton ([], l)
    else map_group_concat m (bound_map_group l (map_group_zero_or_more m)) l
  )))
  (decreases (List.Tot.length l))
= assert (forall l . map_group_zero_or_more m l == map_group_zero_or_more' m l);
  assert_norm (map_group_zero_or_more' m l == (let res1 = m l in
    if FStar.StrongExcludedMiddle.strong_excluded_middle (res1 == FStar.GSet.empty)
    then FStar.GSet.singleton ([], l)
    else map_group_concat m (bound_map_group l (map_group_zero_or_more' m)) l
  ));
  bound_map_group_ext l (map_group_zero_or_more m) (map_group_zero_or_more' m)

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

let map_group_match_item_for_eq_none
  (k: Cbor.raw_data_item)
  (ty: typ)
  (l: cbor_map)
: Lemma
  (requires (
    (~ (List.Tot.memP k (List.Tot.map fst l)))
  ))
  (ensures (
    map_group_match_item_for k ty l == FStar.GSet.empty
  ))
= map_group_match_item_alt_correct (t_literal k) ty l;
  list_filter_and_extract_assoc k ty l;
  list_ghost_assoc_memP k l

let map_group_match_item_for_eq
  (k: Cbor.raw_data_item)
  (ty: typ)
  (l: cbor_map)
: Lemma
  (ensures (
    map_group_match_item_for k ty l `FStar.GSet.equal` begin match list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty)) l with
    | None -> FStar.GSet.empty
    | Some (ll, kv, lr) -> FStar.GSet.singleton ([kv], ll `List.Tot.append` lr)
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
    map_group_match_item_for_eq_none k ty lr

let rec list_for_all_implies_filter
  (#t: Type)
  (f: t -> bool)
  (l: list t)
: Lemma
  (requires (List.Tot.for_all f l))
  (ensures (List.Tot.filter f l == l))
= match l with
  | [] -> ()
  | _ :: q -> list_for_all_implies_filter f q

let gset_equal_intro
  (#t: Type)
  (s1 s2: FStar.GSet.set t)
  (prf12: (x: t) -> Lemma
    (requires FStar.GSet.mem x s1)
    (ensures FStar.GSet.mem x s2)
  )
  (prf21: (x: t) -> Lemma
    (requires FStar.GSet.mem x s2)
    (ensures FStar.GSet.mem x s1)
  )
: Lemma
  (s1 == s2)
= Classical.forall_intro (Classical.move_requires prf12);
  Classical.forall_intro (Classical.move_requires prf21);
  assert (s1 `FStar.GSet.equal` s2)

let rec list_filter_append
  (#t: Type)
  (f: t -> bool)
  (l1 l2: list t)
: Lemma
  (ensures List.Tot.filter f (l1 `List.Tot.append` l2) == List.Tot.filter f l1 `List.Tot.append` List.Tot.filter f l2)
  (decreases l1)
= match l1 with
  | [] -> ()
  | _ :: q -> list_filter_append f q l2

let gset_collect_bound_map_group_length_lt
  (l: cbor_map)
  (m: map_group)
  (s: FStar.GSet.set cbor_map)
: Lemma
  (requires (forall (x: cbor_map) . FStar.GSet.mem x s ==> List.Tot.length x < List.Tot.length l))
  (ensures (
    gset_collect (bound_map_group l m) s `FStar.GSet.equal` gset_collect m s
  ))
= ()

let map_group_match_item_length
  (key value: typ)
  (l: cbor_map)
  (l': list (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (requires FStar.GSet.mem l' (map_group_match_item key value l))
  (ensures List.Tot.length l' < List.Tot.length l)
  [SMTPat (FStar.GSet.mem l' (map_group_match_item key value l))]
= let (l1, kv, l2) = FStar.IndefiniteDescription.indefinite_description_ghost _ (map_group_match_item_witness_pred key value l l') in
  List.Tot.append_length l1 (kv :: l2);
  List.Tot.append_length l1 l2

#push-options "--z3rlimit 16"

#restart-solver
let rec map_group_zero_or_more_match_item_eq
  (key value: typ)
  (l: cbor_map)
: Lemma
  (ensures map_group_zero_or_more (map_group_match_item key value) l `FStar.GSet.equal`
    FStar.GSet.singleton (List.Tot.filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value))) l))
  (decreases (List.Tot.length l))
=
  let m = map_group_match_item key value in
  let f = FStar.Ghost.Pull.pull (matches_map_group_entry key value) in
  let gset_collect_map_group_zero_or_more_match_item_eq
    (s: FStar.GSet.set cbor_map)
  : Lemma
    (requires (forall (x: cbor_map) . FStar.GSet.mem x s ==> List.Tot.length x < List.Tot.length l))
    (ensures gset_collect (map_group_zero_or_more m) s `FStar.GSet.equal`
      gset_map (List.Tot.filter (notp f)) s
    )
  = gset_equal_intro
      (gset_collect (map_group_zero_or_more m) s)
      (gset_map (List.Tot.filter (notp f)) s)
      (fun l' ->
        let l1 = FStar.IndefiniteDescription.indefinite_description_ghost _ (gset_collect_witness_pred (map_group_zero_or_more m) s l') in
        map_group_zero_or_more_match_item_eq key value l1;
        assert (gset_map_witness_pred (List.Tot.filter (notp f)) s l' l1)
      )
      (fun l' ->
        let l1 = FStar.IndefiniteDescription.indefinite_description_ghost _ (gset_map_witness_pred (List.Tot.filter (notp f)) s l') in
        map_group_zero_or_more_match_item_eq key value l1;
        assert (gset_collect_witness_pred (map_group_zero_or_more m) s l' l1)
      )
  in
  map_group_zero_or_more_eq m l;
  let res1 = apply_map_group m l in
  map_group_match_item_alt_correct key value l;
  match list_filter_and_extract f l with
  | None ->
    assert (apply_map_group m l `FStar.GSet.equal` FStar.GSet.empty);
    list_for_all_implies_filter (notp f) l
  | Some (l1, kv, l2) ->
    assert (~ (apply_map_group m l == FStar.GSet.empty));
    gset_collect_bound_map_group_length_lt l (map_group_zero_or_more m) res1;
    gset_collect_map_group_zero_or_more_match_item_eq res1;
    assert (map_group_zero_or_more m l == gset_map (List.Tot.filter (notp f)) res1);
    gset_equal_intro
      (FStar.GSet.singleton (List.Tot.filter (notp f) l)) 
      (gset_map (List.Tot.filter (notp f)) res1)
      (fun l' ->
        assert (l' == List.Tot.filter (notp f) l);
        assert (FStar.GSet.mem (l1 `List.Tot.append` l2) res1);
        list_filter_append (notp f) l1 l2;
        list_filter_append (notp f) l1 (kv :: l2);
        assert (gset_map_witness_pred (List.Tot.filter (notp f)) res1 l' (l1 `List.Tot.append` l2))
      )
      (fun l' ->
        let l1 = FStar.IndefiniteDescription.indefinite_description_ghost _ (gset_map_witness_pred (List.Tot.filter (notp f)) res1 l') in
        assert (FStar.GSet.mem l1 res1);
        let (ll, kv, lr) = map_group_match_item_elim key value l l1 in
        list_filter_append (notp f) ll lr;
        list_filter_append (notp f) ll (kv :: lr);
        assert (l == ll `List.Tot.append` (kv :: lr));
        assert (l1 == ll `List.Tot.append` lr);
        assert (f kv);
        assert (l' == List.Tot.filter (notp f) l1);
        assert (List.Tot.filter (notp f) (kv :: lr) == List.Tot.filter (notp f) lr);
        assert (l' == List.Tot.filter (notp f) l)
      )

#pop-options

let apply_map_group_det (m: map_group) (l: cbor_map) : Pure map_group_result
  (requires True)
  (ensures fun r -> map_group_result_prop l r)
= let s = m l in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (s == FStar.GSet.empty)
  then MapGroupFail
  else if FStar.StrongExcludedMiddle.strong_excluded_middle (exists x . s == FStar.GSet.singleton x)
  then MapGroupDet (FStar.IndefiniteDescription.indefinite_description_ghost _ (fun x -> s == FStar.GSet.singleton x))
  else MapGroupNonDet

let apply_map_group_det_eq_singleton (m: map_group) (l: cbor_map) x : Lemma
  (requires (m l `FStar.GSet.equal` FStar.GSet.singleton x))
  (ensures (apply_map_group_det m l == MapGroupDet x))
= ()

let apply_map_group_det_always_false (l: cbor_map) : Lemma
  (apply_map_group_det map_group_always_false l == MapGroupFail)
= ()

let apply_map_group_det_end (l: cbor_map) : Lemma
  (apply_map_group_det map_group_end l == (if Nil? l then MapGroupDet l else MapGroupFail))
= ()

let apply_map_group_det_nop (l: cbor_map) : Lemma
  (apply_map_group_det map_group_nop l == MapGroupDet l)
= ()

let apply_map_group_det_map_group_equiv (m1 m2: map_group) : Lemma
  (requires
    (forall l . ~ (MapGroupNonDet? (apply_map_group_det m1 l))) /\
    (forall l . apply_map_group_det m1 l == apply_map_group_det m2 l)
  )
  (ensures m1 == m2)
= assert (m1 `map_group_equiv` m2)

let gset_collect_empty
  (m: map_group)
  (l: FStar.GSet.set cbor_map)
: Lemma
  (requires l `FStar.GSet.equal` FStar.GSet.empty)
  (ensures gset_collect m l `FStar.GSet.equal` FStar.GSet.empty)
= ()

let gset_collect_singleton
  (m: map_group)
  (l: FStar.GSet.set cbor_map)
  (x: cbor_map)
: Lemma
  (requires l `FStar.GSet.equal` FStar.GSet.singleton x)
  (ensures gset_collect m l `FStar.GSet.equal` m x)
= ()

let apply_map_group_det_choice (m1 m2: map_group) (l: cbor_map) : Lemma
  (match apply_map_group_det m1 l with
  | MapGroupFail -> apply_map_group_det (m1 `map_group_choice` m2) l == apply_map_group_det m2 l
  | MapGroupDet l1 -> apply_map_group_det (m1 `map_group_choice` m2) l == MapGroupDet l1
  | _ -> True
  )
= ()

let apply_map_group_det_concat (m1 m2: map_group) (l: cbor_map) : Lemma
  (match apply_map_group_det m1 l with
  | MapGroupFail -> apply_map_group_det (m1 `map_group_concat` m2) l == MapGroupFail
  | MapGroupDet l1 -> apply_map_group_det (m1 `map_group_concat` m2) l == apply_map_group_det m2 l1
  | _ -> True)
= match apply_map_group_det m1 l with
  | MapGroupFail -> 
    gset_collect_empty m2 (apply_map_group m1 l)
  | MapGroupDet l1 ->
    gset_collect_singleton m2 (apply_map_group m1 l) l1
  | _ -> ()

let apply_map_group_det_mk_cut cut l = ()

#restart-solver
let apply_map_group_det_match_item_for
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
= map_group_match_item_for_eq k ty l;
  list_filter_and_extract_assoc k ty l;
  match list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty)) l with
  | None -> ()
  | Some (ll, kv, lr) ->
    Classical.forall_intro (fun x -> List.Tot.memP_map_intro fst x ll);
    Classical.forall_intro (fun x -> List.Tot.memP_map_intro fst x lr);
    List.Tot.for_all_mem (notp (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty))) ll;
    list_for_all_implies_filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty))) ll;
    List.Tot.for_all_mem (notp (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty))) lr;
    list_for_all_implies_filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty))) lr;
    list_filter_append (notp (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty))) ll (kv :: lr);
    apply_map_group_det_eq_singleton (map_group_match_item_for k ty) l
      (List.Tot.filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty))) l)

#restart-solver
let apply_map_group_det_zero_or_more_match_item
  (key value: typ)
  (l: cbor_map)
: Lemma
  (apply_map_group_det (map_group_zero_or_more (map_group_match_item key value)) l ==
    MapGroupDet (List.Tot.filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value))) l)
  )
= map_group_zero_or_more_match_item_eq key value l;
  assert (
    map_group_zero_or_more (map_group_match_item key value) l ==
    FStar.GSet.singleton (List.Tot.filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value))) l)
  )

let map_group_filter
  f
= FE.on_dom_g cbor_map #map_group_codom (fun l ->
    FStar.GSet.singleton (List.Tot.filter f l)
  )

let apply_map_group_det_filter
  f l
= ()

let list_filter_implies_2' (#t: Type) (p1 p2: t -> bool) : Lemma
  (requires (forall (x: t) . p1 x ==> p2 x))
  (ensures forall  (l: list t) . List.Tot.filter p1 (List.Tot.filter p2 l) == List.Tot.filter p1 l)
= Classical.forall_intro (fun l -> Classical.move_requires (list_filter_implies_2 p1 p2) l)

#restart-solver
let map_group_zero_or_one_match_item_filter
  key value p
= map_group_equiv_intro
    (map_group_zero_or_one (map_group_match_item key value) `map_group_concat` map_group_filter p)
    (map_group_filter p)
    (fun l l' ->
      let l1 = map_group_concat_elim (map_group_zero_or_one (map_group_match_item key value)) (map_group_filter p) l l' in
      if FStar.StrongExcludedMiddle.strong_excluded_middle (map_group_match_item key value l == FStar.GSet.empty)
      then ()
      else begin
        let (ll, kv, lr) = map_group_match_item_elim key value l l1 in
        list_filter_append p ll (kv :: lr);
        list_filter_append p ll lr
      end
    )
    (fun l l' ->
      if not (FStar.StrongExcludedMiddle.strong_excluded_middle (exists l1 . FStar.GSet.mem l1 (map_group_match_item key value l)))
      then assert (map_group_match_item key value l `FStar.GSet.equal` FStar.GSet.empty)
      else begin
        let l1 = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun l1 -> FStar.GSet.mem l1 (map_group_match_item key value l)) in
        let (ll, kv, lr) = map_group_match_item_elim key value l l1 in
        list_filter_append p ll (kv :: lr);
        list_filter_append p ll lr;
        assert (l' == List.Tot.filter p l1);
        assert (gset_collect_witness_pred (map_group_filter p) (apply_map_group (map_group_zero_or_one (map_group_match_item key value)) l) l' l1)
      end
    )

let rec list_filter_and_extract_none
  (#t: Type)
  (p: t -> bool)
  (l: list t)
: Lemma
  (requires (None? (list_filter_and_extract p l)))
  (ensures (List.Tot.filter (notp p) l == l))
= match l with
  | [] -> ()
  | a :: q -> list_filter_and_extract_none p q

let list_ghost_assoc_none_filter_matches_map_group_entry_for
  (key: Cbor.raw_data_item)
  (value: typ)
  (l: cbor_map)
: Lemma
  (requires (match Cbor.list_ghost_assoc key l with
  | None -> True
  | Some v -> ~ (value v)))
  (ensures List.Tot.filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal key) value))) l == l)
= list_filter_and_extract_assoc key value l;
  list_filter_and_extract_none (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal key) value)) l

let map_group_zero_or_more_map_group_match_item_for
  (key: Cbor.raw_data_item)
  (value: typ)
: Lemma
  (map_group_zero_or_more (map_group_match_item_for key value) ==
    map_group_zero_or_one (map_group_match_item_for key value)
  )
= Classical.forall_intro (Classical.move_requires (
      list_ghost_assoc_none_filter_matches_map_group_entry_for key value
  ));
  apply_map_group_det_map_group_equiv
    (map_group_zero_or_more (map_group_match_item_for key value))
    (map_group_zero_or_one (map_group_match_item_for key value))

let map_group_choice_assoc
  (g1 g2 g3: map_group)
: Lemma
  ((g1 `map_group_choice` g2) `map_group_choice` g3 == g1 `map_group_choice` (g2 `map_group_choice` g3))
= assert (((g1 `map_group_choice` g2) `map_group_choice` g3) `map_group_equiv` (g1 `map_group_choice` (g2 `map_group_choice` g3)))

let map_group_zero_or_one_choice
  (g1 g2: map_group)
: Lemma
  (map_group_zero_or_one (g1 `map_group_choice` g2) == g1 `map_group_choice` map_group_zero_or_one g2)
= map_group_choice_assoc g1 g2 map_group_nop

let matches_map_group (g: map_group) (m: cbor_map) : GTot bool =
    FStar.GSet.mem [] (g m)

let matches_map_group_det (g: map_group) (m: cbor_map) : Lemma
  (match apply_map_group_det g m with
  | MapGroupFail -> ~ (matches_map_group g m)
  | MapGroupDet m' -> matches_map_group g m <==> m' == []
  | _ -> True)
= ()

let map_group_entry_consumed
  (l: cbor_map)
  (entry: (Cbor.raw_data_item & Cbor.raw_data_item))
  (g: map_group)
: Tot prop
= List.Tot.memP entry l /\
  (exists l' . FStar.GSet.mem l' (g l) /\ ~ (List.Tot.memP entry l'))

let map_group_entry_consumed_matches_map_group
  (l: cbor_map)
  (entry: (Cbor.raw_data_item & Cbor.raw_data_item))
  (g: map_group)
: Lemma
  (requires (List.Tot.memP entry l /\ g `matches_map_group` l))
  (ensures map_group_entry_consumed l entry g)
= ()

let map_group_entry_consumed_concat
  (l: cbor_map)
  (entry: (Cbor.raw_data_item & Cbor.raw_data_item))
  (g1 g2: map_group)
: Lemma
  (requires map_group_entry_consumed l entry (g1 `map_group_concat` g2))
  (ensures
    map_group_entry_consumed l entry g1 \/
    (exists l' . FStar.GSet.mem l' (apply_map_group g1 l) /\ map_group_entry_consumed l' entry g2)
  )
= ()

let map_group_entry_consumed_concat_det
  (l: cbor_map)
  (entry: (Cbor.raw_data_item & Cbor.raw_data_item))
  (g1 g2: map_group)
: Lemma
  (requires map_group_entry_consumed l entry (g1 `map_group_concat` g2) /\
    MapGroupDet? (apply_map_group_det g1 l)
  )
  (ensures
    map_group_entry_consumed l entry g1 \/
    (let MapGroupDet l' = apply_map_group_det g1 l in map_group_entry_consumed l' entry g2)
  )
= ()

let map_group_entry_consumed_match_item_intro
  (l: cbor_map)
  (kv: (Cbor.raw_data_item & Cbor.raw_data_item))
  (key value: typ)
: Lemma
  (requires
    List.Tot.memP kv l /\
    matches_map_group_entry key value kv
  )
  (ensures
    map_group_entry_consumed l kv (map_group_match_item key value)
  )
= let (ll, lr) = list_memP_extract kv l in
  assert (map_group_match_item_witness_pred key value l (ll `List.Tot.append` lr) (ll, kv, lr));
  List.Tot.map_append fst ll (kv :: lr);
  List.Tot.no_repeats_p_append (List.Tot.map fst ll) (List.Tot.map fst (kv :: lr));
  assert (~ (List.Tot.memP (fst kv) (List.Tot.map fst ll)));
  assert (~ (List.Tot.memP (fst kv) (List.Tot.map fst lr)));
  List.Tot.append_memP (List.Tot.map fst ll) (List.Tot.map fst lr) (fst kv);
  List.Tot.map_append fst ll lr;
  assert (~ (List.Tot.memP (fst kv) (List.Tot.map fst (ll `List.Tot.append` lr))));
  Classical.move_requires (List.Tot.memP_map_intro fst kv) (ll `List.Tot.append` lr);
  assert (~ (List.Tot.memP kv (ll `List.Tot.append` lr)))

let map_group_entry_consumed_match_item_elim
  (l: cbor_map)
  (kv: (Cbor.raw_data_item & Cbor.raw_data_item))
  (key value: typ)
: Lemma
  (requires
    map_group_entry_consumed l kv (map_group_match_item key value)
  )
  (ensures
    List.Tot.memP kv l /\
    matches_map_group_entry key value kv
  )
= let l' = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun l' -> FStar.GSet.mem l' (map_group_match_item key value l) /\ ~ (List.Tot.memP kv l')) in
  let (ll, kv', lr) = map_group_match_item_elim key value l l' in
  List.Tot.append_memP ll lr kv;
  List.Tot.append_memP ll (kv' :: lr) kv;
  assert (kv == kv')

let map_group_entry_consumed_match_item
  (l: cbor_map)
  (kv: (Cbor.raw_data_item & Cbor.raw_data_item))
  (key value: typ)
: Lemma
  (
    map_group_entry_consumed l kv (map_group_match_item key value) <==> (
    List.Tot.memP kv l /\
    matches_map_group_entry key value kv
  ))
= Classical.move_requires (map_group_entry_consumed_match_item_intro l kv key) value;
  Classical.move_requires (map_group_entry_consumed_match_item_elim l kv key) value

let map_group_disjoint
  (g1 g2: map_group)
: Tot prop
= forall l1 l2 entry . ~ (map_group_entry_consumed l1 entry g1 /\ map_group_entry_consumed l2 entry g2)
