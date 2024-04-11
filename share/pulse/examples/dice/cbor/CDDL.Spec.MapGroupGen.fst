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

module FE = FStar.FunctionalExtensionality

let ghost_map (key value: Type) : Type =
  FE.restricted_g_t key (fun _ -> option value)

let apply_ghost_map
  m k
= m k

let ghost_map_feq (#key #value: Type) (f1 f2: ghost_map key value) : Tot prop =
  FE.feq_g f1 f2

let ghost_map_feq_eq (#key #value: Type) (f1 f2: ghost_map key value) : Lemma
  (ensures (ghost_map_feq f1 f2 <==> f1 == f2))
  [SMTPat (ghost_map_feq f1 f2)]
= ()

let ghost_map_ext
  m1 m2
= ghost_map_feq_eq m1 m2

let ghost_map_equiv_intro
  (#key #value: Type) (f1 f2: ghost_map key value)
  (prf12: (x: (key * value)) -> Lemma (requires ghost_map_mem x f1) (ensures ghost_map_mem x f2))
  (prf21: (x: (key * value)) -> Lemma (requires ghost_map_mem x f2) (ensures ghost_map_mem x f1))
: Lemma
  (f1 == f2)
= let prf x y : Lemma (f1 x == Some y <==> f2 x == Some y) =
    let xy = (x, y) in
    Classical.move_requires prf12 xy;
    Classical.move_requires prf21 xy;
    assert (ghost_map_mem xy f1 <==> ghost_map_mem xy f2)
  in
  Classical.forall_intro_2 prf;
  assert (FE.feq_g f1 f2)


let ghost_map_equiv_intro'
  (#key #value: Type) (f1 f2: ghost_map key value)
  (prf: (x: (key * value)) -> Lemma (ghost_map_mem x f1 <==> ghost_map_mem x f2))
: Lemma
  (f1 == f2)
= ghost_map_equiv_intro f1 f2 (fun x -> prf x) (fun x -> prf x)

#restart-solver
let ghost_map_equiv (#key #value: Type) (f1 f2: ghost_map key value) : Lemma
  (requires (forall kv . ghost_map_mem kv f1 <==> ghost_map_mem kv f2))
  (ensures f1 == f2)
= ghost_map_equiv_intro' f1 f2 (fun _ -> ())

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

let ghost_map_empty (#key #value: Type) : Tot (ghost_map key value) =
  FE.on_dom_g _ (fun _ -> None)

let apply_ghost_map_empty k = ()

let ghost_map_singleton (#key #value: Type) (k: key) (v: value) : Tot (ghost_map key value) =
  FE.on_dom_g _ (fun k' ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
    then Some v
    else None
  )

let apply_ghost_map_singleton k v k' = ()

let ghost_map_union (#key #value: Type) (m1 m2: ghost_map key value) : Tot (ghost_map key value) =
  FE.on_dom_g _ (fun k' ->
    let res1 = m1 k' in
    if Some? res1
    then res1
    else m2 k'
  )

let apply_ghost_map_union m1 m2 k = ()

let ghost_map_disjoint_union (#key #value: Type) (m1 m2: ghost_map key value) : Lemma
  (requires ghost_map_disjoint m1 m2)
  (ensures m1 `ghost_map_union` m2 == m2 `ghost_map_union` m1)
= assert ((m1 `ghost_map_union` m2) `FE.feq_g` (m2 `ghost_map_union` m1))

#restart-solver
let map_group_item_post_prop
  (l: cbor_map)
  (l': (ghost_map Cbor.raw_data_item Cbor.raw_data_item & list (Cbor.raw_data_item & Cbor.raw_data_item)))
: Lemma
  (requires (map_group_item_post l l'))
  (ensures (
    List.Tot.no_repeats_p (List.Tot.map fst (snd l')) /\
    (forall xy . ~ (ghost_map_mem xy (fst l') /\ List.Tot.memP xy (snd l'))) /\
    (forall x . Cbor.list_ghost_assoc x l == begin match fst l' x with
    | Some y -> Some y
    | None -> Cbor.list_ghost_assoc x (snd l')
    end) /\
    (forall x . Cbor.list_ghost_assoc x l == begin match Cbor.list_ghost_assoc x (snd l') with
    | Some y -> Some y
    | None -> fst l' x
    end)
  ))
  [SMTPat (map_group_item_post l l')]
= 
  list_map_is_sublist_of fst (snd l') l;
  list_no_repeats_p_is_sublist_of (List.Tot.map fst (snd l')) (List.Tot.map fst l);
  assert ( 
    List.Tot.no_repeats_p (List.Tot.map fst (snd l'))
  );
  Classical.forall_intro (fun x -> List.Tot.memP_map_intro fst x (snd l'));
  assert
    (forall xy . ~ (ghost_map_mem xy (fst l') /\ List.Tot.memP xy (snd l')));
  let prf xv : Lemma
    (let (x, v) = xv in Cbor.list_ghost_assoc x l == Some v <==> (ghost_map_mem (x, v) (fst l') \/ (Cbor.list_ghost_assoc x (snd l') == Some v /\ ~ (ghost_map_defined x (fst l')))))
  = let (x, v) = xv in
    list_ghost_assoc_memP x (snd l');
    list_ghost_assoc_memP_strong x v l;
    list_ghost_assoc_memP_strong x v (snd l')
  in
  let prf2 x : Lemma (Cbor.list_ghost_assoc x l == begin match fst l' x with
    | Some y -> Some y
    | None -> Cbor.list_ghost_assoc x (snd l')
  end) =
    match Cbor.list_ghost_assoc x l with
    | Some v -> prf (x, v)
    | _ -> match fst l' x with
          | Some v -> prf (x, v)
          | _ -> match Cbor.list_ghost_assoc x (snd l') with
                 | Some v -> prf (x, v)
                 | _ -> ()
  in
  Classical.forall_intro prf2;
  assert (forall x . Cbor.list_ghost_assoc x l == begin match fst l' x with
    | Some y -> Some y
    | None -> Cbor.list_ghost_assoc x (snd l')
  end);
  let prf3 x : Lemma (Cbor.list_ghost_assoc x l == begin match Cbor.list_ghost_assoc x (snd l') with
    | Some y -> Some y
    | None -> fst l' x
  end) =
    match Cbor.list_ghost_assoc x (snd l') with
          | Some v ->
            list_ghost_assoc_memP x (snd l');
            assert (~ (ghost_map_defined x (fst l'))); prf (x, v)
          | _ -> match fst l' x with
                 | Some v -> prf (x, v)
                 | _ -> ()
  in
  Classical.forall_intro prf3;
  assert (forall x . Cbor.list_ghost_assoc x l == begin match Cbor.list_ghost_assoc x (snd l') with
    | Some y -> Some y
    | None -> fst l' x
  end)

let map_group_post
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
  (res: FStar.GSet.set _)
: Tot prop
=
      forall l' .
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

let map_group_codom
  (l: cbor_map)
: Tot Type0
= (res: FStar.GSet.set _ {
      map_group_post l res
  })

let map_group : Type0 =
  FE.restricted_g_t
    (cbor_map)
    (map_group_codom)

let map_group_always_false : map_group =
  FE.on_dom_g cbor_map #map_group_codom
    (fun _ -> FStar.GSet.empty)

let map_group_nop : map_group =
  FE.on_dom_g cbor_map #map_group_codom
    (fun l -> FStar.GSet.singleton (ghost_map_empty, l))

let map_group_end : map_group =
  FE.on_dom_g cbor_map #map_group_codom
    (fun l -> if Nil? l then map_group_nop l else map_group_always_false l)

let map_group_match_item_witness_pred (key value: typ) (l: list (Cbor.raw_data_item & Cbor.raw_data_item)) (l': (ghost_map Cbor.raw_data_item Cbor.raw_data_item & list (Cbor.raw_data_item & Cbor.raw_data_item))) (x: (list (Cbor.raw_data_item & Cbor.raw_data_item) & (Cbor.raw_data_item & Cbor.raw_data_item) & list (Cbor.raw_data_item & Cbor.raw_data_item))) : Tot prop =
  let (l1, (k, v), l2) = x in
      l == l1 `List.Tot.append` ((k, v) :: l2) /\
      fst l' == ghost_map_singleton k v /\
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
  Classical.forall_intro (List.Tot.append_memP l1 (kv :: l2));
  Classical.forall_intro (List.Tot.append_memP l1 l2);
  assert (forall x . (ghost_map_mem x (fst l') \/ List.Tot.memP x (snd l')) <==> List.Tot.memP x l);
  List.Tot.map_append fst l1 (kv :: l2);
  List.Tot.map_append fst l1 l2;
  Classical.forall_intro (list_memP_map fst (l1 `List.Tot.append` (kv :: l2)));
  Classical.forall_intro (list_memP_map fst (l1 `List.Tot.append` l2));
  List.Tot.no_repeats_p_append_permut [] [] (List.Tot.map fst l1) [fst kv] (List.Tot.map fst l2);
  assert (forall x . ~ (ghost_map_defined x (fst l') /\ List.Tot.memP x (List.Tot.map fst (snd l'))))

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
    FStar.GSet.union (FStar.GSet.singleton (ghost_map_singleton (fst x) (snd x), l1 `List.Tot.append` l2)) (gset_map (map_group_match_item_alt_r (l1 `List.Tot.append` [x])) (map_group_match_item key value l2))

#push-options "--z3rlimit 32"

#restart-solver
let map_group_match_item_alt_map_group_match_item
  (key value: typ) (l: cbor_map) l'
: Lemma
  (FStar.GSet.mem l' (map_group_match_item_alt key value l) ==> FStar.GSet.mem l' (map_group_match_item key value l))
= if FStar.GSet.mem l' (map_group_match_item_alt key value l)
  then begin
    let Some (l1, x, l2) = list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry key value)) l in
    if FStar.StrongExcludedMiddle.strong_excluded_middle (l' == (ghost_map_singleton (fst x) (snd x), l1 `List.Tot.append` l2))
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
      let mx' = ghost_map_singleton (fst x') (snd x') in
      assert (map_group_match_item_witness_pred key value lr (mx', lp `List.Tot.append` lr') (lp, x', lr'));
      List.Tot.append_assoc (ll `List.Tot.append` [x]) lp lr';
      assert (gset_map_witness_pred (map_group_match_item_alt_r (ll `List.Tot.append` [x])) (map_group_match_item key value lr) l' (mx', lp `List.Tot.append` lr'))
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
    else map_group_always_false l
  )

let map_group_concat_witness_pred
  (m1 m2: map_group)
  (l: cbor_map)
  (l': (ghost_map Cbor.raw_data_item Cbor.raw_data_item & list (Cbor.raw_data_item & Cbor.raw_data_item)))
  (l1l2: (ghost_map Cbor.raw_data_item Cbor.raw_data_item & list (Cbor.raw_data_item & Cbor.raw_data_item)) & (ghost_map Cbor.raw_data_item Cbor.raw_data_item & list (Cbor.raw_data_item & Cbor.raw_data_item)))
: Tot prop
= let (l1, l2) = l1l2 in
  FStar.GSet.mem l1 (m1 l) /\
  FStar.GSet.mem l2 (m2 (snd l1)) /\
  fst l' `ghost_map_feq` (fst l1 `ghost_map_union` fst l2) /\
  snd l' == snd l2

let ghost_map_disjoint_union_included_in_list
  (#key #value: Type)
  (f1 f2: ghost_map key value)
  (l: list (key & value))
: Lemma
  (requires (
    (forall x . ~ (ghost_map_defined x f1 /\ List.Tot.memP x (List.Tot.map fst l))) /\
    (forall x . ghost_map_mem x f2 ==> List.Tot.memP x l)
  ))
  (ensures (
    ghost_map_disjoint f1 f2
  ))
= let prf x : Lemma (ghost_map_defined x f2 ==> List.Tot.memP x (List.Tot.map fst l))
  = if Some? (f2 x)
    then begin
      let Some v = f2 x in
      List.Tot.memP_map_intro fst (x, v) l
    end
  in
  Classical.forall_intro prf

#push-options "--z3rlimit 16"

#restart-solver
let map_group_concat_witness_pred_correct
  (m1 m2: map_group)
  (l: cbor_map)
  (l': (ghost_map Cbor.raw_data_item Cbor.raw_data_item & list (Cbor.raw_data_item & Cbor.raw_data_item)))
  (l1l2: (ghost_map Cbor.raw_data_item Cbor.raw_data_item & list (Cbor.raw_data_item & Cbor.raw_data_item)) & (ghost_map Cbor.raw_data_item Cbor.raw_data_item & list (Cbor.raw_data_item & Cbor.raw_data_item)))
: Lemma
  (requires map_group_concat_witness_pred m1 m2 l l' l1l2)
  (ensures map_group_item_post l l' /\
    fst (fst l1l2) `ghost_map_disjoint` fst (snd l1l2))
  [SMTPat (map_group_concat_witness_pred m1 m2 l l' l1l2)]
= let (l1, l2) = l1l2 in
  assert (snd l' `is_sublist_of` l);
  ghost_map_disjoint_union_included_in_list (fst l1) (fst l2) (snd l1);
  assert (fst l1 `ghost_map_disjoint` fst l2);
  ghost_map_disjoint_mem_union' (fst l1) (fst l2) ();
  assert (forall x . (ghost_map_mem x (fst l') \/ List.Tot.memP x (snd l')) <==> List.Tot.memP x l);
  Classical.forall_intro (list_memP_map fst l);
  Classical.forall_intro (list_memP_map fst (snd l1));
  Classical.forall_intro (list_memP_map fst (snd l2));
  assert (forall x . ~ (ghost_map_defined x (fst l') /\ List.Tot.memP x (List.Tot.map fst (snd l'))))

#pop-options

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

let map_group_equiv_intro_equiv
  (m1 m2: map_group)
  (prf: (l: cbor_map) ->
    (l': _) ->
    Lemma
    (FStar.GSet.mem l' (m1 l) <==> FStar.GSet.mem l' (m2 l))
  )
: Lemma
  (map_group_equiv m1 m2)
= map_group_equiv_intro m1 m2 (fun l l' -> prf l l') (fun l l' -> prf l l')

let map_group_equiv_intro_equiv_rec
  (m1 m2: map_group)
  (prf: (l: cbor_map) ->
    (prf: (
      (l1: cbor_map { List.Tot.length l1 < List.Tot.length l }) -> Lemma
      (m1 l1 == m2 l1)
    )) ->
    (l': _) ->
    Lemma
    (FStar.GSet.mem l' (m1 l) <==> FStar.GSet.mem l' (m2 l))
  )
: Lemma
  (map_group_equiv m1 m2)
= let rec prf' (l: cbor_map) (l': _) : Lemma
    (ensures FStar.GSet.mem l' (m1 l) <==> FStar.GSet.mem l' (m2 l))
    (decreases (List.Tot.length l))
  = prf l (fun l1 ->
      Classical.forall_intro (prf' l1);
      prf' l1 l'; assert (m1 l1 `FStar.GSet.equal` m2 l1)
    )
    l'
  in
  map_group_equiv_intro_equiv m1 m2 prf'

let map_group_equiv_intro_rec
  (m1 m2: map_group)
  (prf12: (l: cbor_map) ->
    (prf: (
      (l1: cbor_map { List.Tot.length l1 < List.Tot.length l }) -> Lemma
      (m1 l1 == m2 l1)
    )) ->
    (l': _) ->
    Lemma
    (requires FStar.GSet.mem l' (m1 l))
    (ensures FStar.GSet.mem l' (m2 l))
  )
  (prf21: (l: cbor_map) ->
    (prf: (
      (l1: cbor_map { List.Tot.length l1 < List.Tot.length l }) -> Lemma
      (m1 l1 == m2 l1)
    )) ->
    (l': _) ->
    Lemma
    (requires FStar.GSet.mem l' (m2 l))
    (ensures FStar.GSet.mem l' (m1 l))
  )
: Lemma
  (map_group_equiv m1 m2)
= map_group_equiv_intro_equiv_rec m1 m2 (fun l prf l' ->
    Classical.move_requires (prf12 l prf) l';
    Classical.move_requires (prf21 l prf) l'
  )

let ghost_map_disjoint_union_assoc_domain
  (#key #value: Type)
  (f1 f2 f3: ghost_map key value)
: Lemma
  (ensures (
    (f1 `ghost_map_disjoint` f2 /\ (f1 `ghost_map_union` f2) `ghost_map_disjoint` f3) <==>
      (f2 `ghost_map_disjoint` f3 /\ f1 `ghost_map_disjoint` (f2 `ghost_map_union` f3))
  ))
= ()

let ghost_map_disjoint_union_assoc
  (#key #value: Type)
  (f1 f2 f3: ghost_map key value)
: Lemma
  (requires
      (f1 `ghost_map_disjoint` f2 /\ (f1 `ghost_map_union` f2) `ghost_map_disjoint` f3) \/
      (f2 `ghost_map_disjoint` f3 /\ f1 `ghost_map_disjoint` (f2 `ghost_map_union` f3))
  )
  (ensures
    (f1 `ghost_map_union` (f2 `ghost_map_union` f3) == (f1 `ghost_map_union` f2) `ghost_map_union` f3)
  )
= assert ((f1 `ghost_map_union` (f2 `ghost_map_union` f3)) `FE.feq_g` ((f1 `ghost_map_union` f2) `ghost_map_union` f3))

#push-options "--z3rlimit 16"

#restart-solver
let map_group_concat_assoc' (m1 m2 m3: map_group) : Lemma
  (map_group_concat m1 (map_group_concat m2 m3) `map_group_equiv` map_group_concat (map_group_concat m1 m2) m3)
= map_group_equiv_intro
    (map_group_concat m1 (map_group_concat m2 m3))
    (map_group_concat (map_group_concat m1 m2) m3)
    (fun l l' -> 
      let (l1, l23) = map_group_concat_elim m1 (map_group_concat m2 m3) l l' in
      ghost_map_disjoint_mem_union' (fst l1) (fst l23) ();
      let (l2, l3) = map_group_concat_elim m2 m3 (snd l1) l23 in
      ghost_map_disjoint_mem_union' (fst l2) (fst l3) ();
      assert (FStar.GSet.mem l1 (m1 l));
      assert (FStar.GSet.mem l2 (m2 (snd l1)));
      assert (FStar.GSet.mem l3 (m3 (snd l2)));
      let l12 = (fst l1 `ghost_map_union` fst l2, snd l2) in
      ghost_map_disjoint_mem_union' (fst l1) (fst l2) ();
      assert (map_group_concat_witness_pred m1 m2 l l12 (l1, l2));
      ghost_map_disjoint_union_assoc (fst l1) (fst l2) (fst l3);
      ghost_map_disjoint_mem_union' (fst l12) (fst l3) ();
      assert (map_group_concat_witness_pred (map_group_concat m1 m2) m3 l l' (l12, l3))
    )
    (fun l l' ->
      let (l12, l3) = map_group_concat_elim (map_group_concat m1 m2) m3 l l' in
      ghost_map_disjoint_mem_union' (fst l12) (fst l3) ();
      let (l1, l2) = map_group_concat_elim m1 m2 l l12 in
      ghost_map_disjoint_mem_union' (fst l1) (fst l2) ();
      let l23 = (fst l2 `ghost_map_union` fst l3, snd l3) in
      ghost_map_disjoint_mem_union' (fst l2) (fst l3) ();
      assert (map_group_concat_witness_pred m2 m3 (snd l1) l23 (l2, l3));
      ghost_map_disjoint_union_assoc (fst l1) (fst l2) (fst l3);
      ghost_map_disjoint_mem_union' (fst l1) (fst l23) ();
      assert (map_group_concat_witness_pred m1 (map_group_concat m2 m3) l l' (l1, l23))
    )

#pop-options

let map_group_concat_assoc m1 m2 m3 =
  map_group_concat_assoc' m1 m2 m3

let map_group_mk_cut_gen (cut: (Cbor.raw_data_item & Cbor.raw_data_item) -> bool) : map_group =
  FE.on_dom_g cbor_map #map_group_codom (fun l -> 
    if List.Tot.for_all cut l
    then map_group_nop l
    else map_group_always_false l
  )

#restart-solver
let map_group_concat_nop_l
  (m: map_group)
: Lemma
  (map_group_concat map_group_nop m == m)
= map_group_equiv_intro
    (map_group_concat map_group_nop m)
    m
    (fun l l' ->
      let (l1, l2) = map_group_concat_elim map_group_nop m l l' in
      assert (fst l' `ghost_map_feq` fst l2)
    )
    (fun l l' ->
      assert (map_group_concat_witness_pred map_group_nop m l l' ((ghost_map_empty, l), l'))
    )

let map_group_concat_nop_r
  (m: map_group)
: Lemma
  (map_group_concat m map_group_nop == m)
= map_group_equiv_intro
    (map_group_concat m map_group_nop)
    m
    (fun l l' ->
      let (l1, l2) = map_group_concat_elim m map_group_nop l l' in
      assert (fst l' `ghost_map_feq` fst l1)
    )
    (fun l l' -> 
      assert (map_group_concat_witness_pred m map_group_nop l l' (l', (ghost_map_empty, snd l')))
    )

#restart-solver
let map_group_cut_eq
  (cut: typ)
  (m: map_group)
: Lemma
  (map_group_cut cut m == (map_group_mk_cut cut `map_group_concat` m))
= map_group_concat_nop_l m;
  map_group_equiv_intro
    (map_group_cut cut m)
    (map_group_mk_cut cut `map_group_concat` m)
    (fun l l' -> ())
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
    (fun l -> if List.Tot.length l >= List.Tot.length l0 then map_group_nop l else m l)

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
  then map_group_nop l
  else map_group_concat m (bound_map_group l (map_group_zero_or_more' m)) l

let map_group_zero_or_more m =
  FE.on_dom_g cbor_map #map_group_codom (map_group_zero_or_more' m)

let map_group_zero_or_more_eq
  (m: map_group)
  (l: cbor_map)
: Lemma
  (ensures (map_group_zero_or_more m l == (let res1 = m l in
    if FStar.StrongExcludedMiddle.strong_excluded_middle (res1 == FStar.GSet.empty)
    then map_group_nop l
    else map_group_concat m (bound_map_group l (map_group_zero_or_more m)) l
  )))
  (decreases (List.Tot.length l))
= assert (forall l . map_group_zero_or_more m l == map_group_zero_or_more' m l);
  assert_norm (map_group_zero_or_more' m l == (let res1 = m l in
    if FStar.StrongExcludedMiddle.strong_excluded_middle (res1 == FStar.GSet.empty)
    then map_group_nop l
    else map_group_concat m (bound_map_group l (map_group_zero_or_more' m)) l
  ));
  bound_map_group_ext l (map_group_zero_or_more m) (map_group_zero_or_more' m)

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
    | Some (ll, kv, lr) -> FStar.GSet.singleton (ghost_map_singleton (fst kv) (snd kv), ll `List.Tot.append` lr)
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

let map_group_match_item_length
  (key value: typ)
  (l: cbor_map)
  l'
: Lemma
  (requires FStar.GSet.mem l' (map_group_match_item key value l))
  (ensures List.Tot.length (snd l') < List.Tot.length l)
  [SMTPat (FStar.GSet.mem l' (map_group_match_item key value l))]
= let (l1, kv, l2) = FStar.IndefiniteDescription.indefinite_description_ghost _ (map_group_match_item_witness_pred key value l l') in
  List.Tot.append_length l1 (kv :: l2);
  List.Tot.append_length l1 l2

let ghost_map_filter
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m: ghost_map key value)
: ghost_map key value
= FE.on_dom_g _ (fun k ->
    match m k with
    | Some v -> if f (k, v) then Some v else None
    | None -> None
  )

let apply_ghost_map_filter
  f m k
= ()

let ghost_map_of_list
  (#key #value: Type)
  (l: list (key & value))
: ghost_map key value
= FE.on_dom_g _ (fun k -> Cbor.list_ghost_assoc k l)

let apply_ghost_map_of_list
  l k
= ()

let ghost_map_of_list_singleton
  (#key #value: Type)
  (kv: (key & value))
: Lemma
  (ghost_map_of_list [kv] == ghost_map_singleton (fst kv) (snd kv))
  [SMTPat (ghost_map_of_list [kv])]
= assert (ghost_map_of_list [kv] `ghost_map_feq` ghost_map_singleton (fst kv) (snd kv))

let rec list_ghost_assoc_append
  (#key #value: Type)
  (l1 l2: list (key & value))
  (x: key)
: Lemma
  (ensures (Cbor.list_ghost_assoc x (l1 `List.Tot.append` l2) == begin match Cbor.list_ghost_assoc x l1 with
  | Some v -> Some v
  | None -> Cbor.list_ghost_assoc x l2
  end))
  (decreases l1)
= match l1 with
  | [] -> ()
  | _ :: q -> list_ghost_assoc_append q l2 x

let ghost_map_of_list_append
  (#key #value: Type)
  (l1 l2: list (key & value))
: Lemma
  (ghost_map_of_list (List.Tot.append l1 l2) == ghost_map_of_list l1 `ghost_map_union` ghost_map_of_list l2)
= Classical.forall_intro (list_ghost_assoc_append l1 l2);
  assert
    (ghost_map_of_list (List.Tot.append l1 l2) `ghost_map_feq`
      (ghost_map_of_list l1 `ghost_map_union` ghost_map_of_list l2))

let ghost_map_of_list_mem_gen
  (#key #value: Type)
  (l: list (key & value))
  (prf: squash (List.Tot.no_repeats_p (List.Tot.map fst l)))
  (x: (key & value))
: Lemma
  (ghost_map_mem x (ghost_map_of_list l) <==> List.Tot.memP x l)
= list_ghost_assoc_memP_strong (fst x) (snd x) l

let list_filter_memP
  (#t: Type)
  (f: t -> bool)
  (l: list t)
  (x: t)
: Lemma
  (List.Tot.memP x (List.Tot.filter f l) <==> (List.Tot.memP x l /\ f x))
= ()

let ghost_map_filter_of_list
  (f: _ -> bool)
  (l: cbor_map)
: Lemma
  (ghost_map_filter f (ghost_map_of_list l) == ghost_map_of_list (List.Tot.filter f l))
= ghost_map_equiv_intro'
    (ghost_map_filter f (ghost_map_of_list l))
    (ghost_map_of_list (List.Tot.filter f l))
    (fun (k, v) -> 
      list_ghost_assoc_memP_strong k v l;
      list_filter_memP f l (k, v);
      list_ghost_assoc_memP_strong k v (List.Tot.filter f l)
    )

let rec list_for_all_not_implies_filter
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (l: list (key & value))
: Lemma
  (requires (List.Tot.for_all (notp (FStar.Ghost.Pull.pull f)) l))
  (ensures (ghost_map_filter f (ghost_map_of_list l) `ghost_map_feq` ghost_map_empty))
= match l with
  | [] -> ()
  | _ :: q -> list_for_all_not_implies_filter f q

#restart-solver
let gset_is_empty
  (#t: Type)
  (s: FStar.GSet.set t)
: Ghost (option t)
    (requires True)
    (ensures fun res -> 
    (None? res <==> s == FStar.GSet.empty) /\
    begin match res with
    | None -> True
    | Some x -> FStar.GSet.mem x s
    end
    )
= if FStar.StrongExcludedMiddle.strong_excluded_middle (exists x . FStar.GSet.mem x s)
  then Some (FStar.IndefiniteDescription.indefinite_description_ghost _ (fun x -> FStar.GSet.mem x s))
  else begin
    assert (s `FStar.GSet.equal` FStar.GSet.empty);
    None
  end

#restart-solver
let map_group_zero_or_more_zero_or_one_eq
  (m: map_group)
: Lemma
  (map_group_zero_or_more (map_group_zero_or_one m) == map_group_zero_or_more m)
=
  assert ((ghost_map_empty #Cbor.raw_data_item #Cbor.raw_data_item  `ghost_map_union` ghost_map_empty) `ghost_map_feq` ghost_map_empty);
  map_group_equiv_intro_rec
    (map_group_zero_or_more (map_group_zero_or_one m))
    (map_group_zero_or_more m)
    (fun l prf l' ->
      map_group_zero_or_more_eq (map_group_zero_or_one m) l;
      map_group_zero_or_more_eq m l;
      assert (~ (map_group_zero_or_one m l == FStar.GSet.empty));
      Classical.forall_intro prf;
      bound_map_group_ext l (map_group_zero_or_more (map_group_zero_or_one m)) (map_group_zero_or_more m);
      let (l1, l2) = map_group_concat_elim (map_group_zero_or_one m) (bound_map_group l (map_group_zero_or_more m)) l l' in
      ()
    )
    (fun l prf l' ->
      map_group_zero_or_more_eq (map_group_zero_or_one m) l;
      map_group_zero_or_more_eq m l;
      assert (~ (map_group_zero_or_one m l == FStar.GSet.empty));
      Classical.forall_intro prf;
      bound_map_group_ext l (map_group_zero_or_more (map_group_zero_or_one m)) (map_group_zero_or_more m);
      match gset_is_empty (m l) with
      | None ->
        assert (map_group_concat_witness_pred (map_group_zero_or_one m) (bound_map_group l (map_group_zero_or_more m)) l l'
          (
            (ghost_map_empty, l),
            (ghost_map_empty, l)
          )
        )
      | _ -> 
        let (l1, l2) = map_group_concat_elim m (bound_map_group l (map_group_zero_or_more m)) l l' in
        ()
    )

let apply_map_group_det (m: map_group) (l: cbor_map) : Pure map_group_result
  (requires True)
  (ensures fun r -> map_group_result_prop l r)
= let s = m l in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (s == FStar.GSet.empty)
  then MapGroupFail
  else if FStar.StrongExcludedMiddle.strong_excluded_middle (exists x . s == FStar.GSet.singleton x)
  then
    let x = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun x -> s == FStar.GSet.singleton x) in
    MapGroupDet (fst x) (snd x)
  else MapGroupNonDet

#restart-solver
let apply_map_group_det_eq_singleton (m: map_group) (l: cbor_map) (x : (_ & list _)) : Lemma
  (requires (m l `FStar.GSet.equal` FStar.GSet.singleton x))
  (ensures (apply_map_group_det m l == MapGroupDet (fst x) (snd x)))
= let s = m l in
  assert (s == FStar.GSet.singleton x);
  if FStar.StrongExcludedMiddle.strong_excluded_middle (s == FStar.GSet.empty)
  then assert (x `FStar.GSet.mem` FStar.GSet.empty)
  else begin
    assert (exists x . s == FStar.GSet.singleton x);
    assert (MapGroupDet? (apply_map_group_det m l))
  end

#restart-solver
let apply_map_group_det_eq_map (m1 m2: map_group) (l: cbor_map) : Lemma
  (requires m1 l == m2 l)
  (ensures apply_map_group_det m1 l == apply_map_group_det m2 l)
= match apply_map_group_det m1 l with
  | MapGroupDet c1 l1 -> apply_map_group_det_eq_singleton m2 l (c1, l1)
  | _ -> ()

let apply_map_group_det_always_false (l: cbor_map) : Lemma
  (apply_map_group_det map_group_always_false l == MapGroupFail)
= ()

#restart-solver
let apply_map_group_det_nop (l: cbor_map) : Lemma
  (apply_map_group_det map_group_nop l == MapGroupDet ghost_map_empty l)
= ()

let apply_map_group_det_end (l: cbor_map) : Lemma
  (apply_map_group_det map_group_end l == (if Nil? l then MapGroupDet ghost_map_empty l else MapGroupFail))
= ()

let apply_map_group_det_map_group_equiv (m1 m2: map_group) : Lemma
  (requires
    (forall l . ~ (MapGroupNonDet? (apply_map_group_det m1 l))) /\
    (forall l . apply_map_group_det m1 l == apply_map_group_det m2 l)
  )
  (ensures m1 == m2)
= map_group_equiv_intro m1 m2
    (fun l l' ->
      let MapGroupDet _ s1 = apply_map_group_det m1 l in
      let (k1, l1) = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun s1 -> m1 l == FStar.GSet.singleton s1) in
      let (k2, l2) = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun s2 -> m2 l == FStar.GSet.singleton s2) in
      assert (l1 == l2);
      ghost_map_equiv k1 k2
    )
    (fun l l' ->
      let MapGroupDet _ s1 = apply_map_group_det m1 l in
      let (k1, l1) = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun s1 -> m1 l == FStar.GSet.singleton s1) in
      let (k2, l2) = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun s2 -> m2 l == FStar.GSet.singleton s2) in
      assert (l1 == l2);
      ghost_map_equiv k1 k2
    )

let gset_singleton_inj
  (#t: Type)
  (x1 x2: t)
: Lemma
  (requires FStar.GSet.singleton x1 == FStar.GSet.singleton x2)
  (ensures x1 == x2)
= assert (x1 `FStar.GSet.mem` FStar.GSet.singleton x2)

#restart-solver
let apply_map_group_det_choice (m1 m2: map_group) (l: cbor_map)
= match apply_map_group_det m1 l with
  | MapGroupFail -> apply_map_group_det_eq_map (m1 `map_group_choice` m2) m2 l
  | _ -> apply_map_group_det_eq_map (m1 `map_group_choice` m2) m1 l

#push-options "--z3rlimit 16"

#restart-solver
let apply_map_group_det_concat (m1 m2: map_group) (l: cbor_map)
= match apply_map_group_det m1 l with
  | MapGroupFail ->
    assert (map_group_concat m1 m2 l `FStar.GSet.equal` FStar.GSet.empty)
  | MapGroupDet c1 lr1 ->
    let l1 = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun x -> m1 l == FStar.GSet.singleton x) in
    begin match apply_map_group_det m2 lr1 with
    | MapGroupFail -> assert (map_group_concat m1 m2 l `FStar.GSet.equal` FStar.GSet.empty)
    | MapGroupDet c2 lr2 ->
      let l2 = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun x -> m2 lr1 == FStar.GSet.singleton x) in
      let l0 = (ghost_map_union (fst l1) (fst l2), snd l2) in
      gset_equal_intro
        (map_group_concat m1 m2 l)
        (FStar.GSet.singleton l0)
        (fun _ -> ())
        (fun _ ->
          assert (map_group_concat_witness_pred m1 m2 l l0
            (l1, l2)
          )
        )
    | MapGroupNonDet ->
      let Some l2 = gset_is_empty (m2 lr1) in
      let l0 = (ghost_map_union (fst l1) (fst l2), snd l2) in
      assert (map_group_concat_witness_pred m1 m2 l l0
        (l1, l2)
      );
      assert (FStar.GSet.mem l0 (map_group_concat m1 m2 l));
      assert (~ (map_group_concat m1 m2 l == FStar.GSet.empty));
      if FStar.StrongExcludedMiddle.strong_excluded_middle (exists x . map_group_concat m1 m2 l == FStar.GSet.singleton x)
      then begin
        assert (map_group_concat m1 m2 l `FStar.GSet.equal` FStar.GSet.singleton l0);
        gset_equal_intro
          (m2 lr1)
          (FStar.GSet.singleton l2)
          (fun l2' ->
            let l0' = (ghost_map_union (fst l1) (fst l2'), snd l2') in
            assert (map_group_concat_witness_pred m1 m2 l l0'
              (l1, l2')
            );
            assert (FStar.GSet.mem l0' (map_group_concat m1 m2 l));
            assert (l0' == l0);
            ghost_map_disjoint_mem_union' (fst l1) (fst l2') ();
            ghost_map_disjoint_mem_union' (fst l1) (fst l2) ();
            ghost_map_equiv (fst l2') (fst l2);
            assert (l2' == l2)
          )
          (fun _ -> ())
      end
      else ()
    end
  | _ -> ()

#pop-options

let apply_map_group_det_mk_cut_gen
  (cut: (Cbor.raw_data_item & Cbor.raw_data_item) -> bool)
  (l: cbor_map)
: Lemma
  (apply_map_group_det (map_group_mk_cut_gen cut) l == (
    if List.Tot.for_all cut l
    then MapGroupDet ghost_map_empty l
    else MapGroupFail
  ))
= ()

#restart-solver
let apply_map_group_det_match_item_for
  (k: Cbor.raw_data_item)
  (ty: typ)
  (l: cbor_map)
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
      (ghost_map_singleton (fst kv) (snd kv),
        List.Tot.filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry (t_literal k) ty))) l)

// FIXME: swap `notp f` with `f`?
let map_group_filter_item
  (f: (Cbor.raw_data_item & Cbor.raw_data_item) -> bool)
  (l: cbor_map)
: GTot (ghost_map Cbor.raw_data_item Cbor.raw_data_item & list (Cbor.raw_data_item & Cbor.raw_data_item))
=
  ghost_map_filter (notp f) (ghost_map_of_list l),
    List.Tot.filter f l

let map_group_item_post_filter
  (f: (Cbor.raw_data_item & Cbor.raw_data_item) -> bool)
  (l: cbor_map)
: Lemma
  (map_group_item_post l (map_group_filter_item f l))
  [SMTPat (map_group_filter_item f l)]
= let l' = map_group_filter_item f l in
  assert (snd l' `is_sublist_of` l);
  ghost_map_filter_of_list (notp f) l;
  list_ghost_assoc_memP_strong' l ();
  assert (forall x . (ghost_map_mem x (fst l') \/ List.Tot.memP x (snd l')) <==> List.Tot.memP x l);
  Classical.forall_intro (list_memP_map fst l);
  Classical.forall_intro (list_memP_map fst (snd l'));
  assert (forall x . ~ (ghost_map_defined x (fst l') /\ List.Tot.memP x (List.Tot.map fst (snd l'))))

let map_group_filter
  f
= FE.on_dom_g cbor_map #map_group_codom (fun l ->
    FStar.GSet.singleton (map_group_filter_item f l)
  )

let apply_map_group_det_filter
  f l
= apply_map_group_det_eq_singleton (map_group_filter f) l (map_group_filter_item f l)

let orp (#t: Type) (p1 p2: t -> bool) (x: t) : bool =
  p1 x || p2 x

let ghost_map_filter_union
  (#key #value: Type)
  (p1 p2: (key & value) -> bool)
  (m: ghost_map key value)
: Lemma
  (ghost_map_filter p1 m `ghost_map_union`
    ghost_map_filter p2 m ==
    ghost_map_filter (p1 `orp` p2) m
  )
= ghost_map_feq_eq
    (ghost_map_filter p1 m `ghost_map_union`
      ghost_map_filter p2 m)
    (ghost_map_filter (p1 `orp` p2) m)

let ghost_map_filter_not_filter_not_strong
  (p1 p2: (Cbor.raw_data_item & Cbor.raw_data_item) -> bool)
  (l: cbor_map)
: Lemma
  (ghost_map_filter (notp p1) (ghost_map_of_list l) `ghost_map_union`
    ghost_map_filter (notp p2) (ghost_map_of_list (List.Tot.filter p1 l)) ==
    ghost_map_filter (notp (p1 `andp` p2)) (ghost_map_of_list l)
  )
= ghost_map_filter_of_list (notp p2) (List.Tot.filter p1 l);
  list_filter_filter p1 (notp p2) l;
  ghost_map_filter_of_list (p1 `andp` notp p2) l;
  ghost_map_filter_union (notp p1) (p1 `andp` notp p2) (ghost_map_of_list l);
  ghost_map_filter_ext
    (notp p1 `orp` (p1 `andp` notp p2))
    (notp (p1 `andp` p2))
    (ghost_map_of_list l)

let map_group_filter_filter
  p1 p2
= Classical.forall_intro (list_filter_filter p1 p2);
  Classical.forall_intro (ghost_map_filter_not_filter_not_strong p1 p2);
  apply_map_group_det_map_group_equiv
    (map_group_filter p1 `map_group_concat` map_group_filter p2)
    (map_group_filter (andp p1 p2))

let list_filter_implies_2' (#t: Type) (p1 p2: t -> bool) : Lemma
  (requires (forall (x: t) . p1 x ==> p2 x))
  (ensures forall  (l: list t) . List.Tot.filter p1 (List.Tot.filter p2 l) == List.Tot.filter p1 l)
= Classical.forall_intro (fun l -> Classical.move_requires (list_filter_implies_2 p1 p2) l)

let list_memP_equiv_map_no_repeats
  (#key #value: Type)
  (l1 l2: list (key & value))
: Lemma
  (requires (
    List.Tot.no_repeats_p (List.Tot.map fst l1) /\
    (forall x . List.Tot.memP x l1 <==> List.Tot.memP x l2) /\
    List.Tot.length l1 >= List.Tot.length l2
  ))
  (ensures (
    List.Tot.length l1 == List.Tot.length l2 /\
    List.Tot.no_repeats_p (List.Tot.map fst l2)
  ))
= Classical.forall_intro (list_memP_map fst l1);
  Classical.forall_intro (list_memP_map fst l2);
  list_memP_equiv_no_repeats (List.Tot.map fst l1) (List.Tot.map fst l2)

let ghost_map_of_list_ext
  (#key #value: Type)
  (l1 l2: list (key & value))
: Lemma
  (requires (
    List.Tot.no_repeats_p (List.Tot.map fst l1) /\
    (forall x . List.Tot.memP x l1 <==> List.Tot.memP x l2) /\
    List.Tot.length l1 >= List.Tot.length l2
  ))
  (ensures (
    List.Tot.length l1 == List.Tot.length l2 /\
    List.Tot.no_repeats_p (List.Tot.map fst l2) /\
    ghost_map_of_list l1 == ghost_map_of_list l2
  ))
= list_memP_equiv_map_no_repeats l1 l2;
  Classical.forall_intro (ghost_map_of_list_mem_gen l1 ());
  Classical.forall_intro (ghost_map_of_list_mem_gen l2 ());
  ghost_map_equiv (ghost_map_of_list l1) (ghost_map_of_list l2)

#restart-solver
let map_group_zero_or_one_match_item_filter_matched
  (key value: typ)
  (p: (Cbor.raw_data_item & Cbor.raw_data_item) -> bool)
  (l: cbor_map)
  ll kv lr
: Lemma
  (requires (
    (forall x . p x ==> notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value)) x) /\
    l == ll `List.Tot.append` (kv :: lr) /\
    matches_map_group_entry key value kv
  ))
  (ensures (
    ghost_map_singleton (fst kv) (snd kv) `ghost_map_union` ghost_map_filter (notp p) (ghost_map_of_list (ll `List.Tot.append` lr)) ==
      ghost_map_filter (notp p) (ghost_map_of_list l)
  ))
= List.Tot.append_length ll (kv :: lr);
  List.Tot.append_length ll lr;
  Classical.forall_intro (List.Tot.append_memP ll (kv :: lr));
  Classical.forall_intro (List.Tot.append_memP ll lr);
  ghost_map_of_list_ext (ll `List.Tot.append` (kv :: lr)) (kv :: ll `List.Tot.append` lr);
  ghost_map_filter_of_list (notp p) l;
  ghost_map_filter_of_list (notp p) (kv :: ll `List.Tot.append` lr);
  list_filter_append (notp p) [kv] (ll `List.Tot.append` lr);
  ghost_map_of_list_append (List.Tot.filter (notp p) [kv]) (List.Tot.filter (notp p) (ll `List.Tot.append` lr));
  ghost_map_filter_of_list (notp p) (ll `List.Tot.append` lr)

#restart-solver
let map_group_zero_or_one_match_item_filter
  key value p
= map_group_equiv_intro
    (map_group_zero_or_one (map_group_match_item key value) `map_group_concat` map_group_filter p)
    (map_group_filter p)
    (fun l l' ->
      match gset_is_empty (map_group_match_item key value l) with
      | None -> map_group_concat_nop_l (map_group_filter p)
      | Some _ ->
        let (l1, _) = map_group_concat_elim (map_group_zero_or_one (map_group_match_item key value)) (map_group_filter p) l l' in
        let (ll, kv, lr) = map_group_match_item_elim key value l l1 in
        list_filter_append p ll (kv :: lr);
        list_filter_append p ll lr;
        assert (fst l1 == ghost_map_singleton (fst kv) (snd kv));
        assert (map_group_filter p (snd l1) == FStar.GSet.singleton (map_group_filter_item p (snd l1)));
        map_group_zero_or_one_match_item_filter_matched key value p l ll kv lr
    )
    (fun l l' ->
      match gset_is_empty (map_group_match_item key value l) with
      | None -> map_group_concat_nop_l (map_group_filter p)
      | Some l1 ->
        let (ll, kv, lr) = map_group_match_item_elim key value l l1 in
        list_filter_append p ll (kv :: lr);
        list_filter_append p ll lr;
        assert (snd l' == List.Tot.filter p (snd l1));
        map_group_zero_or_one_match_item_filter_matched key value p l ll kv lr;
        assert (map_group_concat_witness_pred (map_group_zero_or_one (map_group_match_item key value)) (map_group_filter p) l l' (l1, (ghost_map_filter (notp p) (ghost_map_of_list (ll `List.Tot.append` lr)), List.Tot.filter p (snd l1))))
    )

#push-options "--z3rlimit 32"

#restart-solver
let map_group_concat_bound_map_group_elim
  (m1 m2: map_group)
  (l1 l2: cbor_map)
  (prf: (l': _) -> Lemma
    (requires (FStar.GSet.mem l' (m1 l1)))
    (ensures (List.Tot.length (snd l') < List.Tot.length l2))
  )
: Lemma
  ((m1 `map_group_concat` bound_map_group l2 m2) l1 ==
    (m1 `map_group_concat` m2) l1)
= Classical.forall_intro (Classical.move_requires prf);
  assert ((m1 `map_group_concat` bound_map_group l2 m2) l1 `FStar.GSet.equal`
    (m1 `map_group_concat` m2) l1
  )

#pop-options

#restart-solver
let map_group_zero_or_one_bound_match_item_filter
  (key value: typ)
  (l: cbor_map)
: Lemma
  (ensures (
    let p = notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value)) in
    (map_group_zero_or_one (map_group_match_item key value) `map_group_concat` bound_map_group l (map_group_filter p)) l == map_group_filter p l
  ))
= let p = notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value)) in
  map_group_match_item_alt_correct key value l;
  match list_filter_and_extract (FStar.Ghost.Pull.pull (matches_map_group_entry key value)) l with
  | None ->
    assert (map_group_match_item key value l == FStar.GSet.empty);
    assert ((ghost_map_empty #Cbor.raw_data_item #Cbor.raw_data_item `ghost_map_union` ghost_map_empty) `ghost_map_feq` ghost_map_empty);
    list_for_all_implies_filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value))) l;
    List.Tot.for_all_mem (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value))) l;
    ghost_map_filter_of_list (notp p) l;
    Classical.forall_intro (ghost_map_of_list_mem (List.Tot.filter p l));
    Classical.forall_intro (list_filter_memP p l);
    ghost_map_equiv (ghost_map_filter (notp p) (ghost_map_of_list l)) ghost_map_empty;
    assert (map_group_filter p l `FStar.GSet.equal` FStar.GSet.singleton (ghost_map_empty, l));
    assert (
      ((map_group_zero_or_one (map_group_match_item key value) `map_group_concat` bound_map_group l (map_group_filter p)) l) `FStar.GSet.equal`
      ((map_group_nop `map_group_concat` bound_map_group l (map_group_filter p)) l)
    );
    map_group_concat_nop_l (bound_map_group l (map_group_filter p));
    assert (bound_map_group l (map_group_filter p) l `FStar.GSet.equal` 
      FStar.GSet.singleton (ghost_map_empty `ghost_map_union` ghost_map_empty, l)
    );
    assert (
      ((map_group_zero_or_one (map_group_match_item key value) `map_group_concat` bound_map_group l (map_group_filter p)) l) `FStar.GSet.equal`
      (map_group_filter p l)
    )
  | Some (ll, (k, v), lr) ->
    let l1 = (ghost_map_singleton k v, ll `List.Tot.append` lr) in
    assert (map_group_match_item_witness_pred key value l l1 (ll, (k, v), lr));
    assert (FStar.GSet.mem l1 (map_group_match_item key value l));
    assert (~ (map_group_match_item key value l == FStar.GSet.empty));
    map_group_concat_bound_map_group_elim (map_group_zero_or_one (map_group_match_item key value)) (map_group_filter p) l l (fun _ -> ());
    map_group_zero_or_one_match_item_filter key value p

#restart-solver
let map_group_zero_or_more_match_item_filter (key value: typ) : Lemma
  (ensures
    map_group_zero_or_more (map_group_match_item key value) == map_group_filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value)))
  )
= let f = (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value))) in
  map_group_equiv_intro_equiv_rec
    (map_group_zero_or_more (map_group_match_item key value))
    (map_group_filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value))))
    (fun l prf l' ->
      map_group_zero_or_more_zero_or_one_eq (map_group_match_item key value);
      map_group_zero_or_more_eq (map_group_zero_or_one (map_group_match_item key value)) l;
      assert (~ (map_group_zero_or_one (map_group_match_item key value) l == FStar.GSet.empty));
      Classical.forall_intro prf;
      bound_map_group_ext l (map_group_zero_or_more (map_group_match_item key value)) (map_group_filter f);
      map_group_zero_or_one_bound_match_item_filter key value l
    )

#restart-solver
let apply_map_group_det_zero_or_more_match_item
  (key value: typ)
  (l: cbor_map)
= map_group_zero_or_more_match_item_filter key value;
  ghost_map_filter_ext
    (matches_map_group_entry key value)
    (notp (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value))))
    (ghost_map_of_list l);
  apply_map_group_det_eq_singleton (map_group_zero_or_more (map_group_match_item key value)) l
    (
      ghost_map_filter (matches_map_group_entry key value) (ghost_map_of_list l),
      List.Tot.filter (notp (FStar.Ghost.Pull.pull (matches_map_group_entry key value))) l
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

#push-options "--z3rlimit 64"

#restart-solver
let map_group_zero_or_more_map_group_match_item_for
  (key: Cbor.raw_data_item)
  (value: typ)
: Lemma
  (map_group_zero_or_more (map_group_match_item_for key value) ==
    map_group_zero_or_one (map_group_match_item_for key value)
  )
= apply_map_group_det_map_group_equiv0
    (map_group_zero_or_more (map_group_match_item_for key value))
    (map_group_zero_or_one (map_group_match_item_for key value))
    (fun l -> ())
    (fun l ->
      Classical.move_requires (list_ghost_assoc_none_filter_matches_map_group_entry_for key value) l;
      let MapGroupDet c1 _ = apply_map_group_det (map_group_zero_or_more (map_group_match_item_for key value)) l in
      let MapGroupDet c2 _ = apply_map_group_det (map_group_zero_or_one (map_group_match_item_for key value)) l in
      assert (c1 `ghost_map_feq` c2)
    )

#pop-options

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
  FStar.StrongExcludedMiddle.strong_excluded_middle (exists gm .
    FStar.GSet.mem (gm, []) (g m)
  )

let matches_map_group_mem (g: map_group) (m: cbor_map) (gm: _) : Lemma
  (requires FStar.GSet.mem (gm, []) (g m))
  (ensures gm == ghost_map_of_list m)
  [SMTPat (FStar.GSet.mem (gm, []) (g m))]
= Classical.forall_intro (ghost_map_of_list_mem m);
  ghost_map_equiv gm (ghost_map_of_list m)

let matches_map_group_det (g: map_group) (m: cbor_map) : Lemma
  (match apply_map_group_det g m with
  | MapGroupFail -> ~ (matches_map_group g m)
  | MapGroupDet _ m' -> matches_map_group g m <==> m' == []
  | _ -> True)
= ()

let map_group_entry_consumed_prop
  (l: cbor_map)
  (entry: (Cbor.raw_data_item & Cbor.raw_data_item))
  (g: map_group)
  l'
: Tot prop
= FStar.GSet.mem l' (g l) /\ ghost_map_mem entry (fst l')

let map_group_entry_consumed
  (l: cbor_map)
  (entry: (Cbor.raw_data_item & Cbor.raw_data_item))
  (g: map_group)
: Tot prop
= exists l' . map_group_entry_consumed_prop l entry g l'

let map_group_entry_consumed_elim
  (l: cbor_map)
  (entry: (Cbor.raw_data_item & Cbor.raw_data_item))
  (g: map_group)
: Ghost _
    (requires (map_group_entry_consumed l entry g))
    (ensures fun l' -> map_group_entry_consumed_prop l entry g l')
= FStar.IndefiniteDescription.indefinite_description_ghost _ (fun l' -> map_group_entry_consumed_prop l entry g l')

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
    (exists l' . FStar.GSet.mem l' (g1 l) /\ map_group_entry_consumed (snd l') entry g2)
  )
= let l' = map_group_entry_consumed_elim l entry (g1 `map_group_concat` g2) in
  let (l1, l2) = map_group_concat_elim g1 g2 l l' in
  ()

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
    (let MapGroupDet _ l' = apply_map_group_det g1 l in map_group_entry_consumed l' entry g2)
  )
= map_group_entry_consumed_concat l entry g1 g2

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
  let (k, v) = kv in
  assert (map_group_match_item_witness_pred key value l (ghost_map_singleton k v, ll `List.Tot.append` lr) (ll, kv, lr))

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
= ()

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
