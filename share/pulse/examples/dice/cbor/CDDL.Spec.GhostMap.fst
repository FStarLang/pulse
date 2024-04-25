module CDDL.Spec.GhostMap
module FE = FStar.FunctionalExtensionality

let ghost_map'
  (key value: Type u#a)
: Type u#a
= FE.restricted_g_t key (fun _ -> option value)

let ghost_map_nil' (#key #value: Type u#a) : ghost_map' key value =
  FE.on_dom_g _ (fun _ -> None)

let ghost_map_cons' (#key #value: Type u#a) (k: key) (v: value) (g: ghost_map' key value) : ghost_map' key value =
  FE.on_dom_g _ (fun k' -> if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k') then Some v else g k')

let rec ghost_map_of_list'
  (#key #value: Type0)
  (l: list (key & value))
: Tot (ghost_map' key value)
= match l with
  | [] -> ghost_map_nil'
  | (k, v) :: q -> ghost_map_cons' k v (ghost_map_of_list' q)

let rec ghost_map_of_list'_assoc
  (#key #value: Type)
  (l: list (key & value))
  (k: key)
: Lemma
  (ghost_map_of_list' l k == Cbor.list_ghost_assoc k l)
  [SMTPat (ghost_map_of_list' l k)]
= match l with
  | [] -> ()
  | _ :: q -> ghost_map_of_list'_assoc q k

let ghost_map_pred
  (#key #value: Type0)
  (g: ghost_map' key value)
  (l: list (key & value))
: Tot prop
= g == ghost_map_of_list' l

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

let rec list_filter_eq_length
  (#t: Type)
  (f: t -> bool)
  (l: list t)
: Lemma
  (requires (List.Tot.length (List.Tot.filter f l) == List.Tot.length l))
  (ensures (List.Tot.filter f l == l))
= match l with
  | [] -> ()
  | a :: q -> list_length_filter f q; list_filter_eq_length f q

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
    list_length_filter (ghost_neq a) (ll `List.Tot.append` lr);
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

let ghost_map key value = (g: ghost_map' key value { exists l . ghost_map_pred g l })

let apply_ghost_map m k = m k

let ghost_map_ext m1 m2 =
  assert (FE.feq_g m1 m2)

let ghost_map_equiv f1 f2
= let prf x y : Lemma (f1 x == Some y <==> f2 x == Some y) =
    let xy = (x, y) in
    assert (ghost_map_mem xy f1 <==> ghost_map_mem xy f2);
    ()
  in
  Classical.forall_intro_2 prf;
  assert (FE.feq_g f1 f2)

let ghost_map_intro
  (#key #value: Type)
  (g: ghost_map' key value)
  (l: list (key & value))
: Pure (ghost_map key value)
    (requires
      List.Tot.no_repeats_p (List.Tot.map fst l) /\
      ghost_map_of_list' l == g
    )
    (ensures fun _ -> True)
= g

let ghost_map_empty #key #value =
  ghost_map_intro ghost_map_nil' []

let apply_ghost_map_empty k = ()

let ghost_map_singleton k v =
  ghost_map_intro
    (ghost_map_cons' k v ghost_map_nil')
    [k, v]

let apply_ghost_map_singleton k v k' = ()
