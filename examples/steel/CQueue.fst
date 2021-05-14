module CQueue
open CQueue.LList

let t a = cllist_lvalue a

let v (a: Type0) = list a

let datas
  (#a: Type0)
  (l: v a)
: Tot (list a)
= l

let (==) (#a:_) (x y: a) : prop = x == y

let snoc_inj (#a: Type) (hd1 hd2: list a) (tl1 tl2: a) : Lemma
  (requires (hd1 `L.append` [tl1] == hd2 `L.append` [tl2]))
  (ensures (hd1 == hd2 /\ tl1 == tl2))
  [SMTPat (hd1 `L.append` [tl1]); SMTPat (hd2 `L.append` [tl2])]
= L.lemma_snoc_unsnoc (hd1, tl1);
  L.lemma_snoc_unsnoc (hd2, tl2)

[@"opaque_to_smt"]
let unsnoc (#a: Type) (l: list a) : Pure (list a & a)
  (requires (Cons? l))
  (ensures (fun (hd, tl) -> l == hd `L.append` [tl] /\ L.length hd < L.length l))
=
  L.lemma_unsnoc_snoc l;
  L.append_length (fst (L.unsnoc l)) [snd (L.unsnoc l)];
  L.unsnoc l

let unsnoc_hd (#a: Type) (l: list a) : Pure (list a) (requires (Cons? l)) (ensures (fun l' -> L.length l' < L.length l)) = fst (unsnoc l)
let unsnoc_tl (#a: Type) (l: list a) : Pure (a) (requires (Cons? l)) (ensures (fun _ -> True)) = snd (unsnoc l)

let rec llist_fragment_tail (#a: Type) (l: Ghost.erased (list a)) (phead: ref (ccell_ptrvalue a)) : Pure vprop
  (requires True)
  (ensures (fun v -> t_of v == ref (ccell_ptrvalue a)))
  (decreases (Ghost.reveal (L.length l)))
= if Nil? l
  then emp `vrewrite` (fun _ -> phead)
  else llist_fragment_tail (Ghost.hide (unsnoc_hd (Ghost.reveal l))) phead `vdep` (fun (ptail: ref (ccell_ptrvalue a)) -> vptr ptail `vrefine` (fun c -> ccell_ptrvalue_is_null c == false) `vdep` (fun (c: ccell_lvalue a) -> vptr (ccell_data c) `vrefine` (fun d -> d == unsnoc_tl (Ghost.reveal l)))) `vrewrite` (fun (| _, (| c, _ |) |) -> ccell_next c)

let queue_tail
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
: Tot vprop
=
  (llist_fragment_tail l (cllist_head x) `star` vptr (cllist_tail x)) `vdep` (fun (tails: (ref (ccell_ptrvalue a) & ref (ccell_ptrvalue a))) -> vptr (fst tails) `vrefine` (fun (tl: ccell_ptrvalue a) -> ccell_ptrvalue_is_null tl == true /\ snd tails == fst tails))

let rec llist_fragment_head (#a: Type) (l: Ghost.erased (list a)) (phead: ref (ccell_ptrvalue a)) (head: ccell_ptrvalue a) : Pure vprop
  (requires True)
  (ensures (fun v -> t_of v == ref (ccell_ptrvalue a) & ccell_ptrvalue a))
  (decreases (Ghost.reveal l))
=
  if Nil? l
  then emp `vrewrite` (fun _ -> (phead, head))
  else ((emp `vrefine` (fun _ -> ccell_ptrvalue_is_null head == false) `vrewrite` (fun _ -> (head <: ccell_lvalue a))) `vdep` (fun (head: ccell_lvalue a) -> (vptr (ccell_data head) `vrefine` (fun (d: a) -> d == L.hd (Ghost.reveal l))) `star` (vptr (ccell_next head) `vdep` (fun (tl: ccell_ptrvalue a) -> llist_fragment_head (L.tl (Ghost.reveal l)) (ccell_next head) tl)))) `vrewrite` (fun (| _, (_, (| _, ptl |) ) |) -> ptl <: (ref (ccell_ptrvalue a) & ccell_ptrvalue a))

let queue_head
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
: Tot vprop
= vptr (cllist_head x) `vdep` (fun hd -> llist_fragment_head l (cllist_head x) hd `vdep` (fun (ptl: (ref (ccell_ptrvalue a) & ccell_ptrvalue a)) -> vptr (cllist_tail x) `vrefine` (fun tl -> tl == fst ptl /\ ccell_ptrvalue_is_null (snd ptl) == true)))

(*
let rec llist_fragment (#a:Type) (rptr: ref (ccell_ptrvalue a))
                                 (ptr: ccell_ptrvalue a)
                                 (l:Ghost.erased (list (ccell_lvalue a & vcell a)))
    : Tot vprop (decreases (Ghost.reveal l))
    =
    match Ghost.reveal l with
    | [] -> emp
    | (chd, vhd) :: tl ->
      pts_to rptr full_perm ptr `star`
      pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
      llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
      pure (chd == ptr)

inline_for_extraction noextract let canon () : FStar.Tactics.Tac unit =
  (FStar.Tactics.norm [delta_attr [`%__reduce__]]; canon' false (`true_p) (`true_p))

let _: squash (forall p q. p `equiv` q <==> hp_of p `Steel.Memory.equiv` hp_of q) =
  Classical.forall_intro_2 reveal_equiv

let rec next_last
  (#a: Type)
  (rptr: ref (ccell_ptrvalue a))
  (ptr: ccell_ptrvalue a)
  (l: Ghost.erased (list (ccell_lvalue a & vcell a)))
: Tot (Ghost.erased (ref (ccell_ptrvalue a) & ccell_ptrvalue a))
  (decreases (Ghost.reveal l))
=
  match Ghost.reveal l with
  | [] -> Ghost.hide (rptr, ptr)
  | (ca, va) :: q -> next_last (ccell_next ca) va.vcell_next q

let rec next_last_correct
  (#a: Type)
  (rptr: ref (ccell_ptrvalue a))
  (ptr: ccell_ptrvalue a)
  (l: Ghost.erased (list (ccell_lvalue a & vcell a)))
: Lemma
  (requires (Cons? l))
  (ensures (
    let (ca', va') = L.last l in
    let (ca, va) = Ghost.reveal (next_last rptr ptr l) in
    ca == ccell_next ca' /\
    va == va'.vcell_next
  ))
  (decreases (Ghost.reveal l))
= match Ghost.reveal l with
  | [_] -> ()
  | (ca, va) :: q -> next_last_correct (ccell_next ca) va.vcell_next (Ghost.hide q)

// AF: This is not true in general, but true in this module since all vprops are direct slprop lifts.
// TODO: Fix proofs, and remove this axiom
// let slprop_extensionality (p q:vprop)
//   : Lemma
//     (requires p `equiv` q)
//     (ensures p == q)
//     [SMTPat (p `equiv` q)]
// = admit()
//  slprop_extensionality p q

let rec llist_fragment_append
  (#a: Type)
  (rptr: ref (ccell_ptrvalue a))
  (ptr: ccell_ptrvalue a)
  (l1: Ghost.erased (list (ccell_lvalue a & vcell a)))
  (l2: Ghost.erased (list (ccell_lvalue a & vcell a)))
: Lemma
  (requires True)
  (ensures (((llist_fragment rptr ptr l1 `star` llist_fragment (fst (next_last rptr ptr l1)) (snd (next_last rptr ptr l1))  l2)) `equiv` llist_fragment rptr ptr (l1 `L.append` l2)))
  (decreases (Ghost.reveal l1))
= match Ghost.reveal l1 with
  | [] ->
    assert (
      (emp `star` llist_fragment rptr ptr l2) `equiv` llist_fragment rptr ptr l2
    ) by canon ()
  | (chd, vhd) :: tl ->
    assert ((
      (
        pts_to rptr full_perm ptr `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
        pure (chd == ptr)
      ) `star`
      llist_fragment (fst (next_last (ccell_next chd) vhd.vcell_next tl)) (snd (next_last (ccell_next chd) vhd.vcell_next tl)) l2
    ) `equiv` (
        pts_to rptr full_perm ptr `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        (
          llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
          llist_fragment (fst (next_last (ccell_next chd) vhd.vcell_next tl)) (snd (next_last (ccell_next chd) vhd.vcell_next tl)) l2
        ) `star`
        pure (chd == ptr)
    )) by canon ();
    llist_fragment_append (ccell_next chd) vhd.vcell_next tl l2;
    assert ((
        pts_to rptr full_perm ptr `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        (
          llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
          llist_fragment (fst (next_last (ccell_next chd) vhd.vcell_next tl)) (snd (next_last (ccell_next chd) vhd.vcell_next tl)) l2
        ) `star`
        pure (chd == ptr)
    ) `equiv` (
        (
          llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
          llist_fragment (fst (next_last (ccell_next chd) vhd.vcell_next tl)) (snd (next_last (ccell_next chd) vhd.vcell_next tl)) l2
        ) `star`
        (
          pts_to rptr full_perm ptr `star`
          pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
          pure (chd == ptr)
        )
    )) by canon ();
    star_congruence
     (
        llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
        llist_fragment (fst (next_last (ccell_next chd) vhd.vcell_next tl)) (snd (next_last (ccell_next chd) vhd.vcell_next tl)) l2
      )
      (
        pts_to rptr full_perm ptr `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        pure (chd == ptr)
      )
      (llist_fragment (ccell_next chd) vhd.vcell_next (tl `L.append` l2))
      (
        pts_to rptr full_perm ptr `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        pure (chd == ptr)
      );
     assert ((
        llist_fragment (ccell_next chd) vhd.vcell_next (tl `L.append` l2) `star`
        (
          pts_to rptr full_perm ptr `star`
          pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
          pure (chd == ptr)
        )
    ) `equiv` (
        pts_to rptr full_perm ptr `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        llist_fragment (ccell_next chd) vhd.vcell_next (tl `L.append` l2) `star`
        pure (chd == ptr)
    )) by canon ()

(* I need to account for changing the next pointer of the last cell *)

let update_next_last
  (#a: Type)
  (l: list (ccell_lvalue a & vcell a))
  (n: ccell_ptrvalue a)
: Tot (list (ccell_lvalue a & vcell a))
= match l with
  | [] -> l
  | _ ->
    let (ctl, vtl) = unsnoc_tl l in
    unsnoc_hd l `L.append` [(ctl, { vcell_data = vtl.vcell_data; vcell_next = n })]

let next_last_update_next_last
  (#a: Type)
  (rptr: ref (ccell_ptrvalue a))
  (ptr: ccell_ptrvalue a)
  (l: Ghost.erased (list (ccell_lvalue a & vcell a)))
  (n: ccell_ptrvalue a)
: Lemma
  (requires (Cons? l))
  (ensures (next_last rptr ptr (update_next_last l n) == Ghost.hide (fst (next_last rptr ptr l), n)))
= next_last_correct rptr ptr l;
  next_last_correct rptr ptr (update_next_last l n);
  let (ctl, vtl) = unsnoc_tl l in
  L.lemma_append_last (unsnoc_hd l) [(unsnoc_tl l)];
  L.lemma_append_last (unsnoc_hd l) [(ctl, { vcell_data = vtl.vcell_data; vcell_next = n })]

let llist_fragment_update_next_last
  (#a: Type)
  (rptr: ref (ccell_ptrvalue a))
  (ptr: ccell_ptrvalue a)
  (l: Ghost.erased (list (ccell_lvalue a & vcell a)))
  (n: ccell_ptrvalue a)
: Lemma
  (llist_fragment rptr ptr (update_next_last l n) `equiv` llist_fragment rptr ptr l)
= match Ghost.reveal l with
  | [] -> ()
  | _ ->
    let hd = unsnoc_hd l in
    let (ctl, vtl) = unsnoc_tl l in
    llist_fragment_append rptr ptr hd [(ctl, vtl)];
    llist_fragment_append rptr ptr hd [(ctl, { vcell_data = vtl.vcell_data; vcell_next = n })]


(* The singly-linked list as a queue *)

let queue_prop
  (#a: Type) (x: cllist_lvalue a) (l: Ghost.erased (v a))
: Tot prop
=
  fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail /\
  ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true

let queue
  #a x l
=
  pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
  llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
  pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
  pure (queue_prop x l)

#push-options "--ide_id_info_off"

let unpack_queue
  (#a: Type)
  (x: cllist_lvalue a) (l: Ghost.erased (v a))
: Steel unit
    (queue x l)
    (fun _ -> pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _))
    (requires (fun _ -> True))
    (ensures (fun _ _ _ ->
      fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail /\
      ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true
    ))
= rewrite_slprop
    (queue x l)
    (pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
      pure (queue_prop x l))
    (fun _ -> ());
  elim_pure (queue_prop x l)

let pack_queue
  (#a: Type)
  (x: cllist_lvalue a) (l: Ghost.erased (v a))
: Steel unit
    (pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _))
    (fun _ -> queue x l)
    (requires (fun _ ->
      fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail /\
      ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true
    ))
    (ensures (fun _ _ _ -> True))
= intro_pure (queue_prop x l);
  rewrite_slprop
    (pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
      pure (queue_prop x l))
    (queue x l)
    (fun _ -> ())

let pack_queue1
  (#a: Type)
  (x: cllist_lvalue a) (l: Ghost.erased (v a))
  (tail1: _) (vtail1: Ghost.erased _)
  (tail2: _) (vtail2: Ghost.erased _)
: Steel unit
    (pts_to tail1 full_perm vtail1 `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to tail2 full_perm vtail2)
    (fun _ -> queue x l)
    (requires (fun _ ->
      tail1 == cllist_tail x /\
      Ghost.reveal vtail1 == l.vllist.vllist_tail /\
      tail2 == l.vllist.vllist_tail /\
      Ghost.reveal vtail2 == ccell_ptrvalue_null a /\
      fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail /\
      ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true
    ))
    (ensures (fun _ _ _ -> True))
=
  rewrite_slprop
    (pts_to (tail1) full_perm vtail1)
    (pts_to (cllist_tail x) full_perm l.vllist.vllist_tail)
    (fun _ -> ());
  rewrite_slprop
    (pts_to (tail2) full_perm vtail2)
    (pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _))
    (fun _ -> ());
  pack_queue x l

let change_equiv_slprop
  (p q: vprop)
  (sq: (unit -> Lemma (p `equiv` q)))
: SteelT unit
    p
    (fun _ -> q)
=
  rewrite_slprop p q (fun _ -> sq ())

let change_equal_slprop
  (p q: vprop)
  (sq: (unit -> Lemma (p == q)))
: SteelT unit
    p
    (fun _ -> q)
= change_equiv_slprop p q (fun _ -> reveal_equiv p q; sq ())

let get_data_update_next_last
  (#a: Type)
  (l: (list (ccell_lvalue a & vcell a)))
  (n: ccell_ptrvalue a)
: Lemma
  (L.map get_data (update_next_last l n) == L.map get_data l)
= match l with
  | [] -> ()
  | _ ->
    let hd = unsnoc_hd l in
    let (ctl, vtl) = unsnoc_tl l in
    L.map_append get_data hd [(ctl, vtl)];
    L.map_append get_data hd [(ctl, { vcell_data = vtl.vcell_data; vcell_next = n })]

let create_queue
  a
=
  let ll = alloc_cllist (ccell_ptrvalue_null _) null in
  let cl = fst ll in
  rewrite_slprop (cllist (fst ll) full_perm (snd ll)) (pts_to (cllist_head cl) full_perm (snd ll).vllist_head `star` pts_to (cllist_tail cl) full_perm (snd ll).vllist_tail) (fun _ -> ());
  write_pt (cllist_tail cl) (cllist_head cl);
  let wl = { vllist_head = ccell_ptrvalue_null _; vllist_tail = cllist_head cl } in
  let w = Ghost.hide ({
    vllist = wl;
    cells = [];
  }) in
  let res = (cl, w) in
  rewrite_slprop
    emp
    (llist_fragment (cllist_head (fst res)) (Ghost.reveal (snd res)).vllist.vllist_head (Ghost.reveal (snd res)).cells)
    (fun _ -> ());
  pack_queue1 (fst res) (snd res) (cllist_tail cl) (cllist_head cl) (cllist_head cl) (snd ll).vllist_head;
  res

private
let abcd_abc_d (a b c d : vprop)
  : Lemma (((a `star` b `star` c) `star` d) `equiv` (a `star` b `star` c `star` d))
  = assert (((a `star` b `star` c) `star` d) `equiv` (a `star` b `star` c `star` d)) by canon ()

let emp_equiv_pure
  (p: prop)
: Lemma
  (requires p)
  (ensures (emp `equiv` pure p))
= reveal_emp ();
  reveal_equiv emp (pure p);
  Classical.forall_intro intro_emp;
  Classical.forall_intro (pure_interp p)

#restart-solver

#push-options "--z3rlimit 40"

let enqueue
  #a x l w
=
  let cc = alloc_cell w (ccell_ptrvalue_null a) in
  let c = fst cc in
  let vc = snd cc in
  rewrite_slprop (ccell (fst cc) full_perm (snd cc))
    (pts_to (ccell_data c) full_perm w `star` pts_to (ccell_next c) full_perm (ccell_ptrvalue_null a))
    (fun _ -> ());
  unpack_queue x l;
  let tail = read_pt (cllist_tail x) in
  rewrite_slprop
    (pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _))
    (pts_to tail full_perm (ccell_ptrvalue_null _))
    (fun _ -> ());
  write_pt tail c;
  write_pt (cllist_tail x) (ccell_next c);
  let res = Ghost.hide ({
    vllist = {
      vllist_head =
        begin match l.cells with
        | [] -> c
        | _ -> l.vllist.vllist_head
        end;
      vllist_tail = ccell_next c;
    };
    cells = update_next_last l.cells c `L.append` [(c, Ghost.reveal vc)]
  }) in
  L.map_append get_data (update_next_last l.cells c) [(c, Ghost.reveal vc)];
  get_data_update_next_last l.cells c;
  L.lemma_append_last (update_next_last l.cells c) [(c, Ghost.reveal vc)];
  next_last_correct l.vllist.vllist_tail l.vllist.vllist_head res.cells;
  rewrite_slprop
    (llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to tail full_perm c `star`
      pts_to (ccell_data c) full_perm w)
    (llist_fragment (cllist_head x) res.vllist.vllist_head res.cells)
    (fun _ ->
      llist_fragment_update_next_last (cllist_head x) l.vllist.vllist_head l.cells c;
      match Ghost.reveal l.cells with
      | [] ->
        assert (
          (emp `star` pts_to tail full_perm c `star` pts_to (ccell_data c) full_perm w) `equiv`
          ((pts_to tail full_perm c `star` pts_to (ccell_data c) full_perm w `star` emp) `star` emp)
        ) by canon ();
        emp_equiv_pure (c == res.vllist.vllist_head);
        star_congruence
          (pts_to tail full_perm c `star` pts_to (ccell_data c) full_perm w `star` emp)
          emp
          (pts_to tail full_perm c `star` pts_to (ccell_data c) full_perm w `star` emp)
          (pure (c == res.vllist.vllist_head));
       abcd_abc_d (pts_to tail full_perm c) (pts_to (ccell_data c) full_perm w) emp
         (pure (c == res.vllist.vllist_head));
       assert (
         (pts_to tail full_perm c `star` pts_to (ccell_data c) full_perm w `star` emp) `star` pure (c == res.vllist.vllist_head)
         `equiv`
         (pts_to tail full_perm c `star` pts_to (ccell_data c) full_perm w `star` emp `star` pure (c == res.vllist.vllist_head))
       )

      | _ ->
        next_last_update_next_last (cllist_head x) l.vllist.vllist_head l.cells c;
        emp_equiv_pure (c == (c <: ccell_ptrvalue a));
        llist_fragment_append (cllist_head x) l.vllist.vllist_head (update_next_last l.cells c) [(c, Ghost.reveal vc)];
        assert ((
          llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
          pts_to tail full_perm c `star`
          pts_to (ccell_data c) full_perm w
        ) `equiv` (
          llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
            (pts_to tail full_perm c `star`
              pts_to (ccell_data c) full_perm w `star`
              emp `star`
              emp
            )
        )) by canon ();
        admit()
        (* AF: TODO: I added the following, but it is not yet sufficient *)

       //  assert (
       //    (llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
       //      (pts_to tail full_perm c `star`
       //        pts_to (ccell_data c) full_perm w `star`
       //        emp `star`
       //        emp
       //      ))
       //     `equiv`
       //    ((llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
       //      pts_to tail full_perm c `star`
       //        pts_to (ccell_data c) full_perm w `star`
       //        emp
       //    ) `star` emp)
       //  ) by canon ();
       // star_congruence
       //   (llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
       //    pts_to tail full_perm c `star`
       //    pts_to (ccell_data c) full_perm w `star`
       //    emp)
       //   emp
       //   (llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
       //    pts_to tail full_perm c `star`
       //    pts_to (ccell_data c) full_perm w `star`
       //    emp)
       //   (pure (c == (c <: ccell_ptrvalue a)));
       //  assert ((llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
       //      pts_to tail full_perm c `star`
       //        pts_to (ccell_data c) full_perm w `star`
       //        emp
       //    ) `star` pure (c == (c <: ccell_ptrvalue a))
       //    `equiv`
       //  (llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star` (
       //        pts_to tail full_perm c `star`
       //        pts_to (ccell_data c) full_perm w `star`
       //        emp `star`
       //        pure (c == (c <: ccell_ptrvalue a))))
       //  ) by canon ()

    );
  pack_queue1 x res (cllist_tail x) (ccell_next c) (ccell_next c) (ccell_ptrvalue_null a);
  res

let pure_star_equiv
  (p: vprop)
  (q: prop)
: Lemma
  (forall m . interp (hp_of (p `star` pure q)) m <==> interp (hp_of p) m /\ q)
=
  emp_unit (hp_of p);
  Classical.forall_intro (fun m ->
    pure_star_interp (hp_of p) q m
  )

let pure_star_accumulate_r
  (p: vprop)
  (q1 q2: prop)
: Lemma
  (((p `star` pure q1) `star` pure q2) `equiv` (p `star` pure (q1 /\ q2)))
= Classical.forall_intro_2 reveal_equiv;
  pure_star_equiv (p `star` pure q1) q2;
  pure_star_equiv p q1;
  pure_star_equiv p (q1 /\ q2)

let pure_rewrite
  (p1 p2: vprop)
  (q: prop)
: Lemma
  (requires (q ==> (p1 `equiv` p2)))
  (ensures ((p1 `star` pure q) `equiv` (p2 `star` pure q)))
= Classical.forall_intro_2 reveal_equiv;
  pure_star_equiv p1 q;
  pure_star_equiv p2 q

let pure_rewrite_intro
  (p1 p2: vprop)
  (q: prop)
  (lem: unit -> Lemma (requires q) (ensures (p1 `equiv` p2)))
: Lemma
  (ensures ((p1 `star` pure q) `equiv` (p2 `star` pure q)))
=
  Classical.move_requires lem ();
  pure_rewrite p1 p2 q

let rec llist_fragment'
  (#a: Type)
  (p: ccell_ptrvalue a)
  (l: Ghost.erased (list (ccell_lvalue a & vcell a)))
: Tot vprop
  (decreases (Ghost.reveal l))
= match Ghost.reveal l with
  | [] -> emp
  | (pc, vc) :: q ->
    ccell pc full_perm vc `star` llist_fragment' vc.vcell_next q `star` pure (pc == p)

let queue_prop'
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Tot prop
= ccell_ptrvalue_is_null l.vllist.vllist_head == Nil? l.cells /\
  begin match l.cells with
  | [] -> l.vllist.vllist_tail == cllist_head x
  | _ -> l.vllist.vllist_tail == ccell_next (fst (L.last l.cells)) /\ ccell_ptrvalue_is_null (snd (L.last l.cells)).vcell_next
  end

let queue'
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Tot vprop
=
  cllist x full_perm l.vllist `star`
  llist_fragment' l.vllist.vllist_head l.cells `star`
  pure (queue_prop' x l)

let queue_prop0
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Tot prop
= ccell_ptrvalue_is_null l.vllist.vllist_head == Nil? l.cells /\
  fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail /\
  ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true

let queue_prop0_equiv
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Lemma
  (queue_prop0 x l <==> queue_prop' x l)
= match l.cells with
  | [] -> ()
  | _ -> next_last_correct (cllist_head x) l.vllist.vllist_head l.cells

let pure_and_equiv
  (p q: prop)
: Lemma
  ((pure p `star` pure q) `equiv` pure (p /\ q))
=
  assert ((pure p `star` pure q) `equiv` (emp `star` pure p `star` pure q)) by canon ();
  assert (pure (p /\ q) `equiv` (emp `star` pure (p /\ q))) by canon ();
  pure_star_accumulate_r emp p q

let pure_dup
  (p q: prop)
: Lemma
  (pure p `equiv` (pure p `star` pure p))
=
  pure_equiv p (p /\ p);
  pure_and_equiv p p

let queue_equiv_1
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Lemma
  (queue x l `equiv` (
    pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
    llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
    pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
    pure (queue_prop0 x l)
  ))
=
  match l.cells with
  | [] ->
    pure_equiv (queue_prop x l) (queue_prop0 x l);
    star_congruence
      (pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
       llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
       pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _))
      (pure (queue_prop0 x l))
      (pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
       llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
       pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _))
      (pure (queue_prop x l))

  | (chd, vhd) :: tl ->
    pure_equiv (chd == l.vllist.vllist_head) (chd == l.vllist.vllist_head /\ ccell_ptrvalue_is_null l.vllist.vllist_head == false);
    pure_and_equiv (chd == l.vllist.vllist_head) (ccell_ptrvalue_is_null l.vllist.vllist_head == false);
    assert (( (* necessary, otherwise queue x l cannot be proven equiv to the lhs of the equiv below *)
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells
    ) == (
        pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        llist_fragment (ccell_next chd) vhd.vcell_next (Ghost.hide tl) `star`
        pure (chd == l.vllist.vllist_head)
    ));
    assert ((
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      (
        pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
        (pure (chd == l.vllist.vllist_head) `star` pure (ccell_ptrvalue_is_null l.vllist.vllist_head == false))
      ) `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
      pure (queue_prop x l)
    ) `equiv` (
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      (
        pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
        pure (chd == l.vllist.vllist_head)
      ) `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
      (
        pure (queue_prop x l) `star`
        pure (ccell_ptrvalue_is_null l.vllist.vllist_head == false)
      )
    )) by canon ();
    pure_and_equiv (queue_prop x l) (ccell_ptrvalue_is_null l.vllist.vllist_head == false);
    pure_equiv (queue_prop0 x l) (queue_prop x l /\ ccell_ptrvalue_is_null l.vllist.vllist_head == false);
    admit()
    (* AF: TODO: Fix *)



let rec llist_fragment_equiv
  (#a: Type)
  (phd: ref (ccell_ptrvalue a))
  (hd: ccell_ptrvalue a)
  (l: list (ccell_lvalue a & vcell a))
: Lemma
  (requires True)
  (ensures ((
    llist_fragment phd hd l `star`
    pts_to (fst (next_last phd hd l)) full_perm (snd (next_last phd hd l))
  ) `equiv` (
    pts_to phd full_perm hd `star`
    llist_fragment' hd l
  )))
  (decreases l)
= match l with
  | [] ->
    assert (
      (emp `star` pts_to phd full_perm hd) `equiv`
      (pts_to phd full_perm hd `star` emp)
    ) by canon ()
  | (chd, vhd) :: tl ->
    assert ((
      pts_to phd full_perm hd `star`
      pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
      llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
      pure (chd == hd) `star`
      pts_to (fst (next_last phd hd l)) full_perm (snd (next_last phd hd l))
    ) `equiv` (
      pts_to phd full_perm hd `star`
      pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        (llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
          pts_to (fst (next_last phd hd l)) full_perm (snd (next_last phd hd l))) `star`
      pure (chd == hd)
    )) by canon ();
    llist_fragment_equiv (ccell_next chd) vhd.vcell_next tl;
    assert ((
      pts_to phd full_perm hd `star`
      pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        (pts_to (ccell_next chd) full_perm vhd.vcell_next `star`
          llist_fragment' vhd.vcell_next tl) `star`
      pure (chd == hd)
    ) `equiv` (
      pts_to phd full_perm hd `star`
      (pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        pts_to (ccell_next chd) full_perm vhd.vcell_next `star`
        llist_fragment' vhd.vcell_next tl `star`
        pure (chd == hd))
    )) by canon ();
    admit()
    (* AF: TODO: Fix *)

let queue_equiv_2
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Lemma
  (requires (
    queue_prop0 x l
  ))
  (ensures ((
    pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
    llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
    pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _)
  ) `equiv` (
    cllist x full_perm l.vllist `star`
    llist_fragment' l.vllist.vllist_head l.cells
  )))
=
    assert ((
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _)
    ) `equiv` (
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      (llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
        pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _))
    )) by canon ();
    llist_fragment_equiv (cllist_head x) l.vllist.vllist_head l.cells;
    assert ((
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      (pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
        llist_fragment' l.vllist.vllist_head l.cells)
    ) `equiv` (
      pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment' l.vllist.vllist_head l.cells
    )) by canon ();
    admit()
    (* TODO: Fix *)

let queue_equiv
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Lemma
  (queue x l `equiv` queue' x l)
= pure_rewrite_intro
    (
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _)
    )
    (
      cllist x full_perm l.vllist `star`
      llist_fragment' l.vllist.vllist_head l.cells
    )
    (queue_prop0 x l)
    (fun _ -> queue_equiv_2 x l);
  queue_equiv_1 x l;
  queue_prop0_equiv x l;
  reveal_equiv (pure (queue_prop0 x l)) (pure (queue_prop' x l));
  pure_equiv (queue_prop0 x l) (queue_prop' x l);
  admit()
  (* TODO: Fix *)

let peek_pure
  (#uses:_) (p:prop)
  : SteelGhostT (_:unit{p}) uses
                (pure p)
                (fun _ -> pure p)
=
  let q = elim_pure p in
  intro_pure p;
  q

let read_no_change (#a:Type) (#p:perm) (#v:Ghost.erased a) (r:ref a)
  : Steel a (pts_to r p v) (fun _ -> pts_to r p v)
           (requires fun _ -> True)
           (ensures fun _ x _ -> x == Ghost.reveal v)
=
  let v' = read_pt r in
  rewrite_slprop (pts_to r p v') (pts_to r p v) (fun _ -> ());
  return v'

let queue_is_empty
  #a x l
=
  change_equiv_slprop
    (queue x l)
    (
      pts_to (cllist_head x) full_perm l.vllist.vllist_head `star` pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment' l.vllist.vllist_head l.cells `star`
      pure (queue_prop' x l)
    )
    (fun _ -> queue_equiv x l);
  peek_pure (queue_prop' x l);
  let hd = read_pt (cllist_head x) in
  change_equiv_slprop
    (
        pts_to (cllist_head x) full_perm hd `star` pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
        llist_fragment' l.vllist.vllist_head l.cells `star`
        pure (queue_prop' x l)
    )
    (queue x l)
    (fun _ -> queue_equiv x l);
  ccell_ptrvalue_is_null hd


let dequeue
  #a x l
=
  let l0 : (l0: Ghost.erased (list (ccell_lvalue a & vcell a)) { Cons? l0 }) = l.cells in
  let chd : Ghost.erased (ccell_lvalue a) = Ghost.hide (fst (L.hd l0)) in
  let vhd : Ghost.erased (vcell a) = Ghost.hide (snd (L.hd l0)) in
  let tl : Ghost.erased (list (ccell_lvalue a & vcell a)) = Ghost.hide (L.tl l0) in
  change_equiv_slprop
    (queue x l)
    (
      cllist x full_perm l.vllist `star`
      (
        ccell chd full_perm vhd `star`
        llist_fragment' vhd.vcell_next tl `star`
        pure (Ghost.reveal chd == l.vllist.vllist_head)
      ) `star`
      pure (queue_prop' x l)
    )
    (fun _ -> queue_equiv x l);
  elim_pure (queue_prop' x l);
  elim_pure (Ghost.reveal chd == l.vllist.vllist_head);
  let chd' = read_pt (cllist_head x) in
  assert (chd' == Ghost.reveal chd);
  let (chd' : ccell_lvalue a) = chd' in
  rewrite_slprop
    (ccell chd full_perm vhd)
    (pts_to (ccell_data chd') full_perm vhd.vcell_data `star` pts_to (ccell_next chd') full_perm vhd.vcell_next)
    (fun _ -> ());
  let chd_data = read_pt (ccell_data chd') in
  let chd_next = read_pt (ccell_next chd') in
  rewrite_slprop
    (pts_to (ccell_data chd') full_perm chd_data `star` pts_to (ccell_next chd') full_perm chd_next)
    (ccell chd' full_perm vhd)
    (fun _ -> ());
  free_cell chd' _;
  write_pt (cllist_head x) chd_next;
  if ccell_ptrvalue_is_null chd_next
  then begin
    rewrite_slprop
      (llist_fragment' vhd.vcell_next tl)
      (llist_fragment' vhd.vcell_next tl `star` pure (Nil? tl == true))
      (fun _ ->
        admit();
        match Ghost.reveal tl with
        | [] ->
          assert (llist_fragment' vhd.vcell_next tl `equiv` (llist_fragment' vhd.vcell_next tl `star` emp)) by canon ();
          emp_equiv_pure (Nil? tl == true)
        | (chd2, vhd2) :: tl2 ->
          pure_equiv (chd2 == vhd.vcell_next) (chd2 == vhd.vcell_next /\ Nil? tl == true); // because that equality contradicts ccell_ptrvalue_is_null chd_next
          pure_and_equiv (chd2 == vhd.vcell_next) (Nil? tl == true);
          assert ((
            ccell chd2 full_perm vhd2 `star` llist_fragment' vhd2.vcell_next tl2 `star` (pure (chd2 == vhd.vcell_next) `star` pure (Nil? tl == true))
          ) `equiv` (
            (ccell chd2 full_perm vhd2 `star` llist_fragment' vhd2.vcell_next tl2 `star` pure (chd2 == vhd.vcell_next)) `star` pure (Nil? tl == true)
          )) by canon ()
      );
    elim_pure (Nil? tl == true);
    write_pt (cllist_tail x) (cllist_head x);
    let l' : Ghost.erased (v a) = Ghost.hide ({
      vllist = ({ vllist_head = chd_next; vllist_tail = cllist_head x });
      cells = []
    })
    in
    let res = (chd_data, l') in
    intro_pure (queue_prop' x l');
    rewrite_slprop
      (
        pts_to (cllist_head x) full_perm chd_next `star`
        pts_to (cllist_tail x) full_perm (cllist_head x) `star`
        llist_fragment' vhd.vcell_next tl `star`
        pure (queue_prop' x l')
      )
      (queue x (snd res))
      (fun _ ->
        queue_equiv x (snd res)
      );
    return res
  end else begin
    let l' : Ghost.erased (v a) = Ghost.hide ({
      vllist = ({ vllist_head = chd_next; vllist_tail = l.vllist.vllist_tail });
      cells = Ghost.reveal tl;
    })
    in
    let res = (chd_data, l') in
    intro_pure (queue_prop' x l');
    rewrite_slprop
      (
        pts_to (cllist_head x) full_perm chd_next `star`
        pts_to (cllist_tail x) full_perm _ `star`
        llist_fragment' vhd.vcell_next tl `star`
        pure (queue_prop' x l')
      )
      (queue x (snd res))
      (fun _ -> queue_equiv x (snd res));
    return res
  end
