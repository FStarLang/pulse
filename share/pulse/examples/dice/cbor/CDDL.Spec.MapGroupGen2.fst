module CDDL.Spec.MapGroupGen2

let map_group_footprint_concat_consumes_all_recip = admit ()

let list_no_repeats_filter = admit ()

#restart-solver
let parser_spec_map_group'
  (source0: det_map_group)
  (#source: det_map_group)
  (#source_fp: typ)
  (#target: Type0)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source source_fp target_size {
    restrict_map_group source0 source /\
    map_group_footprint source source_fp
  })
  (x: Cbor.raw_data_item { t_map source0 x })
: Ghost target
    (requires True)
    (ensures (fun res ->
      let f = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp any) in
      (forall x . Ghost.reveal f x == matches_map_group_entry source_fp any x) /\
      (let x' = List.Tot.filter f (Cbor.Map?.v x) in
      map_group_parser_spec_arg_prop source source_fp x' /\
      res == p x'
    )))
=
    let Cbor.Map a = x in
    let a' = List.Tot.filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp any)) a in
    ghost_map_split (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp any)) (ghost_map_of_list a);
    let res = p a' in
    res

let parser_spec_map_group
  source0 p
= fun x -> parser_spec_map_group' source0 p x

let parser_spec_map_group_eq
  source0 #source #source_fp p x
= let f = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp any) in
  assert (
    (forall x . Ghost.reveal f x == matches_map_group_entry source_fp any x) /\
    (let x' = List.Tot.filter f (Cbor.Map?.v x) in
    map_group_parser_spec_arg_prop source source_fp x' /\
    parser_spec_map_group source0 p x == p x'
  ))

#restart-solver
let map_group_parser_spec_concat'
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (#target_size1: target1 -> nat)
  (p1: map_group_parser_spec source1 source_fp1 target_size1)
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (#target_size2: target2 -> nat)
  (p2: map_group_parser_spec source2 source_fp2 target_size2)
  (target_size: (target1 & target2) -> nat {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    typ_disjoint source_fp1 source_fp2 /\
    (forall x . target_size x == target_size1 (fst x) + target_size2 (snd x))
  })
  (l: map_group_parser_spec_arg (map_group_concat source1 source2) (source_fp1 `t_choice` source_fp2))
: Ghost (map_group_parser_spec_ret (map_group_concat source1 source2) (source_fp1 `t_choice` source_fp2) target_size l)
    (requires True)
    (ensures (fun l' ->
        let f1 = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp1 any) in
        let f2 = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp2 any) in
        (forall x . f1 x == matches_map_group_entry source_fp1 any x) /\
        (forall x . f2 x == matches_map_group_entry source_fp2 any x) /\ (
        let l1 = List.Tot.filter f1 l in
        let l2 = List.Tot.filter f2 l in
        map_group_parser_spec_arg_prop source1 source_fp1 l1 /\
        map_group_parser_spec_arg_prop source2 source_fp2 l2 /\
        (l' <: (target1 & target2)) == ((p1 l1 <: target1), (p2 l2 <: target2))
      )
    ))
=
  ghost_map_equiv
    (ghost_map_filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp1 any)) (ghost_map_of_list l))
    (ghost_map_filter (matches_map_group_entry source_fp1 any) (ghost_map_of_list l));
  map_group_footprint_is_consumed source1 source_fp1 (ghost_map_of_list l);
  let res1 = p1 (List.Tot.filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp1 any)) l) in
  let MapGroupDet c1 r1 = apply_map_group_det source1 (ghost_map_filter (matches_map_group_entry source_fp1 any) (ghost_map_of_list l)) in
  ghost_map_disjoint_union_comm r1 (ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l));
  ghost_map_split (matches_map_group_entry source_fp1 any) (ghost_map_of_list l);
  let MapGroupDet c1' r1' = apply_map_group_det source1 (ghost_map_of_list l) in
  ghost_map_equiv
    (ghost_map_filter (notp_g (matches_map_group_entry source_fp1 any)) (ghost_map_of_list l))
    (ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l));
  map_group_footprint_consumed source1 source_fp1 (ghost_map_filter (matches_map_group_entry source_fp1 any) (ghost_map_of_list l)) (ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l));
  ghost_map_union_assoc c1 r1 (ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l));
  assert (r1' == r1 `ghost_map_union` ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l));
  map_group_footprint_consumed source2 source_fp2 (ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l)) r1;
  ghost_map_equiv
    (ghost_map_filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp2 any)) (ghost_map_of_list l))
    (ghost_map_filter (matches_map_group_entry source_fp2 any) (ghost_map_of_list l));
  let res2 = p2 (List.Tot.filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp2 any)) l) in
  ghost_map_length_disjoint_union
    (ghost_map_of_list (List.Tot.filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp1 any)) l))
    (ghost_map_of_list (List.Tot.filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp2 any)) l));
  let res = (res1, res2) in
  res

let map_group_parser_spec_concat
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (#target_size1: target1 -> nat)
  (p1: map_group_parser_spec source1 source_fp1 target_size1)
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (#target_size2: target2 -> nat)
  (p2: map_group_parser_spec source2 source_fp2 target_size2)
  (target_size: (target1 & target2) -> nat {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    typ_disjoint source_fp1 source_fp2 /\
    (forall x . target_size x == target_size1 (fst x) + target_size2 (snd x))
  })
: Tot (map_group_parser_spec (map_group_concat source1 source2) (source_fp1 `t_choice` source_fp2) target_size)
= map_group_parser_spec_concat' p1 p2 target_size

#restart-solver
let map_group_parser_spec_concat_eq
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (#target_size1: target1 -> nat)
  (p1: map_group_parser_spec source1 source_fp1 target_size1)
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (#target_size2: target2 -> nat)
  (p2: map_group_parser_spec source2 source_fp2 target_size2)
  (target_size: (target1 & target2) -> nat {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    typ_disjoint source_fp1 source_fp2 /\
    (forall x . target_size x == target_size1 (fst x) + target_size2 (snd x))
  })
  (l: map_group_parser_spec_arg (map_group_concat source1 source2) (source_fp1 `t_choice` source_fp2))
: Lemma
  (exists (f1: _ -> bool) (f2: _ -> bool) .
    (forall x . f1 x == matches_map_group_entry source_fp1 any x) /\
    (forall x . f2 x == matches_map_group_entry source_fp2 any x) /\ (
    let l1 = List.Tot.filter f1 l in
    let l2 = List.Tot.filter f2 l in
    map_group_parser_spec_arg_prop source1 source_fp1 l1 /\
    map_group_parser_spec_arg_prop source2 source_fp2 l2 /\
    map_group_parser_spec_concat p1 p2 target_size l == (p1 l1, p2 l2)
  ))
  [SMTPat (map_group_parser_spec_concat p1 p2 target_size l)]
= let f1 = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp1 any) in
  let f2 = FStar.Ghost.Pull.pull (matches_map_group_entry source_fp2 any) in
  assert (
    (forall x . f1 x == matches_map_group_entry source_fp1 any x) /\
    (forall x . f2 x == matches_map_group_entry source_fp2 any x) /\ (
    let l1 = List.Tot.filter f1 l in
    let l2 = List.Tot.filter f2 l in
    map_group_parser_spec_arg_prop source1 source_fp1 l1 /\
    map_group_parser_spec_arg_prop source2 source_fp2 l2 /\
    map_group_parser_spec_concat p1 p2 target_size l == (p1 l1, p2 l2)
  ))
