module CDDL.Spec.MapGroupGen2
include CDDL.Spec.MapGroupGen2.Base
module Cbor = CBOR.Spec
module U8 = FStar.UInt8
module U64 = FStar.UInt64

let det_map_group = (m: map_group { forall l . ~ (MapGroupNonDet? (apply_map_group_det m l)) })

let ghost_map_disjoint_from_footprint
  (m: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
  (f: typ)
: Tot prop
= forall x . ghost_map_mem x m ==> ~ (f (fst x))

let map_group_footprint
  (g: map_group)
  (f: typ)
: Tot prop
= forall m m' . (ghost_map_disjoint m m' /\ ghost_map_disjoint_from_footprint m' f) ==>
  begin match apply_map_group_det g m, apply_map_group_det g (m `ghost_map_union` m') with
  | MapGroupCutFail, MapGroupCutFail
  | MapGroupFail, MapGroupFail -> True
  | MapGroupDet _ r, MapGroupDet _ r' -> r' == r `ghost_map_union` m'
  | _ -> False
  end

#restart-solver
let map_group_footprint_elim
  (g: map_group)
  (f: typ)
  (m m' : ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Lemma
  (requires
    map_group_footprint g f /\
    ghost_map_disjoint m m' /\
    ghost_map_disjoint_from_footprint m' f
  )
  (ensures
  begin match apply_map_group_det g m, apply_map_group_det g (m `ghost_map_union` m') with
  | MapGroupCutFail, MapGroupCutFail
  | MapGroupFail, MapGroupFail -> True
  | MapGroupDet _ r, MapGroupDet _ r' -> r' == r `ghost_map_union` m'
  | _ -> False
  end
  )
= ()

#restart-solver
let map_group_footprint_intro
  (g: map_group)
  (f: typ)
  (prf: (m: _) -> (m' : ghost_map Cbor.raw_data_item Cbor.raw_data_item) ->
    Lemma
    (requires
      ghost_map_disjoint m m' /\
      ghost_map_disjoint_from_footprint m' f
    )
    (ensures
    begin match apply_map_group_det g m, apply_map_group_det g (m `ghost_map_union` m') with
    | MapGroupCutFail, MapGroupCutFail
    | MapGroupFail, MapGroupFail -> True
    | MapGroupDet _ r, MapGroupDet _ r' -> r' == r `ghost_map_union` m'
    | _ -> False
    end
    )
  )
: Lemma
  (map_group_footprint g f)
= Classical.forall_intro_2 (fun m -> Classical.move_requires (prf m))

#restart-solver
let map_group_footprint_consumed
  (g: map_group)
  (f: typ)
  (m m': _)
: Lemma
  (requires
    map_group_footprint g f /\
    ghost_map_disjoint m m' /\
    ghost_map_disjoint_from_footprint m' f /\
    (MapGroupDet? (apply_map_group_det g m) \/ MapGroupDet? (apply_map_group_det g (m `ghost_map_union` m')))
  )
  (ensures (
    match apply_map_group_det g m, apply_map_group_det g (m `ghost_map_union` m') with
    | MapGroupDet c _, MapGroupDet c' _ -> c == c'
    | _ -> False
  ))
  [SMTPat (map_group_footprint g f); SMTPat (apply_map_group_det g (m `ghost_map_union` m'))]
= let MapGroupDet c r = apply_map_group_det g m in
  let MapGroupDet c' r' = apply_map_group_det g (m `ghost_map_union` m') in
  ghost_map_union_assoc c r m';
  ghost_map_disjoint_union_simpl_r c c' r'

#restart-solver
let map_group_footprint_is_consumed
  (g: map_group)
  (f: typ)
  (m: _)
: Lemma
  (requires
    map_group_footprint g f
  )
  (ensures (
    MapGroupDet? (apply_map_group_det g m) <==> MapGroupDet? (apply_map_group_det g (ghost_map_filter (matches_map_group_entry f any) m))
  ))
= ghost_map_split (matches_map_group_entry f any) m

let map_group_footprint_consumed_disjoint
  (g: map_group)
  (f f': typ)
  (m: _)
: Lemma
  (requires
    map_group_footprint g f /\
    f `typ_disjoint` f' /\
    MapGroupDet? (apply_map_group_det g m)
  )
  (ensures (
    match apply_map_group_det g m with
    | MapGroupDet c _ ->
      ghost_map_disjoint_from_footprint c f'
    | _ -> False
  ))
= ghost_map_split (matches_map_group_entry f any) m;
  map_group_footprint_consumed g f (ghost_map_filter (matches_map_group_entry f any) m) (ghost_map_filter (notp_g (matches_map_group_entry f any)) m)

#restart-solver
let map_group_footprint_concat
  (g1 g2: map_group)
  (f1 f2: typ)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2
  ))
  (ensures (
    map_group_footprint (map_group_concat g1 g2) (t_choice f1 f2)
  ))
= ()

#restart-solver
let map_group_footprint_choice
  (g1 g2: map_group)
  (f1 f2: typ)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2
  ))
  (ensures (
    map_group_footprint (map_group_choice g1 g2) (t_choice f1 f2)
  ))
= ()

#restart-solver
let map_group_footprint_zero_or_one
  (g1: map_group)
  (f1: typ)
: Lemma
  (requires (
    map_group_footprint g1 f1
  ))
  (ensures (
    map_group_footprint (map_group_zero_or_one g1) f1
  ))
= ()

#restart-solver
let map_group_footprint_consumes_all
  (g1: map_group)
  (f1: typ)
  (m1: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    apply_map_group_det g1 m1 == MapGroupDet m1 ghost_map_empty
  ))
  (ensures (
    ghost_map_filter (matches_map_group_entry f1 any) m1 == m1 /\
    ghost_map_filter (notp_g (matches_map_group_entry f1 any)) m1 == ghost_map_empty
  ))
= let phi1 = matches_map_group_entry f1 any in
  ghost_map_split phi1 m1;
  map_group_footprint_elim g1 f1 (ghost_map_filter phi1 m1) (ghost_map_filter (notp_g phi1) m1); 
  map_group_footprint_consumed g1 f1 (ghost_map_filter phi1 m1) (ghost_map_filter (notp_g phi1) m1);
  let MapGroupDet c1 r1 = apply_map_group_det g1 (ghost_map_filter phi1 m1) in
  let MapGroupDet c' r' = apply_map_group_det g1 (ghost_map_filter phi1 m1 `ghost_map_union` ghost_map_filter (notp_g phi1) m1) in
  assert (ghost_map_empty == r1 `ghost_map_union` ghost_map_filter (notp_g phi1) m1);
  ghost_map_ext ghost_map_empty (ghost_map_filter (notp_g phi1) m1);
  ()

#restart-solver
let map_group_footprint_concat_consumes_all
  (g1 g2: map_group)
  (f1 f2: typ)
  (m1 m2: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    apply_map_group_det g1 m1 == MapGroupDet m1 ghost_map_empty /\
    apply_map_group_det g2 m2 == MapGroupDet m2 ghost_map_empty /\
    typ_disjoint f1 f2
  ))
  (ensures (
    m1 `ghost_map_disjoint` m2 /\
    apply_map_group_det (g1 `map_group_concat` g2) (m1 `ghost_map_union` m2) == MapGroupDet (m1 `ghost_map_union` m2) ghost_map_empty
  ))
= map_group_footprint_consumes_all g1 f1 m1;
  map_group_footprint_consumes_all g2 f2 m2;
  ()

#restart-solver
let map_group_footprint_match_item_for
  (cut: bool)
  (key: Cbor.raw_data_item)
  (value: typ)
: Lemma
  (ensures (
    map_group_footprint (map_group_match_item_for cut key value) (t_literal key)
  ))
= let g = map_group_match_item_for cut key value in
  map_group_footprint_intro
    g
    (t_literal key)
    (fun m m' ->
       assert (~ (ghost_map_defined key m'));
       match apply_map_group_det g m, apply_map_group_det g (m `ghost_map_union` m') with
       | MapGroupDet _ r, MapGroupDet _ r' ->
         ghost_map_ext r' (r `ghost_map_union` m')
       | _ -> ()
    )

#restart-solver
let map_group_footprint_filter
  (phi: _ -> GTot bool)
  (f: typ)
: Lemma
  (requires
    forall (x: (Cbor.raw_data_item & Cbor.raw_data_item)) . notp_g phi x ==> f (fst x)
  )
  (ensures (
    map_group_footprint (map_group_filter phi) f
  ))
= let g = map_group_filter phi in
  map_group_footprint_intro
    g
    f
    (fun m m' ->
      let MapGroupDet _ r = apply_map_group_det g m in
      let MapGroupDet _ r' = apply_map_group_det g (m `ghost_map_union` m') in
      ghost_map_disjoint_union_filter phi m m';
      ghost_map_filter_for_all phi m';
      assert (r' == r `ghost_map_union` m')
    )

let restrict_map_group
  (g g': map_group)
: Tot prop
= forall m .
  begin match apply_map_group_det g m, apply_map_group_det g' m with
  | MapGroupCutFail, MapGroupCutFail
  | MapGroupFail, MapGroupFail -> True
  | MapGroupDet c r, MapGroupDet c' r' -> (forall x . ghost_map_mem x c' ==> ghost_map_mem x c)
  | _ -> False
  end

let restrict_map_group_intro
  (g g': map_group)
  (prf1: (m: _) -> Lemma
    begin match apply_map_group_det g m, apply_map_group_det g' m with
    | MapGroupCutFail, MapGroupCutFail
    | MapGroupFail, MapGroupFail -> True
    | MapGroupDet c r, MapGroupDet c' r' -> ghost_map_included c' c
    | _ -> False
    end
  )
: Lemma
  (restrict_map_group g g')
= Classical.forall_intro prf1

let restrict_map_group_refl
  (g: det_map_group)
: Lemma
  (restrict_map_group g g)
= ()

let restrict_map_group_filter
  (f: (Cbor.raw_data_item & Cbor.raw_data_item) -> GTot bool)
: Lemma
  (restrict_map_group (map_group_filter f) map_group_nop)
= ()

let restrict_map_group_zero_or_one_no_cut
  (g: det_map_group)
: Lemma
  (requires (forall m . ~ (MapGroupCutFail? (apply_map_group_det g m))))
  (ensures (restrict_map_group (map_group_zero_or_one g) map_group_nop))
= ()

let restrict_map_group_choice
  (g1 g1' g2 g2': map_group)
: Lemma
  (requires (
    restrict_map_group g1 g1' /\
    restrict_map_group g2 g2'
  ))
  (ensures (
    restrict_map_group (g1 `map_group_choice` g2) (g1' `map_group_choice` g2')
  ))
= ()

let typ_included (f1 f2: typ) : Tot prop =
  forall x . f1 x ==> f2 x

let map_group_footprint_weaken
  (g: map_group)
  (f f': typ)
: Lemma
  (requires
    map_group_footprint g f /\
    f `typ_included` f'
  )
  (ensures
    map_group_footprint g f'
  )
= ()

#restart-solver
let restrict_map_group_concat
  (g1: map_group)
  (f1: typ)
  (g1': map_group)
  (g2: map_group)
  (g2': map_group)
  (f2': typ)
: Lemma
  (requires (
    restrict_map_group g1 g1' /\
    map_group_footprint g1 f1 /\
    map_group_footprint g1' f1 /\
    restrict_map_group g2 g2' /\
    map_group_footprint g2' f2' /\
    typ_disjoint f1 f2'
  ))
  (ensures (
    restrict_map_group (g1 `map_group_concat` g2) (g1' `map_group_concat` g2')
  ))
= restrict_map_group_intro
    (g1 `map_group_concat` g2)
    (g1' `map_group_concat` g2')
    (fun m ->
      match apply_map_group_det g1 m with
      | MapGroupDet c1 r1 ->
        let MapGroupDet c1' r1' = apply_map_group_det g1' m in
        let d1 = c1 `ghost_map_sub` c1' in
        ghost_map_union_assoc c1' d1 r1;
        ghost_map_disjoint_union_simpl_l c1' (d1 `ghost_map_union` r1) r1';
        ghost_map_disjoint_union_comm d1 r1;
        assert (r1' == r1 `ghost_map_union` d1);
        map_group_footprint_consumed_disjoint g1 f1 f2' m;
        assert (ghost_map_disjoint_from_footprint d1 f2');
        map_group_footprint_elim g2' f2' r1 d1;
        begin match apply_map_group_det g2 r1 with
        | MapGroupDet c2 r2 ->
          let MapGroupDet c2' r2' = apply_map_group_det g2' r1 in
          assert (c2' `ghost_map_included` c2);
          assert ((c1' `ghost_map_union` c2') `ghost_map_included` (c1 `ghost_map_union` c2))
        | _ -> ()
        end
      | _ -> ()
    )

let map_group_choice_compatible
  (left right: map_group)
: Tot prop
= forall x . match apply_map_group_det right x with
  | MapGroupDet _ rem -> rem == ghost_map_empty ==> MapGroupFail? (apply_map_group_det left x)
  | _ -> True

#restart-solver
let map_group_choice_compatible_intro
  (left right: map_group)
  (prf: (x: _) -> Lemma
    (requires begin match apply_map_group_det right x with
     | MapGroupDet _ rem -> rem == ghost_map_empty
     | _ -> False
    end)
    (ensures MapGroupFail? (apply_map_group_det left x))
  )
: Lemma
  (map_group_choice_compatible left right)
= Classical.forall_intro (Classical.move_requires prf)

#restart-solver
let map_group_choice_compatible_match_item_for
  (cut: bool)
  (key: Cbor.raw_data_item)
  (value: typ)
  (right: map_group)
  (fp: typ)
: Lemma
  (requires (
    t_literal key `typ_disjoint` fp /\
    map_group_footprint right fp
  ))
  (ensures (
    map_group_choice_compatible (map_group_match_item_for cut key value) right
  ))
= map_group_choice_compatible_intro (map_group_match_item_for cut key value) right (fun x ->
    let phi = matches_map_group_entry fp any in
    ghost_map_split phi x;
    map_group_footprint_elim right fp (ghost_map_filter phi x) (ghost_map_filter (notp_g phi) x)
  )

let map_group_choice_compatible_no_cut
  (left right: map_group)
: Tot prop
= forall x . match apply_map_group_det right x with
  | MapGroupDet _ rem -> rem == ghost_map_empty ==> ~ (MapGroupCutFail? (apply_map_group_det left x))
  | _ -> True

let map_group_choice_compatible_implies_no_cut
  (left right: map_group)
: Lemma
  (map_group_choice_compatible left right ==> map_group_choice_compatible_no_cut left right)
= ()

#restart-solver
let map_group_fail_concat_intro
  (g1: det_map_group)
  (f1: typ)
  (g2: det_map_group)
  (f2: typ)
  (x: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    typ_disjoint f1 f2 /\ (
    MapGroupFail? (apply_map_group_det g1 x) \/ (
    (~ (MapGroupCutFail? (apply_map_group_det g1 x))) /\
    MapGroupFail? (apply_map_group_det g2 x)
  ))))
  (ensures (
    MapGroupFail? (apply_map_group_det (g1 `map_group_concat` g2) x)
  ))
= if MapGroupFail? (apply_map_group_det g1 x)
  then ()
  else begin
    let MapGroupDet c1 r1 = apply_map_group_det g1 x in
    map_group_footprint_consumed_disjoint g1 f1 f2 x;
    ghost_map_disjoint_union_comm c1 r1
  end

let map_group_consumes_all
  (g: map_group)
  (x: ghost_map _ _)
: Tot prop
= match apply_map_group_det g x with
  | MapGroupDet _ r -> r == ghost_map_empty
  | _ -> False

let map_group_choice_compatible_list
  (l: list map_group)
  (g: map_group)
: Tot prop
= forall x . map_group_consumes_all g x ==> (exists g' . List.Tot.memP g' l /\ MapGroupFail? (apply_map_group_det g' x))

let map_group_choice_compatible_list_singleton
  (left right: map_group)
: Lemma
  (map_group_choice_compatible_list [left] right <==> map_group_choice_compatible left right)
= ()

let map_group_choice_compatible_list_concat_left
  (g1: det_map_group)
  (f1: typ)
  (g2: det_map_group)
  (f2: typ)
  (l:  list map_group)
  (g: map_group)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    typ_disjoint f1 f2 /\
    map_group_choice_compatible_no_cut g1 g /\
    map_group_choice_compatible_list (g1 :: g2 :: l) g
  ))
  (ensures (
    map_group_choice_compatible_list ((g1 `map_group_concat` g2) :: l) g
  ))
= Classical.forall_intro (Classical.move_requires (map_group_fail_concat_intro g1 f1 g2 f2))

#restart-solver
let map_group_choice_compatible_list_choice_left
  (g1: det_map_group)
  (g2: det_map_group)
  (l: list map_group)
  (g: map_group)
: Lemma
  (requires (
    map_group_choice_compatible_list (g1 :: l) g /\
    map_group_choice_compatible_list (g2 :: l) g
  ))
  (ensures (
    map_group_choice_compatible_list ((g1 `map_group_choice` g2) :: l) g
  ))
= ()

#restart-solver
let map_group_choice_compatible_tail
  (g1: det_map_group)
  (l: list map_group)
  (g: map_group)
: Lemma
  (requires (
    map_group_choice_compatible_list l g
  ))
  (ensures (
    map_group_choice_compatible_list (g1 :: l) g
  ))
= ()

#restart-solver
let map_group_choice_compatible_list_choice_right
  (g1: det_map_group)
  (g2: det_map_group)
  (l: list map_group)
: Lemma
  (requires (
    map_group_choice_compatible_list l g1 /\
    map_group_choice_compatible_list l g2
  ))
  (ensures (
    map_group_choice_compatible_list l (g1 `map_group_choice` g2)
  ))
= ()

#restart-solver
val map_group_footprint_concat_consumes_all_recip
  (g1 g2: map_group)
  (f1 f2: typ)
  (m: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Pure (ghost_map Cbor.raw_data_item Cbor.raw_data_item & ghost_map Cbor.raw_data_item Cbor.raw_data_item)
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    typ_disjoint f1 f2 /\
    map_group_consumes_all (g1 `map_group_concat` g2) m
  ))
  (ensures (fun (m1, m2) ->
    m1 `ghost_map_disjoint` m2 /\
    apply_map_group_det g1 m1 == MapGroupDet m1 ghost_map_empty /\
    apply_map_group_det g2 m2 == MapGroupDet m2 ghost_map_empty /\
    m1 `ghost_map_union` m2 == m
  ))

#restart-solver
let map_group_footprint_concat_consumes_all_recip'
  (g1 g2: map_group)
  (f1 f2: typ)
  (m: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
: Lemma
  (requires (
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    typ_disjoint f1 f2 /\
    map_group_consumes_all (g1 `map_group_concat` g2) m
  ))
  (ensures exists m1m2 .
    (let (m1, m2) = m1m2 in
    m1 `ghost_map_disjoint` m2 /\
    apply_map_group_det g1 m1 == MapGroupDet m1 ghost_map_empty /\
    apply_map_group_det g2 m2 == MapGroupDet m2 ghost_map_empty /\
    m1 `ghost_map_union` m2 == m
  ))
= let (_, _) = map_group_footprint_concat_consumes_all_recip g1 g2 f1 f2 m in
  ()

#restart-solver
let map_group_choice_compatible_match_item_for_concat_right
  (cut: bool)
  (k: Cbor.raw_data_item)
  (v: typ)
  (l: list map_group)
  (g1: det_map_group)
  (f1: typ)
  (g2: det_map_group)
  (f2: typ)
: Lemma
  (requires (
    let g = map_group_match_item_for cut k v in
    map_group_footprint g1 f1 /\
    map_group_footprint g2 f2 /\
    typ_disjoint f1 f2 /\
    List.Tot.memP g l /\
    map_group_choice_compatible_list [g] g1 /\
    map_group_choice_compatible_list [g] g2
  ))
  (ensures (
    map_group_choice_compatible_list l (g1 `map_group_concat` g2)
  ))
= Classical.forall_intro (Classical.move_requires (map_group_footprint_concat_consumes_all_recip' g1 g2 f1 f2))

#restart-solver
let map_group_choice_compatible_match_item_for_zero_or_one_right
  (cut: bool)
  (k: Cbor.raw_data_item)
  (v: typ)
  (g: det_map_group)
: Lemma
  (requires (
    map_group_choice_compatible_list [map_group_match_item_for cut k v] g
  ))
  (ensures (
    map_group_choice_compatible_list [map_group_match_item_for cut k v] (map_group_zero_or_one g)
  ))
= ()

#restart-solver
let map_group_choice_compatible_match_item_for_same
  (k: Cbor.raw_data_item)
  (v1 v2: typ)
  (cut2: bool)
: Lemma
  (requires (
    typ_disjoint v1 v2
  ))
  (ensures (
    map_group_choice_compatible_list [map_group_match_item_for false k v1] (map_group_match_item_for cut2 k v2)
  ))
= ()

let ghost_map_in_footprint
  (m: ghost_map Cbor.raw_data_item Cbor.raw_data_item)
  (f: typ)
: Tot prop
= forall x . ghost_map_mem x m ==> (f (fst x))

unfold
let map_group_parser_spec_arg_common
  (source: det_map_group)
  (source_fp: typ)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item)) // list needed because I need to preserve the order of elements when parsing a table
: Tot prop
= 
    let m = ghost_map_of_list x in
    List.Tot.no_repeats_p (List.Tot.map fst x) /\
    map_group_footprint source source_fp /\
    ghost_map_in_footprint m source_fp

unfold
let map_group_parser_spec_arg_prop
  (source: det_map_group)
  (source_fp: typ)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item)) // list needed because I need to preserve the order of elements when parsing a table
: Tot prop
= map_group_parser_spec_arg_common source source_fp x /\
  MapGroupDet? (apply_map_group_det source (ghost_map_of_list x))

let map_group_parser_spec_arg
  (source: det_map_group)
  (source_fp: typ)
: Tot Type0
= (x: list (Cbor.raw_data_item & Cbor.raw_data_item) {
    map_group_parser_spec_arg_prop source source_fp x
  })

let map_group_parser_spec_ret
  (source: det_map_group)
  (source_fp: typ)
  (#target: Type0)
  (target_size: target -> nat)
  (x: map_group_parser_spec_arg source source_fp)
: Tot Type0
= (y: target { 
    target_size y <= List.Tot.length x // not everything is parsed, especially for choice
  })

let map_group_parser_spec
  (source: det_map_group)
  (source_fp: typ)
  (#target: Type0)
  (target_size: target -> nat)
: Type0
= (x: map_group_parser_spec_arg source source_fp) -> GTot (map_group_parser_spec_ret source source_fp target_size x)

unfold
let map_group_serializer_spec_arg_prop
  (source: det_map_group)
  (source_fp: typ)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item)) // list needed because I need to preserve the order of elements when parsing a table
: Tot prop
= map_group_parser_spec_arg_common source source_fp x /\
  begin match apply_map_group_det source (ghost_map_of_list x) with
  | MapGroupDet _ res -> res == ghost_map_empty // everything is consumed
  | _ -> False
  end

#restart-solver
let map_group_serializer_spec
  (#source: det_map_group)
  (#source_fp: typ)
  (#target: Type0)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source source_fp target_size)
: Type0
= (x: target) -> GTot (y: list _ {
    map_group_serializer_spec_arg_prop source source_fp y /\
    target_size x == List.Tot.length y /\
    p y == x
  })

let map_group_target_serializable
  (#target: Type0)
  (target_size: target -> nat)
: Tot Type0
= (x: target { target_size x < pow2 64 })

val list_no_repeats_filter
  (#key #value: Type)
  (f: (key & value) -> bool)
  (l: list (key & value))
: Lemma
  (requires
    List.Tot.no_repeats_p (List.Tot.map fst l)
  )
  (ensures
    List.Tot.no_repeats_p (List.Tot.map fst (List.Tot.filter f l))
  )
  [SMTPat (List.Tot.no_repeats_p (List.Tot.map fst (List.Tot.filter f l)))]

(*
val parser_spec_map_group
  (source0: det_map_group)
  (#source: det_map_group)
  (#source_fp: typ)
  (#target: Type0)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source source_fp target_size {
    restrict_map_group source0 source /\
    map_group_footprint source source_fp
  })
: Tot (parser_spec (t_map source0) (map_group_target_serializable target_size))

val parser_spec_map_group_eq
  (source0: det_map_group)
  (#source: det_map_group)
  (#source_fp: typ)
  (#target: Type0)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source source_fp target_size {
    restrict_map_group source0 source /\
    map_group_footprint source source_fp
  })
  (x: CBOR.Spec.raw_data_item { t_map source0 x })
: Lemma
  (exists (f: (Cbor.raw_data_item & Cbor.raw_data_item) -> bool) .
    (forall x . Ghost.reveal f x == matches_map_group_entry source_fp any x) /\
    (let x' = List.Tot.filter f (Cbor.Map?.v x) in
    map_group_parser_spec_arg_prop source source_fp x' /\
    parser_spec_map_group source0 p x == p x'
  ))
  [SMTPat (parser_spec_map_group source0 p x)]
*)

#restart-solver
let parser_spec_map_group
  (source0: det_map_group)
  (#source: det_map_group)
  (#source_fp: typ)
  (#target: Type0)
  (#target_size: target -> nat)
  (p: map_group_parser_spec source source_fp target_size {
    restrict_map_group source0 source /\
    map_group_footprint source source_fp
  })
: Tot (parser_spec (t_map source0) (map_group_target_serializable target_size))
= fun x ->
    let Cbor.Map a = x in
    let a' = List.Tot.filter (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp any)) a in
    ghost_map_split (FStar.Ghost.Pull.pull (matches_map_group_entry source_fp any)) (ghost_map_of_list a);
    let res = p a' in
    res

let rec list_forall_memP_filter
  (#t: Type)
  (f: t -> bool)
  (l: list t)
: Lemma
  (requires (forall x . List.Tot.memP x l ==> f x))
  (ensures (List.Tot.filter f l == l))
= match l with
  | [] -> ()
  | _ :: q -> list_forall_memP_filter f q

#restart-solver
let serializer_spec_map_group
  (source0: det_map_group)
  (#source: det_map_group)
  (#source_fp: typ)
  (#target: Type0)
  (#target_size: target -> nat)
  (#p: map_group_parser_spec source source_fp target_size)
  (s: map_group_serializer_spec p {
    restrict_map_group source0 source /\
    map_group_footprint source source_fp
  })
: Tot (serializer_spec (parser_spec_map_group source0 p))
= fun z ->
  let l = s z in
  let MapGroupDet _ rem = apply_map_group_det source0 (ghost_map_of_list l) in
  ghost_map_equiv rem ghost_map_empty;
  let res = Cbor.Map l in
  assert (t_map source0 res);
  Classical.forall_intro (fun f -> Classical.move_requires (list_forall_memP_filter #(Cbor.raw_data_item & Cbor.raw_data_item) f) l);
  assert (parser_spec_map_group source0 p res == z);
  res

let map_group_parser_spec_bij
  (#source: det_map_group)
  (#source_fp: typ)
  (#target1: Type0)
  (#target_size1: target1 -> nat)
  (f: map_group_parser_spec source source_fp target_size1)
  (#target2: Type0)
  (target_size2: target2 -> nat)
  (bij: bijection target1 target2 {
    forall x2 . target_size2 x2 == target_size1 (bij.bij_to_from x2)
  })
: Tot (map_group_parser_spec source source_fp target_size2)
= fun x -> bij.bij_from_to (f x)

let map_group_serializer_spec_bij
  (#source: det_map_group)
  (#source_fp: typ)
  (#target1: Type0)
  (#target_size1: target1 -> nat)
  (#f: map_group_parser_spec source source_fp target_size1)
  (s: map_group_serializer_spec f)
  (#target2: Type0)
  (target_size2: target2 -> nat)
  (bij: bijection target1 target2 {
    forall x2 . target_size2 x2 == target_size1 (bij.bij_to_from x2)
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_bij f target_size2 bij))
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
: Tot (map_group_parser_spec (map_group_match_item_for cut k ty) (t_literal k) target_size)
= fun x ->
  let Some v = Cbor.list_ghost_assoc k x in
  ghost_map_equiv (ghost_map_of_list x) (ghost_map_of_list [k, v]);
  ghost_map_length_of_list [k, v];
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
: Tot (map_group_serializer_spec (map_group_parser_spec_match_item_for cut k p target_size))
= fun x ->
  map_group_footprint_match_item_for cut k ty;
  let v = s x in
  let res = [k, v] in
  let mres = ghost_map_of_list res in
  ghost_map_equiv mres (ghost_map_singleton k v);
  let MapGroupDet _ rem = apply_map_group_det (map_group_match_item_for cut k ty) mres in
  ghost_map_equiv rem ghost_map_empty;
  res

(*
val map_group_parser_spec_concat
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
*)

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

let orp (#t: Type) (p1 p2: t -> bool) (x: t) : bool =
  p1 x || p2 x

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

let rec list_filter_for_none
  (#t: Type)
  (f: t -> bool)
  (l: list t)
: Lemma
  (requires (forall x . List.Tot.memP x l ==> ~ (f x)))
  (ensures List.Tot.filter f l == [])
= match l with
  | [] -> ()
  | _ :: q -> list_filter_for_none f q

#restart-solver
let map_group_serializer_spec_concat
  (#source1: det_map_group)
  (#source_fp1: typ)
  (#target1: Type)
  (#target_size1: target1 -> nat)
  (#p1: map_group_parser_spec source1 source_fp1 target_size1)
  (s1: map_group_serializer_spec p1)
  (#source2: det_map_group)
  (#source_fp2: typ)
  (#target2: Type)
  (#target_size2: target2 -> nat)
  (#p2: map_group_parser_spec source2 source_fp2 target_size2)
  (s2: map_group_serializer_spec p2)
  (target_size: (target1 & target2) -> nat {
    map_group_footprint source1 source_fp1 /\
    map_group_footprint source2 source_fp2 /\
    typ_disjoint source_fp1 source_fp2 /\
    (forall x . target_size x == target_size1 (fst x) + target_size2 (snd x))
  })
: Tot (map_group_serializer_spec (map_group_parser_spec_concat p1 p2 target_size))
= fun x ->
    map_group_footprint_concat source1 source2 source_fp1 source_fp2;
    let (x1, x2) = x in
    let l1 = s1 x1 in
    let l2 = s2 x2 in
    let res = l1 `List.Tot.append` l2 in
    map_group_footprint_concat_consumes_all source1 source2 source_fp1 source_fp2 (ghost_map_of_list l1) (ghost_map_of_list l2);
    List.Tot.append_length l1 l2;
    assert (ghost_map_in_footprint (ghost_map_of_list l1) (source_fp1 `t_choice` source_fp2));
    assert (ghost_map_in_footprint (ghost_map_of_list l2) (source_fp1 `t_choice` source_fp2));
    assert (ghost_map_in_footprint (ghost_map_of_list l1 `ghost_map_union` ghost_map_of_list l2) (source_fp1 `t_choice` source_fp2));
    ghost_map_of_list_append l1 l2;
    ghost_map_length_of_list (l1 `List.Tot.append` l2);
    assert (map_group_serializer_spec_arg_prop (source1 `map_group_concat` source2) (source_fp1 `t_choice` source_fp2) res);
    let prf
      (f1 : _ -> bool) (f2 : _ -> bool)
    : Lemma
      (requires (
        (forall x . f1 x == matches_map_group_entry source_fp1 any x) /\
        (forall x . f2 x == matches_map_group_entry source_fp2 any x)
      ))
      (ensures (
        (forall x . (f1 `orp` f2) x == matches_map_group_entry (source_fp1 `t_choice` source_fp2) any x) /\
        l1 == List.Tot.filter f1 res /\
        l2 == List.Tot.filter f2 res
      ))
    = assert (forall x . (f1 `orp` f2) x == matches_map_group_entry (source_fp1 `t_choice` source_fp2) any x);
      list_filter_append f1 l1 l2;
      list_forall_memP_filter f1 l1;
      list_filter_for_none f1 l2;
      List.Tot.append_l_nil l1;
      list_filter_for_none f2 l1;
      list_forall_memP_filter f2 l2;
      list_filter_append f2 l1 l2
    in
    Classical.forall_intro_2 (fun f1 -> Classical.move_requires (prf f1));
    assert (map_group_parser_spec_concat p1 p2 target_size res == x);
    res

(*
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
