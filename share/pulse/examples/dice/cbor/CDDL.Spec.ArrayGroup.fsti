module CDDL.Spec.ArrayGroup
include CDDL.Spec.Base
module Cbor = CBOR.Spec
module U8 = FStar.UInt8
module U64 = FStar.UInt64

// Section 2.1: Groups 

// Groups in array context (Section 3.4)

// Greedy semantics (Appendix A)

let list_is_suffix_of
  (#t: Type)
  (small large: list t)
: Tot prop
= exists prefix . large == prefix `List.Tot.append` small

let list_is_suffix_of_refl
  (#t: Type)
  (l: list t)
: Lemma
  (l `list_is_suffix_of` l)
  [SMTPat (l `list_is_suffix_of` l)]
= assert (l == [] `List.Tot.append` l)

let rec list_nil_precedes
  (#t: Type)
  (l: list t)
: Lemma
  (Nil #t == l \/ Nil #t << l)
= match l with
  | [] -> ()
  | a :: q -> list_nil_precedes q

let rec list_is_suffix_of_precedes
  (#t0 #t: Type)
  (v0: t0)
  (small large: list t)
: Lemma
  (requires (
    large << v0 /\
    small `list_is_suffix_of` large
  ))
  (ensures (
    small << v0
  ))
  (decreases (List.Tot.length large))
  [SMTPat [small << v0]; SMTPat [small `list_is_suffix_of` large]]
= if Nil? small
  then list_nil_precedes large
  else begin
    let prefix = FStar.IndefiniteDescription.indefinite_description_ghost (list t) (fun prefix -> large == prefix `List.Tot.append` small) in
    List.Tot.append_length prefix small;
    if List.Tot.length small = List.Tot.length large
    then ()
    else list_is_suffix_of_precedes v0 small (List.Tot.tl large)
  end

let opt_precedes_list_item
  (#t1 #t2: Type)
  (x2: option t2)
  (x1: t1)
: GTot bool
= FStar.StrongExcludedMiddle.strong_excluded_middle (opt_precedes x1 x2)

module Pull = FStar.Ghost.Pull

noextract
let opt_precedes_list
  (#t1 #t2: Type)
  (l: list t1)
  (b: option t2)
: Tot prop
= List.Tot.for_all (Pull.pull (opt_precedes_list_item b)) l

let rec opt_precedes_opt_precedes_list
  (#t1 #t2: Type)
  (l: list t1)
  (b: option t2)
: Lemma
  (requires (opt_precedes l b))
  (ensures (opt_precedes_list l b))
  [SMTPat (opt_precedes_list l b)]
= match l with
  | [] -> ()
  | a :: q -> opt_precedes_opt_precedes_list q b

[@@erasable; noextract_to "krml"]
let array_group3 (bound: option Cbor.raw_data_item) = (l: list Cbor.raw_data_item { opt_precedes_list l bound }) -> Ghost (option (list Cbor.raw_data_item & list Cbor.raw_data_item))
  (requires True)
  (ensures (fun l' -> match l' with
  | None -> True
  | Some (l1, l2) -> l == l1 `List.Tot.append` l2
  ))

noextract
let array_group3_equiv
  #b
  (g1 g2: array_group3 b)
: Tot prop
= forall l . g1 l == g2 l

let array_group3_always_false #b : array_group3 b = fun _ -> None

let opt_precedes_list_assoc
  (#t1 #t2: Type)
  (l1 l2: list t1)
  (b: option t2)
: Lemma
  (opt_precedes_list (l1 `List.Tot.append` l2) b <==>  opt_precedes_list l1 b /\ opt_precedes_list l2 b)
  [SMTPat (opt_precedes_list (l1 `List.Tot.append` l2) b)]
= List.Tot.for_all_append (Pull.pull (opt_precedes_list_item b)) l1 l2

let array_group3_empty #b : array_group3 b = fun x -> Some ([], x)
let array_group3_concat #b (a1 a3: array_group3 b) : array_group3 b =
  (fun l ->
    match a1 l with
    | None -> None
    | Some (l1, l2) ->  begin match a3 l2 with
      | None -> None
      | Some (l3, l4) -> List.Tot.append_assoc l1 l3 l4; Some (List.Tot.append l1 l3, l4)
    end
  )

let array_group3_concat_equiv
  #b
  (a1 a1' a2 a2' : array_group3 b)
: Lemma
  (requires ((a1 `array_group3_equiv` a1') /\ (a2 `array_group3_equiv` a2')))
  (ensures ((a1 `array_group3_concat` a2) `array_group3_equiv` (a1' `array_group3_concat` a2')))
= ()

let array_group3_concat_unique_strong
  #b (a1 a3: array_group3 b)
: Tot prop
= (forall (l: (l: list Cbor.raw_data_item { opt_precedes_list l b })) (l' rem: list Cbor.raw_data_item) .
    array_group3_concat a1 a3 l == Some (l', rem) <==> (
      (exists (l1 l2 l3: list Cbor.raw_data_item) .
        l == l1 `List.Tot.append` l2 /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l3, rem) /\
        l' == l1 `List.Tot.append` l3
  ))) /\
  (forall (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b })) .
    (a1 l1 == Some (l1, []) /\ Some? (a3 l2)) ==>
    a1 (l1 `List.Tot.append` l2) == Some (l1, l2)
  )

let array_group3_concat_unique_strong_prop_intro
  #b (a1 a3: array_group3 b)
  (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b }))
  (l3 rem: list Cbor.raw_data_item)
: Lemma
  (requires (
    array_group3_concat_unique_strong a1 a3 /\
    (a1 l1 == Some (l1, []) /\ a3 l2 == Some (l3, rem))
  ))
  (ensures (
      array_group3_concat a1 a3 (l1 `List.Tot.append` l2) == Some (l1 `List.Tot.append` l3, rem)
  ))
= ()

let array_group3_concat_unique_strong_prop_elim_gen
  #b (a1 a3: array_group3 b)
  (l: list Cbor.raw_data_item { opt_precedes_list l b })
  (l' rem: list Cbor.raw_data_item)
: Lemma
  (requires (
    array_group3_concat_unique_strong a1 a3 /\
    array_group3_concat a1 a3 l == Some (l', rem)
  ))
  (ensures (
      (exists (l1 l2 l3: list Cbor.raw_data_item) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l3, rem) /\
        l' == l1 `List.Tot.append` l3
  )))
= ()

let array_group3_concat_unique_strong_prop_elim
  #b (a1 a3: array_group3 b)
  (l: list Cbor.raw_data_item { opt_precedes_list l b })
: Lemma
  (requires (
    array_group3_concat_unique_strong a1 a3 /\
    array_group3_concat a1 a3 l == Some (l, [])
  ))
  (ensures (
      (exists (l1 l2: list Cbor.raw_data_item) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, []))
  ))
= array_group3_concat_unique_strong_prop_elim_gen a1 a3 l l [];
  let Some (l1, l2) = a1 l in
  let Some (l3, _) = a3 l2 in
  List.Tot.append_l_nil l3

let array_group3_concat_unique_strong_intro
  #b (a1 a3: array_group3 b)
: Lemma
  (requires (
    forall (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b })) .
      Some? (a3 l2) ==> (a1 l1 == Some (l1, []) <==> a1 (l1 `List.Tot.append` l2) == Some (l1, l2))
  ))
  (ensures (
    array_group3_concat_unique_strong a1 a3
  ))
= ()

let array_group3_concat_unique_strong_elim1
  #b (a1 a3: array_group3 b)
: Lemma
  (requires (
    array_group3_concat_unique_strong a1 a3
  ))
  (ensures (
    forall (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b })) .
      Some? (a3 l2) ==> (a1 l1 == Some (l1, []) ==> a1 (l1 `List.Tot.append` l2) == Some (l1, l2))
  ))
= ()

let indefinite_description_ghost3
  #t1 #t2 #t3
  (p: t1 -> t2 -> t3 -> prop)
: Ghost (t1 & t2 & t3)
    (requires (exists x1 x2 x3 . p x1 x2 x3))
    (ensures (fun (x1, x2, x3) -> p x1 x2 x3))
= let x1 = FStar.IndefiniteDescription.indefinite_description_ghost t1 (fun x1 -> exists x2 x3 . p x1 x2 x3) in
  let x2 = FStar.IndefiniteDescription.indefinite_description_ghost t2 (fun x2 -> exists x3 . p x1 x2 x3) in
  let x3 = FStar.IndefiniteDescription.indefinite_description_ghost t3 (fun x3 -> p x1 x2 x3) in
  (x1, x2, x3)

let array_group3_concat_unique_strong_elim2
  #b (a1 a3: array_group3 b)
: Lemma
  (requires (array_group3_concat_unique_strong a1 a3))
  (ensures (
    forall (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b })) .
      Some? (a3 l2) ==> (a1 (l1 `List.Tot.append` l2) == Some (l1, l2) ==> a1 l1 == Some (l1, []))
  ))
= let prf
      (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b }))
  : Lemma
    ((Some? (a3 l2) /\ a1 (l1 `List.Tot.append` l2) == Some (l1, l2)) ==> a1 l1 == Some (l1, []))
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (Some? (a3 l2) /\ a1 (l1 `List.Tot.append` l2) == Some ((l1 <: list _), (l2 <: list _)))
    then begin
      let Some (l3, rem) = a3 l2 in
      let l' = l1 `List.Tot.append` l3 in
      let l = l1 `List.Tot.append` l2 in
      array_group3_concat_unique_strong_prop_elim_gen a1 a3 l l' rem
    end
  in
  Classical.forall_intro_2 prf

noextract
let array_group3_concat_unique_strong'
  #b (a1 a3: array_group3 b)
: Tot prop
=
    forall (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b })) .
      Some? (a3 l2) ==> (a1 (l1 `List.Tot.append` l2) == Some (l1, l2) <==> a1 l1 == Some (l1, []))

let array_group3_concat_unique_strong_equiv
  #b (a1 a3: array_group3 b)
: Lemma
  (array_group3_concat_unique_strong a1 a3 <==> array_group3_concat_unique_strong' a1 a3)
  [SMTPat (array_group3_concat_unique_strong a1 a3)]
= Classical.move_requires (array_group3_concat_unique_strong_elim2 a1) a3

let array_group3_strong_prefix
  #b (a1: array_group3 b)
: Tot prop
= forall (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b })) .
    (a1 l1 == Some (l1, []) <==> a1 (l1 `List.Tot.append` l2) == Some (l1, l2))

let array_group3_strong_prefix_empty
  (b: option Cbor.raw_data_item)
: Lemma
  (array_group3_strong_prefix #b array_group3_empty)
= ()

let array_group3_strong_prefix_implies_concat_unique_strong
  #b (a1 a3: array_group3 b)
: Lemma
  (array_group3_strong_prefix a1 ==> array_group3_concat_unique_strong a1 a3)
= ()

let array_group3_concat_unique_strong'_strong_prefix
  #b (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_concat_unique_strong' a1 a2 /\
    array_group3_strong_prefix a2
  ))
  (ensures (
    array_group3_strong_prefix (array_group3_concat a1 a2)
  ))
= let a = array_group3_concat a1 a2 in
  let prf
    (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b }))
  : Lemma
    (a l1 == Some (l1, []) ==> a (l1 `List.Tot.append` l2) == Some (l1, l2))
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (a l1 == Some (l1, []))
    then begin
      let Some (l11, l12) = a1 l1 in
      List.Tot.append_assoc l11 l12 l2
    end
    else ()
  in
  Classical.forall_intro_2 prf

let array_group3_concat_unique_strong_strong_prefix
  #b (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_concat_unique_strong a1 a2 /\
    array_group3_strong_prefix a2
  ))
  (ensures (
    array_group3_strong_prefix (array_group3_concat a1 a2)
  ))
= array_group3_concat_unique_strong'_strong_prefix a1 a2

let array_group3_concat_unique_strong_concat
  #b (a1 a2 a3: array_group3 b)
: Lemma
  (requires (
    array_group3_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group3_concat_unique_strong a1 (array_group3_concat a2 a3)
  ))
= ()

let array_group3_choice #b (a1 a3: array_group3 b) : array_group3 b =
  fun l -> match a1 l with
    | None -> a3 l
    | Some l3 -> Some l3

let array_group3_concat_unique_strong_choice_right #b (a1 a2 a3: array_group3 b) : Lemma
  (requires (
    array_group3_concat_unique_strong a1 a2 /\
    array_group3_concat_unique_strong a1 a3
  ))
  (ensures (
    array_group3_concat_unique_strong a1 (array_group3_choice a2 a3)
  ))
= ()

let array_group3_disjoint #b (a1 a2: array_group3 b) : Tot prop
= (forall (l: list Cbor.raw_data_item { opt_precedes_list l b }) . ~ (Some? (a1 l) /\ Some? (a2 l)))

let array_group3_concat_unique_strong_choice_left #b (a1 a2 a3: array_group3 b) : Lemma
  (requires (
    array_group3_concat_unique_strong a1 a3 /\
    array_group3_concat_unique_strong a2 a3 /\
    array_group3_disjoint a1 a2
  ))
  (ensures (
    array_group3_concat_unique_strong (array_group3_choice a1 a2) a3
  ))
= ()

let array_group3_disjoint_sym #b (a1 a2: array_group3 b) : Lemma
  (array_group3_disjoint a1 a2 <==> array_group3_disjoint a2 a1)
= ()

let array_group3_disjoint_choice #b (a1 a2 a3: array_group3 b) : Lemma
  (requires (
    array_group3_disjoint a1 a2 /\
    array_group3_disjoint a1 a3
  ))
  (ensures (
    array_group3_disjoint a1 (array_group3_choice a2 a3)
  ))
= ()

let array_group3_disjoint_concat #b (a1 a2 a3: array_group3 b) : Lemma
  (requires (array_group3_disjoint a1 a2))
  (ensures (array_group3_disjoint a1 (array_group3_concat a2 a3)))
= ()

let rec array_group3_zero_or_more' #b (a: array_group3 b) (l: list Cbor.raw_data_item { opt_precedes_list l b }) : Ghost (option (list Cbor.raw_data_item & list Cbor.raw_data_item))
  (requires True)
  (ensures (fun l' -> match l' with None -> True | Some (l1, l2) -> l == l1 `List.Tot.append` l2))
  (decreases (List.Tot.length l))
=
  match a l with
  | None -> Some ([], l)
  | Some (l1, l2) ->
    List.Tot.append_length l1 l2;
    if Nil? l1
    then Some (l1, l2)
    else
      begin match array_group3_zero_or_more' a l2 with
      | None -> None
      | Some (l2', l3) -> List.Tot.append_assoc l1 l2' l3; Some (List.Tot.append l1 l2', l3)
      end

let array_group3_zero_or_more #b : array_group3 b -> array_group3 b = array_group3_zero_or_more'

let rec array_group3_zero_or_more_some
  #b
  (a: array_group3 b)
  (l: list Cbor.raw_data_item { opt_precedes_list l b })
: Lemma
  (ensures (Some? (array_group3_zero_or_more a l)))
  (decreases List.Tot.length l)
  [SMTPat (array_group3_zero_or_more a l)]
= match a l with
  | None -> ()
  | Some (l1, l2) ->
    List.Tot.append_length l1 l2;
    if Nil? l1
    then ()
    else array_group3_zero_or_more_some a l2

let array_group3_concat_unique_strong_concat_zero_or_more_right
  #b (a1 a2 a3: array_group3 b)
: Lemma
  (requires (
    array_group3_concat_unique_strong a1 a2 /\
    array_group3_concat_unique_strong a1 a3
  ))
  (ensures (
    array_group3_concat_unique_strong a1 (array_group3_concat (array_group3_zero_or_more a2) a3)
  ))
= ()

let array_group3_concat_unique_strong_zero_or_more_right
  #b (a1 a2: array_group3 b)
: Lemma
  (ensures (
    array_group3_concat_unique_strong a1 (array_group3_zero_or_more a2) <==> array_group3_strong_prefix a1
  ))
= ()

let array_group3_concat_unique_strong'_zero_or_more_left
  #b (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_disjoint a1 a2 /\
    array_group3_concat_unique_strong' a1 a1 /\
    array_group3_concat_unique_strong' a1 a2
  ))
  (ensures (
    array_group3_concat_unique_strong' (array_group3_zero_or_more a1) a2
  ))
= let _ : squash (array_group3_disjoint a1 a2) = () in
  let rec prf
    (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b }))
  : Lemma
    (ensures (
      Some? (a2 l2) ==> (array_group3_zero_or_more a1 l1 == Some (l1, []) <==> array_group3_zero_or_more a1 (l1 `List.Tot.append` l2) == Some (l1, l2))
    ))
    (decreases (List.Tot.length l1))
  = if Some? (a2 l2)
    then begin
      if FStar.StrongExcludedMiddle.strong_excluded_middle (array_group3_zero_or_more a1 l1 == Some (l1, []))
      then
        match a1 l1 with
        | None -> ()
        | Some (l1l, l1r) ->
          if Nil? l1l
          then ()
          else begin
            List.Tot.append_length l1l l1r;
            List.Tot.append_assoc l1l l1r l2;
            let Some (l1rl, l1rr) = array_group3_zero_or_more a1 l1r in
            assert (Nil? l1rr);
            List.Tot.append_l_nil l1rl;
            prf l1r l2
          end
      else if FStar.StrongExcludedMiddle.strong_excluded_middle (array_group3_zero_or_more a1 (l1 `List.Tot.append` l2) == Some (l1, l2))
      then begin
        match a1 (l1 `List.Tot.append` l2) with
        | None -> ()
        | Some (l12l, l12r) ->
          let Some (l12rl, l12rr) = array_group3_zero_or_more a1 l12r in
          assert (l12rr == l2);
          List.Tot.append_assoc l12l l12rl l2;
          List.Tot.append_length l12rl l12rr;
          List.Tot.append_length l12l l12r;
          List.Tot.append_length l1 l2;
          if Nil? l12l
          then ()
          else begin
            prf l12rl l2
          end
      end
    end
  in
  Classical.forall_intro_2 prf

let array_group3_concat_unique_strong_zero_or_more_left
  #b (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_disjoint a1 a2 /\
    array_group3_concat_unique_strong a1 a1 /\
    array_group3_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group3_concat_unique_strong (array_group3_zero_or_more a1) a2
  ))
= array_group3_concat_unique_strong'_zero_or_more_left a1 a2

let array_group3_concat_unique_weak
  #b (a1 a3: array_group3 b)
: Tot prop
= (forall (l: (l: list Cbor.raw_data_item { opt_precedes_list l b })) .
    array_group3_concat a1 a3 l == Some (l, []) ==> (
      (exists (l1 l2: list Cbor.raw_data_item) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, [])
  ))) /\
  (forall (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b })) .
    (a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, [])) ==>
    a1 (l1 `List.Tot.append` l2) == Some (l1, l2)
  )

let list_append_l_nil
  (#t: Type)
  (l: list t)
: Lemma
  (l `List.Tot.append` [] == l)
  [SMTPat (l `List.Tot.append` [])]
= List.Tot.append_l_nil l

let array_group3_concat_unique_strong_implies_weak
  #b (a1 a3: array_group3 b)
: Lemma
  (array_group3_concat_unique_strong a1 a3 ==> array_group3_concat_unique_weak a1 a3)
= ()

#push-options "--z3rlimit 16"
#restart-solver

let array_group3_concat_unique_weak_concat_zero_or_more_right
  #b (a1 a2 a3: array_group3 b)
: Lemma
  (requires (
    array_group3_concat_unique_strong a1 a2 /\
    array_group3_concat_unique_weak a1 a3
  ))
  (ensures (
    array_group3_concat_unique_weak a1 (array_group3_concat (array_group3_zero_or_more a2) a3)
  ))
= ()

#pop-options

#push-options "--z3rlimit 32"
#restart-solver

let array_group3_concat_unique_weak_zero_or_more_left'
  #b (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_disjoint a1 a2 /\
    array_group3_concat_unique_strong' a1 a1 /\
    array_group3_concat_unique_weak a1 a2
  ))
  (ensures (
    array_group3_concat_unique_weak (array_group3_zero_or_more a1) a2
  ))
= let a10 = a1 in
  let a1 = array_group3_zero_or_more a10 in
  let a3 = a2 in
  let rec prf2
    (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b }))
  : Lemma
    (ensures ((a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, [])) ==>
    a1 (l1 `List.Tot.append` l2) == Some (l1, l2)))
    (decreases (List.Tot.length l1))
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, []))
    then match a10 l1 with
    | None -> ()
    | Some (l1l, l1r) ->
      if Nil? l1l
      then ()
      else begin
        List.Tot.append_length l1l l1r;
        List.Tot.append_assoc l1l l1r l2;
        prf2 l1r l2
      end
  in
  let rec prf1
    (l: (l: list Cbor.raw_data_item { opt_precedes_list l b }))
  : Lemma
    (ensures (array_group3_concat a1 a3 l == Some (l, []) ==> (
      (exists (l1 l2: list Cbor.raw_data_item) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, [])
    ))))
    (decreases (List.Tot.length l))
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (array_group3_concat a1 a3 l == Some (l, []))
    then match a10 l with
    | None -> ()
    | Some (l1l, l1r) ->
      if Nil? l1l
      then ()
      else begin
        List.Tot.append_length l1l l1r;
        prf1 l1r;
        let Some (l2l, l2r) = a1 l1r in
        List.Tot.append_assoc l1l l2l l2r
      end
  in
  Classical.forall_intro prf1;
  Classical.forall_intro_2 prf2

#pop-options

let array_group3_concat_unique_weak_zero_or_more_left
  #b (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_disjoint a1 a2 /\
    array_group3_concat_unique_strong a1 a1 /\
    array_group3_concat_unique_weak a1 a2
  ))
  (ensures (
    array_group3_concat_unique_weak (array_group3_zero_or_more a1) a2
  ))
= array_group3_concat_unique_weak_zero_or_more_left' a1 a2

let array_group3_concat_unique_weak_zero_or_more_right
  #b (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group3_concat_unique_weak a1 (array_group3_zero_or_more a2)
  ))
= ()

#push-options "--z3rlimit 16"
#restart-solver

let array_group3_concat_unique_weak_zero_or_more'
  #b (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_concat_unique_strong' a1 a1 /\
    array_group3_concat_unique_strong' a1 a2 /\
    array_group3_disjoint a1 a2
  ))
  (ensures (
    array_group3_concat_unique_weak (array_group3_zero_or_more a1) (array_group3_zero_or_more a2)
  ))
= let a10 = a1 in
  let a1 = array_group3_zero_or_more a10 in
  let a3 = array_group3_zero_or_more a2 in
  let rec prf2
    (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b }))
  : Lemma
    (ensures ((a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, [])) ==>
    a1 (l1 `List.Tot.append` l2) == Some (l1, l2)))
    (decreases (List.Tot.length l1))
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, []))
    then match a10 l1 with
    | None -> ()
    | Some (l1l, l1r) ->
      if Nil? l1l
      then ()
      else begin
        List.Tot.append_length l1l l1r;
        List.Tot.append_assoc l1l l1r l2;
        prf2 l1r l2
      end
  in
  let rec prf1
    (l: (l: list Cbor.raw_data_item { opt_precedes_list l b }))
  : Lemma
    (ensures (array_group3_concat a1 a3 l == Some (l, []) ==> (
      (exists (l1 l2: list Cbor.raw_data_item) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, [])
    ))))
    (decreases (List.Tot.length l))
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (array_group3_concat a1 a3 l == Some (l, []))
    then match a10 l with
    | None -> ()
    | Some (l1l, l1r) ->
      if Nil? l1l
      then ()
      else begin
        List.Tot.append_length l1l l1r;
        prf1 l1r;
        let Some (l2l, l2r) = a1 l1r in
        List.Tot.append_assoc l1l l2l l2r
      end
  in
  Classical.forall_intro prf1;
  Classical.forall_intro_2 prf2

#pop-options

let array_group3_concat_unique_weak_zero_or_more
  #b (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_concat_unique_strong a1 a1 /\
    array_group3_concat_unique_strong a1 a2 /\
    array_group3_disjoint a1 a2
  ))
  (ensures (
    array_group3_concat_unique_weak (array_group3_zero_or_more a1) (array_group3_zero_or_more a2)
  ))
= array_group3_concat_unique_weak_zero_or_more' a1 a2

let array_group3_concat_unique_weak_choice_right #b (a1 a2 a3: array_group3 b) : Lemma
  (requires (
    array_group3_concat_unique_weak a1 a2 /\
    array_group3_concat_unique_weak a1 a3
  ))
  (ensures (
    array_group3_concat_unique_weak a1 (array_group3_choice a2 a3)
  ))
= ()

let array_group3_concat_unique_weak_choice_left #b (a1 a2 a3: array_group3 b) : Lemma
  (requires (
    array_group3_concat_unique_weak a1 a3 /\
    array_group3_concat_unique_weak a2 a3 /\
    array_group3_disjoint a1 a2
  ))
  (ensures (
    array_group3_concat_unique_weak (array_group3_choice a1 a2) a3
  ))
= ()

let array_group3_one_or_more #b (a: array_group3 b) : array_group3 b =
  a `array_group3_concat` array_group3_zero_or_more a

let array_group3_zero_or_one #b (a: array_group3 b) : Tot (array_group3 b) =
  a `array_group3_choice` array_group3_empty

let array_group3_item (#b: option Cbor.raw_data_item) (t: bounded_typ_gen b) : array_group3 b = fun l ->
  match l with
  | [] -> None
  | a :: q -> if t a then Some ([a], q) else None

let array_group3_item_equiv
  #b
  (t1 t2: bounded_typ_gen b)
: Lemma
  (requires (t1 `typ_equiv` t2))
  (ensures (array_group3_item t1 `array_group3_equiv` array_group3_item t2))
= ()

let match_array_group3 (#b: option Cbor.raw_data_item) (a: array_group3 b)
  (l: list Cbor.raw_data_item {opt_precedes_list l b})
: GTot bool
= match a l with
  | Some (_, l') -> Nil? l'
  | _ -> false

let t_array3 (#b: option Cbor.raw_data_item) (a: array_group3 b) : bounded_typ_gen b = fun x ->
  Cbor.Array? x &&
  match_array_group3 a (Cbor.Array?.v x)

let t_array3_equiv
  #b
  (a1 a2: array_group3 b)
: Lemma
  (requires (array_group3_equiv a1 a2))
  (ensures (typ_equiv (t_array3 a1) (t_array3 a2)))
= ()

// Recursive type (needed by COSE Section 5.1 "Recipient")

// Inspiring from Barthe et al., Type-Based Termination with Sized
// Products (CSL 2008): we allow recursion only at the level of
// destructors. In other words, instead of having a generic recursion
// combinator, we provide a recursion-enabled version only for each
// destructor combinator. We need to annotate it with a bound b (akin
// to the "size" annotation in a sized type.)

let rec t_array3_rec
  (phi: (b: Cbor.raw_data_item) -> (bounded_typ b -> array_group3 (Some b)))
  (x: Cbor.raw_data_item)
: GTot bool
  (decreases x)
=
  Cbor.Array? x &&
  match_array_group3 (phi x (t_array3_rec phi)) (Cbor.Array?.v x)
