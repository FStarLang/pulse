module Pulse.C.Types.Base
open Pulse.Lib.Pervasives

/// Helper to compose two permissions into one
val prod_perm (p1 p2: perm) : Pure perm
  (requires True)
  (ensures (fun p ->
    ((p1 `lesser_equal_perm` full_perm /\ p2 `lesser_equal_perm` full_perm) ==>
    p `lesser_equal_perm` full_perm) /\
    p.v == (let open FStar.Real in p1.v *. p2.v)
  ))

[@@noextract_to "krml"] // proof-only
val typedef (t: Type0) : Type0

inline_for_extraction [@@noextract_to "krml"]
let typeof (#t: Type0) (td: typedef t) : Tot Type0 = t

val fractionable (#t: Type0) (td: typedef t) (x: t) : GTot prop

val mk_fraction (#t: Type0) (td: typedef t) (x: t) (p: perm) : Ghost t
  (requires (fractionable td x))
  (ensures (fun y -> p `lesser_equal_perm` full_perm ==> fractionable td y))

val mk_fraction_full (#t: Type0) (td: typedef t) (x: t) : Lemma
  (requires (fractionable td x))
  (ensures (mk_fraction td x full_perm == x))
  [SMTPat (mk_fraction td x full_perm)]

val mk_fraction_compose (#t: Type0) (td: typedef t) (x: t) (p1 p2: perm) : Lemma
  (requires (fractionable td x /\ p1 `lesser_equal_perm` full_perm /\ p2 `lesser_equal_perm` full_perm))
  (ensures (mk_fraction td (mk_fraction td x p1) p2 == mk_fraction td x (p1 `prod_perm` p2)))

val full (#t: Type0) (td: typedef t) (v: t) : GTot prop

val uninitialized (#t: Type0) (td: typedef t) : Ghost t
  (requires True)
  (ensures (fun y -> full td y /\ fractionable td y))

val unknown (#t: Type0) (td: typedef t) : Ghost t
  (requires True)
  (ensures (fun y -> fractionable td y))

val full_not_unknown
  (#t: Type)
  (td: typedef t)
  (v: t)
: Lemma
  (requires (full td v))
  (ensures (~ (v == unknown td)))
  [SMTPat (full td v)]

val mk_fraction_unknown (#t: Type0) (td: typedef t) (p: perm) : Lemma
  (ensures (mk_fraction td (unknown td) p == unknown td))

val mk_fraction_eq_unknown (#t: Type0) (td: typedef t) (v: t) (p: perm) : Lemma
  (requires (fractionable td v /\ mk_fraction td v p == unknown td))
  (ensures (v == unknown td))


// To be extracted as: void*

[@@noextract_to "krml"] // primitive
val void_ptr : Type0
 
// To be extracted as: NULL
[@@noextract_to "krml"] // primitive
val void_null: void_ptr

// To be extracted as: *t
[@@noextract_to "krml"] // primitive
val ptr_gen ([@@@unused] t: Type) : Type0
[@@noextract_to "krml"] // primitive
val null_gen (t: Type) : Tot (ptr_gen t)

val ghost_void_ptr_of_ptr_gen (#[@@@unused] t: Type) (x: ptr_gen t) : GTot void_ptr
val ghost_ptr_gen_of_void_ptr (x: void_ptr) ([@@@unused] t: Type) : GTot (ptr_gen t)

val ghost_void_ptr_of_ptr_gen_of_void_ptr
  (x: void_ptr)
  (t: Type)
: Lemma
  (ghost_void_ptr_of_ptr_gen (ghost_ptr_gen_of_void_ptr x t) == x)
  [SMTPat (ghost_void_ptr_of_ptr_gen (ghost_ptr_gen_of_void_ptr x t))]

val ghost_ptr_gen_of_void_ptr_of_ptr_gen
  (#t: Type)
  (x: ptr_gen t)
: Lemma
  (ghost_ptr_gen_of_void_ptr (ghost_void_ptr_of_ptr_gen x) t == x)
  [SMTPat (ghost_ptr_gen_of_void_ptr (ghost_void_ptr_of_ptr_gen x) t)]

inline_for_extraction [@@noextract_to "krml"] // primitive
let ptr (#t: Type) (td: typedef t) : Tot Type0 = ptr_gen t
inline_for_extraction [@@noextract_to "krml"] // primitive
let null (#t: Type) (td: typedef t) : Tot (ptr td) = null_gen t

inline_for_extraction [@@noextract_to "krml"]
let ref (#t: Type) (td: typedef t) : Tot Type0 = (p: ptr td { ~ (p == null td) })

val pts_to (#t: Type) (#td: typedef t) (r: ref td) (v: Ghost.erased t) : vprop

let pts_to_or_null
  (#t: Type) (#td: typedef t) (p: ptr td) (v: Ghost.erased t) : vprop
= if FStar.StrongExcludedMiddle.strong_excluded_middle (p == null _)
  then emp
  else pts_to p v

[@@noextract_to "krml"] // primitive
val is_null
  (#t: Type)
//  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (p: ptr td)
// : STAtomicBase bool false opened Unobservable
: stt bool
    (pts_to_or_null p v)
    (fun res -> pts_to_or_null p v ** pure (
      res == true <==> p == null _
    ))

val assert_null
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (p: ptr td)
: stt_ghost unit
    (pts_to_or_null p v ** pure (
      p == null _
    ))
    (fun _ -> emp)
// = rewrite (pts_to_or_null p v) emp

val assert_not_null
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (p: ptr td)
: stt_ghost (squash (~ (p == null _)))
    (pts_to_or_null p v ** pure (
      ~ (p == null _)
    ))
    (fun _ -> pts_to p v)
// = rewrite (pts_to_or_null p v) (pts_to p v)

[@@noextract_to "krml"] // primitive
// val void_ptr_of_ptr (#t: Type) (#opened: _) (#td: typedef t) (#v: Ghost.erased t) (x: ptr td) : STAtomicBase void_ptr false opened Unobservable
val void_ptr_of_ptr (#t: Type) (#td: typedef t) (#v: Ghost.erased t) (x: ptr td) : stt void_ptr
  (pts_to_or_null x v)
  (fun y -> pts_to_or_null x v ** pure (
    y == ghost_void_ptr_of_ptr_gen x
  ))

// [@@noextract_to "krml"] inline_for_extraction
// let void_ptr_of_ref (#t: Type) (#opened: _) (#td: typedef t) (#v: Ghost.erased t) (x: ref td) : STAtomicBase void_ptr false opened Unobservable
val void_ptr_of_ref (#t: Type) (#td: typedef t) (#v: Ghost.erased t) (x: ref td) : stt void_ptr
  (pts_to x v)
  (fun y -> pts_to x v ** pure (
    y == ghost_void_ptr_of_ptr_gen x
  ))
(*
= rewrite (pts_to x v) (pts_to_or_null x v);
  let res = void_ptr_of_ptr x in
  rewrite (pts_to_or_null x v) (pts_to x v);
  return res
*)

[@@noextract_to "krml"] // primitive
// val ptr_of_void_ptr (#t: Type) (#opened: _) (#td: typedef t) (#v: Ghost.erased t) (x: void_ptr) : STAtomicBase (ptr td) false opened Unobservable
val ptr_of_void_ptr (#t: Type) (#td: typedef t) (#v: Ghost.erased t) (x: void_ptr) : stt (ptr td)
  (pts_to_or_null (ghost_ptr_gen_of_void_ptr x t <: ptr td) v)
  (fun y -> pts_to_or_null y v ** pure (
    y == ghost_ptr_gen_of_void_ptr x t
  ))

// [@@noextract_to "krml"] inline_for_extraction
// let ref_of_void_ptr (#t: Type) (#opened: _) (#td: typedef t) (#v: Ghost.erased t) (x: void_ptr) (y': Ghost.erased (ref td)) : STAtomicBase (ref td) false opened Unobservable
val ref_of_void_ptr (#t: Type) (#td: typedef t) (#v: Ghost.erased t) (x: void_ptr) (y': Ghost.erased (ref td)) : stt (ref td)
  (pts_to y' v ** pure (
    Ghost.reveal y' == ghost_ptr_gen_of_void_ptr x t
  ))
  (fun y -> pts_to y v ** pure (
    y == Ghost.reveal y'
  ))
(*
= rewrite (pts_to y' v) (pts_to_or_null (ghost_ptr_gen_of_void_ptr x t <: ptr td) v);
  let y = ptr_of_void_ptr x in
  rewrite (pts_to_or_null y v) (pts_to y v);
  return y
*)

val ref_equiv
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
: Tot vprop

val pts_to_equiv
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
  (v: Ghost.erased t)
: stt_ghost unit
    (ref_equiv r1 r2 ** pts_to r1 v)
    (fun _ -> ref_equiv r1 r2 ** pts_to r2 v)

val freeable
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
: Tot vprop

val freeable_dup
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
: stt_ghost unit
    (freeable r)
    (fun _ -> freeable r ** freeable r)

val freeable_equiv
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
: stt_ghost unit
    (ref_equiv r1 r2 ** freeable r1)
    (fun _ -> ref_equiv r1 r2 ** freeable r2)

let freeable_or_null
  (#t: Type)
  (#td: typedef t)
  (r: ptr td)
: Tot vprop
= if FStar.StrongExcludedMiddle.strong_excluded_middle (r == null _)
  then emp
  else freeable r

(*
let freeable_or_null_dup
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: ptr td)
: SteelGhostT vprop opened
    (freeable_or_null r)
    (fun _ -> freeable_or_null r ** freeable_or_null r)
= if FStar.StrongExcludedMiddle.strong_excluded_middle (r == null _)
  then ()
  else freeable r
*)

[@@noextract_to "krml"] // primitive
val alloc
  (#t: Type)
  (td: typedef t)
: stt (ptr td)
    emp
    (fun p -> pts_to_or_null p (uninitialized td) ** freeable_or_null p)

[@@noextract_to "krml"] // primitive
val free
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
: stt unit
    (pts_to r v ** freeable r ** pure (
      full td v
    ))
    (fun _ -> emp)

val mk_fraction_split_gen
  (#t: Type) (#td: typedef t) (r: ref td) (v: t { fractionable td v }) (p p1 p2: perm)
: stt_ghost unit
  (pts_to r (mk_fraction td v p) ** pure (
    p == p1 `sum_perm` p2 /\ p `lesser_equal_perm` full_perm
  ))
  (fun _ -> pts_to r (mk_fraction td v p1) ** pts_to r (mk_fraction td v p2))

val mk_fraction_split
  (#t: Type) (#td: typedef t) (r: ref td) (v: Ghost.erased t { fractionable td v }) (p1 p2: perm)
: stt_ghost unit
  (pts_to r v ** pure (
    full_perm == p1 `sum_perm` p2
  ))
  (fun _ -> pts_to r (mk_fraction td v p1) ** pts_to r (mk_fraction td v p2))
(*
= mk_fraction_full td v;
  rewrite (pts_to _ _) (pts_to _ _);
  mk_fraction_split_gen r v full_perm p1 p2
*)

val mk_fraction_join
  (#t: Type) (#td: typedef t) (r: ref td) (v: t { fractionable td v }) (p1 p2: perm)
: stt_ghost unit
  (pts_to r (mk_fraction td v p1) ** pts_to r (mk_fraction td v p2))
  (fun _ -> pts_to r (mk_fraction td v (p1 `sum_perm` p2)))

val fractional_permissions_theorem
  (#t: Type)
  (#td: typedef t)
  (v1: t { fractionable td v1 })
  (v2: t { fractionable td v2 })
  (p1 p2: perm)
  (r: ref td)
: stt_ghost unit
    (pts_to r (mk_fraction td v1 p1) ** pts_to r (mk_fraction td v2 p2) ** pure (
      full td v1 /\ full td v2
    ))
    (fun _ -> pts_to r (mk_fraction td v1 p1) ** pts_to r (mk_fraction td v2 p2) ** pure (
      v1 == v2 /\ (p1 `sum_perm` p2) `lesser_equal_perm` full_perm
    ))

[@@noextract_to "krml"] // primitive
val copy
  (#t: Type)
  (#td: typedef t)
  (#v_src: Ghost.erased t { full td v_src /\ fractionable td v_src })
  (#p_src: perm)
  (#v_dst: Ghost.erased t { full td v_dst })
  (src: ref td)
  (dst: ref td)
: stt unit
    (pts_to src (mk_fraction td v_src p_src) ** pts_to dst v_dst)
    (fun _ -> pts_to src (mk_fraction td v_src p_src) ** pts_to dst v_src)

val norm_field_attr : unit

noextract
let norm_field_steps = [
  delta_attr [`%norm_field_attr];
  iota; zeta; primops;
]
