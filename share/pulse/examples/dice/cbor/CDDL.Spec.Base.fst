module CDDL.Spec.Base
module Cbor = CBOR.Spec
module U8 = FStar.UInt8
module U64 = FStar.UInt64

// Concise Data Definition Language (RFC 8610)

noextract
let opt_precedes
  (#t1 #t2: Type)
  (x1: t1)
  (x2: option t2)
: Tot prop
= match x2 with
  | None -> True
  | Some x2 -> x1 << x2

[@@noextract_to "krml"]
let bounded_typ_gen (e: option Cbor.raw_data_item) = (e': Cbor.raw_data_item { opt_precedes e' e }) -> GTot bool  // GTot needed because of the .cbor control (staged serialization)

[@@noextract_to "krml"]
let typ = bounded_typ_gen None

let any : typ = (fun _ -> true)
let t_always_false : typ = (fun _ -> false)

[@@noextract_to "krml"]
let bounded_typ (e: Cbor.raw_data_item) = bounded_typ_gen (Some e)

let coerce_to_bounded_typ
  (b: option Cbor.raw_data_item)
  (t: typ)
: Tot (bounded_typ_gen b)
= t

noextract
let typ_equiv
  (#b: option Cbor.raw_data_item)
  (t1 t2: bounded_typ_gen b)
: Tot prop
= forall x . t1 x == t2 x

let typ_disjoint (a1 a2: typ) : Tot prop
= (forall (l: Cbor.raw_data_item) . ~ (a1 l /\ a2 l))

let t_literal (i: Cbor.raw_data_item) : typ =
  (fun x -> FStar.StrongExcludedMiddle.strong_excluded_middle (x == i))

let t_choice (#b: option Cbor.raw_data_item) (t1 t2: bounded_typ_gen b) : bounded_typ_gen b = (fun x -> t1 x || t2 x)

let t_choice_equiv
  #b
  (t1 t1' t2 t2' : bounded_typ_gen b)
: Lemma
  (requires (t1 `typ_equiv` t1' /\ t2 `typ_equiv` t2'))
  (ensures ((t1 `t_choice` t2) `typ_equiv` (t1' `t_choice` t2')))
= ()
// etc.

let t_choice_simpl
  #b
  (t: bounded_typ_gen b)
: Lemma
  ((t `t_choice` t) `typ_equiv` t)
= ()
