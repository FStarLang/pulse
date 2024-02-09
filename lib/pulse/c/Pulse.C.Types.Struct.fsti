module Pulse.C.Types.Struct
open Pulse.Lib.Pervasives
include Pulse.C.Types.Fields
open Pulse.C.Typestring

// To be extracted as: struct t { fields ... }

[@@noextract_to "krml"] // primitive
val define_struct0 (tn: Type0) (#tf: Type0) (n: string) (fields: nonempty_field_description_t tf) : Tot Type0
inline_for_extraction [@@noextract_to "krml"]
let define_struct (n: string) (#tf: Type0) (#tn: Type0) (#[solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == tn))) (fields: nonempty_field_description_t tf) : Tot Type0
= define_struct0 tn #tf n fields

// To be extracted as: struct t
[@@noextract_to "krml"] // primitive
val struct_t0 (tn: Type0) (#tf: Type0) (n: string) (fields: nonempty_field_description_t tf) : Tot Type0
inline_for_extraction [@@noextract_to "krml"]
let struct_t (#tf: Type0) (n: string) (#tn: Type0) (# [solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == tn))) (fields: nonempty_field_description_t tf) : Tot Type0
= struct_t0 tn #tf n fields

val struct_set_field (#tn: Type0) (#tf: Type0) (#n: string) (#fields: nonempty_field_description_t tf) (f: field_t fields) (v: fields.fd_type f) (s: struct_t0 tn n fields) : GTot (struct_t0 tn n fields)

val struct_get_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
  (field: field_t fields)
: GTot (fields.fd_type field)

val struct_eq
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s1 s2: struct_t0 tn n fields)
: Ghost prop
  (requires True)
  (ensures (fun y ->
    (y <==> (s1 == s2)) /\
    (y <==> (forall field . struct_get_field s1 field == struct_get_field s2 field))
  ))

val struct_get_field_same
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
  (field: field_t fields)
  (v: fields.fd_type field)
: Lemma
  (struct_get_field (struct_set_field field v s) field == v)
  [SMTPat (struct_get_field (struct_set_field field v s) field)]

val struct_get_field_other
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
  (field: field_t fields)
  (v: fields.fd_type field)
  (field': field_t fields)
: Lemma
  (requires (field' <> field))
  (ensures (struct_get_field (struct_set_field field v s) field' == struct_get_field s field'))

let struct_get_field_pat
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
  (field: field_t fields)
  (v: fields.fd_type field)
  (field': field_t fields)
: Lemma
  (struct_get_field (struct_set_field field v s) field' == (if field' = field then v else struct_get_field s field'))
  [SMTPat (struct_get_field (struct_set_field field v s) field')]
= if field' = field
  then ()
  else struct_get_field_other s field v field'

[@@noextract_to "krml"] // proof-only
val struct0 (tn: Type0) (#tf: Type0) (n: string) (fields: nonempty_field_description_t tf) : Tot (typedef (struct_t0 tn n fields))

inline_for_extraction
[@@noextract_to "krml"; norm_field_attr] // proof-only
let struct (#tf: Type0) (n: string) (#tn: Type0) (# [solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == tn))) (fields: nonempty_field_description_t tf) : Tot (typedef (struct_t0 tn n fields))
= struct0 tn #tf n fields

val struct_get_field_unknown
  (tn: Type0)
  (#tf: Type0)
  (n: string)
  (fields: nonempty_field_description_t tf)
  (field: field_t fields)
: Lemma
  (struct_get_field (unknown (struct0 tn n fields)) field == unknown (fields.fd_typedef field))
  [SMTPat (struct_get_field (unknown (struct0 tn n fields)) field)]

val struct_get_field_uninitialized
  (tn: Type0)
  (#tf: Type0)
  (n: string)
  (fields: nonempty_field_description_t tf)
  (field: field_t fields)
: Lemma
  (struct_get_field (uninitialized (struct0 tn n fields)) field == uninitialized (fields.fd_typedef field))
  [SMTPat (struct_get_field (uninitialized (struct0 tn n fields)) field)]

val has_struct_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
: Tot vprop

val has_struct_field_prop
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
: stt_ghost unit
    (has_struct_field r field r')
    (fun _ -> has_struct_field r field r' ** pure (
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field
    ))

val has_struct_field_dup
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
: stt_ghost unit
    (has_struct_field r field r')
    (fun _ -> has_struct_field r field r' ** has_struct_field r field r')

val has_struct_field_inj
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t1: Type0)
  (#td1: typedef t1)
  (r1: ref td1)
  (#t2: Type0)
  (#td2: typedef t2)
  (r2: ref td2)
: stt_ghost (squash (t1 == t2 /\ td1 == td2))
    (has_struct_field r field r1 ** has_struct_field r field r2)
    (fun _ -> has_struct_field r field r1 ** has_struct_field r field r2 ** ref_equiv r1 (coerce_eq () r2))

val has_struct_field_equiv_from
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r1: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
  (r2: ref (struct0 tn n fields))
: stt_ghost unit
    (ref_equiv r1 r2 ** has_struct_field r1 field r')
    (fun _ -> ref_equiv r1 r2 ** has_struct_field r2 field r')

val has_struct_field_equiv_to
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r1' r2': ref td')
: stt_ghost unit
    (ref_equiv r1' r2' ** has_struct_field r field r1')
    (fun _ -> ref_equiv r1' r2' ** has_struct_field r field r2')

val ghost_struct_field_focus
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
: stt_ghost (squash (
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field
  ))
    (has_struct_field r field r' ** pts_to r v)
    (fun _ -> has_struct_field r field r' ** pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) ** pts_to r' (Ghost.hide (coerce_eq () (struct_get_field v field))))

val ghost_struct_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
: stt_ghost (Ghost.erased (ref (fields.fd_typedef field)))
    (pts_to r v)
    (fun r' -> pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) ** pts_to r' (struct_get_field v field) ** has_struct_field r field r')

[@@noextract_to "krml"] // primitive
val struct_field0
  (#tn: Type0)
  (#tf: Type0)
  (t': Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (td': typedef t' {
    t' ==  fields.fd_type field /\
    td' == fields.fd_typedef field
  })
: stt (ref td')
    (pts_to r v)
    (fun r' -> pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) ** pts_to r' (Ghost.hide (coerce_eq () (struct_get_field v field))) ** has_struct_field r field r')

inline_for_extraction
[@@noextract_to "krml"] // primitive
let struct_field1
  (#tn: Type0)
  (#tf: Type0)
  (t': Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (td': typedef t')
  (sq_t': squash (t' ==  fields.fd_type field))
  (sq_td': squash (td' == fields.fd_typedef field))
: stt (ref td')
    (pts_to r v)
    (fun r' -> pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) ** pts_to r' (struct_get_field v field) ** has_struct_field r field r')
= struct_field0 t' r field td'

inline_for_extraction [@@noextract_to "krml"] // primitive
let struct_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (# [ norm_fields () ] sq_t': squash (t' ==  fields.fd_type field))
  (# [ norm_fields () ] sq_td': squash (td' == fields.fd_typedef field))
  ()
: stt (ref td')
    (pts_to r v)
    (fun r' -> pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) ** pts_to r' (struct_get_field v field) ** has_struct_field r field r')
= struct_field0
    t'
    r
    field
    td'

val unstruct_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (#v': Ghost.erased t')
  (r': ref td')
: stt_ghost (Ghost.erased (struct_t0 tn n fields))
    (has_struct_field r field r' ** pts_to r v ** pts_to r' v' ** pure (
      struct_get_field v field == unknown (fields.fd_typedef field)
    ))
    (fun res -> has_struct_field r field r' ** pts_to r res ** pure (
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field /\
      Ghost.reveal res == struct_set_field field (coerce_eq () (Ghost.reveal v')) v
    ))

```pulse
ghost
fn unstruct_field_and_drop
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (#v': Ghost.erased t')
  (r': ref td')
requires
    (has_struct_field r field r' ** pts_to r v ** pts_to r' v' ** pure (
      struct_get_field v field == unknown (fields.fd_typedef field)
    ))
returns res: (Ghost.erased (struct_t0 tn n fields))
ensures
    (pts_to r res ** pure (
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field /\
      Ghost.reveal res == struct_set_field field (coerce_eq () (Ghost.reveal v')) v
    ))
{
  let res = unstruct_field r field r';
  drop_ (has_struct_field r field r');
  res
}
```

```pulse
ghost
fn unstruct_field_alt
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#v': Ghost.erased (fields.fd_type field))
  (r': ref (fields.fd_typedef field))
requires
    (has_struct_field r field r' ** pts_to r v ** pts_to r' v' ** pure (
      struct_get_field v field == unknown (fields.fd_typedef field)
    ))
returns s': (Ghost.erased (struct_t0 tn n fields))
ensures
    (has_struct_field r field r' ** pts_to r s' ** pure (
      Ghost.reveal s' == struct_set_field field v' v
    ))
{
  unstruct_field r field r'
}
```

val fractionable_struct
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
: Lemma
  (fractionable (struct0 tn n fields) s <==> (forall field . fractionable (fields.fd_typedef field) (struct_get_field s field)))
  [SMTPat (fractionable (struct0 tn n fields) s)]

val mk_fraction_struct
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
  (p: perm)
  (field: field_t fields)
: Lemma
  (requires (fractionable (struct0 tn n fields) s))
  (ensures (struct_get_field (mk_fraction (struct0 tn n fields) s p) field == mk_fraction (fields.fd_typedef field) (struct_get_field s field) p))
  [SMTPat (struct_get_field (mk_fraction (struct0 tn n fields) s p) field)]

(*
val mk_fraction_struct_recip
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
  (p: perm)
: Ghost (struct_t0 tn n fields)
  (requires (
    (forall field . exists v . fractionable (fields.fd_typedef field) v /\ struct_get_field s field == mk_fraction (fields.fd_typedef field) v p)
  ))
  (ensures (fun s' ->
    fractionable (struct0 tn n fields) s' /\
    s == mk_fraction (struct0 tn n fields) s' p
  ))
*)

val full_struct
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
: Lemma
  (full (struct0 tn n fields) s <==> (forall field . full (fields.fd_typedef field) (struct_get_field s field)))
  [SMTPat (full (struct0 tn n fields) s)]
