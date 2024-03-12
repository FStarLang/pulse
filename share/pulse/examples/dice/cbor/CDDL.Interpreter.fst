module CDDL.Interpreter
open Pulse.Lib.Pervasives

open CDDL.Pulse
module Spec = CDDL.Spec
module U64 = FStar.UInt64

noeq
type elem_typ =
| TDef: (i: nat) -> elem_typ
| TFalse
| TTrue
| TBool
| TNil
| TNull
| TUndefined
| TUIntLiteral: (v: U64.t) -> elem_typ
| TArray: (i: nat) -> elem_typ

noeq
type typ =
| TElem: (t: elem_typ) -> typ
| TChoice: (l: list elem_typ) -> typ
// | TMap

noeq
type atom_array_group =
| TADef: (i: nat) -> atom_array_group
| TAElem: (t: elem_typ) -> atom_array_group

noeq
type elem_array_group =
| TAAtom: (t: atom_array_group) -> elem_array_group
| TAZeroOrMore: (t: atom_array_group) -> elem_array_group

type array_group = list (string & elem_array_group)

let nat_up_to (n: nat) = (x: nat { x < n })

[@@erasable]
noeq
type semenv_elem =
| SEType of Spec.typ
| SEArrayGroup of Spec.array_group3 None

noeq
type semenv = {
  se_bound: nat;
  se_env: (nat_up_to se_bound -> semenv_elem);
}

let se_typ
  (se: semenv)
  (i: nat_up_to se.se_bound)
: Tot Spec.typ
= match se.se_env i with
  | SEType t -> t
  | _ -> Spec.t_false

let se_array_group
  (se: semenv)
  (i: nat_up_to se.se_bound)
: Tot (Spec.array_group3 None)
= match se.se_env i with
  | SEArrayGroup t -> t
  | _ -> Spec.array_group3_always_false

let semenv_included (s1 s2: semenv) : Tot prop =
  s1.se_bound <= s2.se_bound /\
  (forall (i: nat_up_to s1.se_bound) . s1.se_env i == s2.se_env i)

let elem_typ_bounded
  (bound: nat)
  (t: elem_typ)
: Tot bool
= match t with
  | TDef i -> i < bound
  | TArray j -> j < bound
  | _ -> true

let elem_typ_sem
  (env: semenv)
  (t: elem_typ)
: Pure Spec.typ
  (requires elem_typ_bounded env.se_bound t)
  (ensures fun _ -> True)
= match t with
  | TDef i -> se_typ env i
  | TArray i -> Spec.t_array3 (se_array_group env i)
  | TFalse -> Spec.t_false
  | TTrue -> Spec.t_true
  | TBool -> Spec.t_bool
  | TNil -> Spec.t_nil
  | TNull -> Spec.t_null
  | TUndefined -> Spec.t_undefined
  | TUIntLiteral n -> Spec.t_uint_literal n

let elem_typ_sem_included (s1 s2: semenv) (t: elem_typ) : Lemma
  (requires 
    semenv_included s1 s2 /\
    elem_typ_bounded s1.se_bound t
  )
  (ensures
    elem_typ_bounded s1.se_bound t /\
    elem_typ_bounded s2.se_bound t /\
    elem_typ_sem s2 t == elem_typ_sem s1 t
  )
= ()

// module Pull = FStar.Ghost.Pull

let rec sem_typ_choice
  (env: semenv)
  (l: list elem_typ)
: Pure Spec.typ
    (requires List.Tot.for_all (elem_typ_bounded env.se_bound) l)
    (ensures fun _ -> True)
    (decreases l)
= match l with
  | [] -> Spec.t_false
  | [t] -> elem_typ_sem env t
  | a :: q -> elem_typ_sem env a `Spec.t_choice` sem_typ_choice env q

let typ_bounded
  (bound: nat)
  (t: typ)
: Tot bool
= match t with
  | TElem t -> elem_typ_bounded bound t
  | TChoice l -> List.Tot.for_all (elem_typ_bounded bound) l

let typ_sem
  (env: semenv)
  (t: typ)
: Pure Spec.typ
  (requires typ_bounded env.se_bound t)
  (ensures fun _ -> True)
= match t with
  | TElem t -> elem_typ_sem env t
  | TChoice l -> sem_typ_choice env l

let atom_array_group_bounded
  (bound: nat)
  (t: atom_array_group)
: Tot bool
= match t with
  | TADef i -> i < bound
  | TAElem t -> elem_typ_bounded bound t

let elem_array_group_bounded
  (bound: nat)
  (t: elem_array_group)
: Tot bool
= match t with
  | TAAtom t -> atom_array_group_bounded bound t
  | TAZeroOrMore t -> atom_array_group_bounded bound t

let array_group_bounded
  (bound: nat)
  (t: array_group)
: Tot bool
= List.Tot.for_all (elem_array_group_bounded bound) (List.Tot.map snd t)

let atom_array_group_sem
  (env: semenv)
  (t: atom_array_group)
: Pure (Spec.array_group3 None)
    (requires atom_array_group_bounded env.se_bound t)
    (ensures fun _ -> True)
= match t with
  | TADef i -> se_array_group env i
  | TAElem j -> Spec.array_group3_item (elem_typ_sem env j)

let elem_array_group_sem
  (env: semenv)
  (t: elem_array_group)
: Pure (Spec.array_group3 None)
    (requires elem_array_group_bounded env.se_bound t)
    (ensures fun _ -> True)
= match t with
  | TAAtom i -> atom_array_group_sem env i
  | TAZeroOrMore i -> Spec.array_group3_zero_or_more (atom_array_group_sem env i)

let rec array_group_sem
  (env: semenv)
  (t: array_group)
: Pure (Spec.array_group3 None)
    (requires array_group_bounded env.se_bound t)
    (ensures fun _ -> True)
    (decreases t)
= match t with
  | [] -> Spec.array_group3_empty
  | [_, t] -> elem_array_group_sem env t
  | (_, t) :: q -> Spec.array_group3_concat (elem_array_group_sem env t) (array_group_sem env q)
