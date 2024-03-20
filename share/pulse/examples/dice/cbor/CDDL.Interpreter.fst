module CDDL.Interpreter
open Pulse.Lib.Pervasives

open CDDL.Pulse
module Spec = CDDL.Spec
module U64 = FStar.UInt64

type elem_typ =
| TDef: (i: nat) -> elem_typ
| TFalse
| TTrue
| TBool
| TNil
| TUndefined
| TUIntLiteral: (v: U64.t) -> elem_typ
| TArray: (i: nat) -> elem_typ

type typ =
| TElem: (t: elem_typ) -> typ
| TChoice: (l: list elem_typ) -> typ
| TTag: (tag: U64.t) -> (i: elem_typ) -> typ
// | TMap

type atom_array_group =
| TADef: (i: nat) -> atom_array_group
| TAElem: (t: elem_typ) -> atom_array_group

type elem_array_group =
| TAAtom: (t: atom_array_group) -> elem_array_group
| TAZeroOrMore: (t: atom_array_group) -> elem_array_group

type array_group = list (string & elem_array_group)

let nat_up_to (n: nat) = (x: nat { x < n })

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
  | _ -> Spec.t_always_false

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
  | [] -> Spec.t_always_false
  | [t] -> elem_typ_sem env t
  | a :: q -> elem_typ_sem env a `Spec.t_choice` sem_typ_choice env q

let typ_bounded
  (bound: nat)
  (t: typ)
: Tot bool
= match t with
  | TElem t -> elem_typ_bounded bound t
  | TChoice l -> List.Tot.for_all (elem_typ_bounded bound) l
  | TTag _tag t -> elem_typ_bounded bound t

let typ_sem
  (env: semenv)
  (t: typ)
: Pure Spec.typ
  (requires typ_bounded env.se_bound t)
  (ensures fun _ -> True)
= match t with
  | TElem t -> elem_typ_sem env t
  | TChoice l -> sem_typ_choice env l
  | TTag tag t -> Spec.t_tag tag (elem_typ_sem env t)

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

let array_group_bounded_append
  (bound: nat)
  (t1 t2: array_group)
: Lemma
  (requires (array_group_bounded bound t1 /\
    array_group_bounded bound t2
  ))
  (ensures
    array_group_bounded bound (t1 `List.Tot.append` t2)
  )
  [SMTPat (array_group_bounded bound (t1 `List.Tot.append` t2))]
= List.Tot.map_append snd t1 t2;
  List.Tot.for_all_append (elem_array_group_bounded bound) (List.Tot.map snd t1) (List.Tot.map snd t2)

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

let spec_close_array_group
  (#b: _)
  (t: Spec.array_group3 b)
: Tot (Spec.array_group3 b)
= fun l ->
    let res = t l in
    match res with
    | Some (_, []) -> res
    | _ -> None

let array_group3_concat_close
  (#b: _)
  (a1 a2: Spec.array_group3 b)
: Lemma
  (Spec.array_group3_equiv
    (spec_close_array_group (Spec.array_group3_concat a1 a2))
    (Spec.array_group3_concat a1 (spec_close_array_group a2))
  )
= ()

let spec_array3_close_array_group
  (#b: _)
  (a: Spec.array_group3 b)
: Lemma
  (Spec.typ_equiv
    (Spec.t_array3 a)
    (Spec.t_array3 (spec_close_array_group a))
  )
= ()

let spec_maybe_close_array_group
  (#b: _)
  (t: Spec.array_group3 b)
  (close: bool)
: Tot (Spec.array_group3 b)
= if close
  then spec_close_array_group t
  else t

let array_group3_concat_assoc
  (#b: _)
  (a1 a2 a3: Spec.array_group3 b)
: Lemma
  (Spec.array_group3_concat a1 (Spec.array_group3_concat a2 a3) `Spec.array_group3_equiv`
    Spec.array_group3_concat (Spec.array_group3_concat a1 a2) a3)
  [SMTPatOr [
    [SMTPat (Spec.array_group3_concat a1 (Spec.array_group3_concat a2 a3))];
    [SMTPat (Spec.array_group3_concat (Spec.array_group3_concat a1 a2) a3)]
  ]]
= let prf
    (l: list CBOR.Spec.raw_data_item { Spec.opt_precedes_list l b})
  : Lemma
    (Spec.array_group3_concat a1 (Spec.array_group3_concat a2 a3) l ==
      Spec.array_group3_concat (Spec.array_group3_concat a1 a2) a3 l)
  = match a1 l with
    | None -> ()
    | Some (l1, lr1) ->
      begin match a2 lr1 with
      | None -> ()
      | Some (l2, lr2) ->
        begin match a3 lr2 with
        | None -> ()
        | Some (l3, lr3) -> List.Tot.append_assoc l1 l2 l3
        end
      end
  in
  Classical.forall_intro prf

let array_group_sem_alt
  (env: semenv)
  (t: array_group)
: Pure (Spec.array_group3 None)
    (requires array_group_bounded env.se_bound t)
    (ensures fun y -> y `Spec.array_group3_equiv` array_group_sem env t)
    (decreases t)
= match t with
  | [] -> Spec.array_group3_empty
  | (_, t) :: q -> Spec.array_group3_concat (elem_array_group_sem env t) (array_group_sem env q)

let rec array_group_sem_append
  (env: semenv)
  (t1 t2: array_group)
: Lemma
  (requires
    array_group_bounded env.se_bound t1 /\
    array_group_bounded env.se_bound t2
  )
  (ensures
    array_group_bounded env.se_bound (t1 `List.Tot.append` t2) /\
    Spec.array_group3_equiv
      (array_group_sem env (t1 `List.Tot.append` t2))
      (Spec.array_group3_concat
        (array_group_sem env t1)
        (array_group_sem env t2)
      )
  )
  (decreases t1)
  [SMTPat (array_group_sem env (t1 `List.Tot.append` t2))]
= match t1 with
  | [] -> ()
  | [_] -> ()
  | _ :: q1 -> array_group_sem_append env q1 t2

noeq
type env = {
  e_semenv: semenv;
  e_typ: (i: nat_up_to e_semenv.se_bound { SEType? (e_semenv.se_env i) } -> (t: typ { 
    typ_bounded e_semenv.se_bound t /\
    Spec.typ_equiv (typ_sem e_semenv t) (se_typ e_semenv i)
  }));
  e_array_group: (i: nat_up_to e_semenv.se_bound { SEArrayGroup? (e_semenv.se_env i) } -> (a: array_group {
    array_group_bounded e_semenv.se_bound a /\
    Spec.array_group3_equiv (array_group_sem e_semenv a) (se_array_group e_semenv i)
  }));
}

let spec_array_group3_zero_or_more_equiv #b
 (a1 a2: Spec.array_group3 b)
: Lemma
  (requires Spec.array_group3_equiv a1 a2)
  (ensures Spec.array_group3_equiv (Spec.array_group3_zero_or_more a1) (Spec.array_group3_zero_or_more a2))
  [SMTPat (Spec.array_group3_equiv (Spec.array_group3_zero_or_more a1) (Spec.array_group3_zero_or_more a2))]
= admit ()

// This is nothing more than delta-equivalence

#push-options "--z3rlimit 16"

let rec typ_equiv
  (e: env)
  (fuel: nat)
  (t1: typ)
  (t2: typ)
: Pure bool
  (requires (
    typ_bounded e.e_semenv.se_bound t1 /\
    typ_bounded e.e_semenv.se_bound t2
  ))
  (ensures (fun b ->
    typ_bounded e.e_semenv.se_bound t1 /\
    typ_bounded e.e_semenv.se_bound t2 /\
    (b == true ==> Spec.typ_equiv (typ_sem e.e_semenv t1) (typ_sem e.e_semenv t2))
  ))
  (decreases fuel)
= if t1 = t2
  then true
  else if fuel = 0
  then false
  else let fuel' : nat = fuel - 1 in
  match t1, t2 with
  | TElem (TDef i), _ ->
    let s1 = e.e_semenv.se_env i in
    if SEType? s1
    then
      let t1' = e.e_typ i in
      typ_equiv e fuel' t1' t2
    else false
  | _, TElem (TDef _) ->
    typ_equiv e fuel' t2 t1
  | TChoice [], TChoice [] -> true
  | TChoice (t1' :: q1'), TChoice (t2' :: q2') ->
    if typ_equiv e fuel' (TElem t1') (TElem t2')
    then typ_equiv e fuel' (TChoice q1') (TChoice q2')
    else false
  | TTag tag1 t1, TTag tag2 t2 ->
    if tag1 <> tag2
    then false
    else typ_equiv e fuel' (TElem t1) (TElem t2)
  | TElem (TArray i1), TElem (TArray i2) ->
    let s1 = e.e_semenv.se_env i1 in
    let s2 = e.e_semenv.se_env i2 in
    if SEArrayGroup? s1 && SEArrayGroup? s2
    then
      let t1' = e.e_array_group i1 in
      let t2' = e.e_array_group i2 in
      array_group_equiv e fuel' t1' t2'
    else false
  | _ -> false

and array_group_equiv
  (e: env)
  (fuel: nat)
  (t1: array_group)
  (t2: array_group)
: Pure bool
  (requires (
    array_group_bounded e.e_semenv.se_bound t1 /\
    array_group_bounded e.e_semenv.se_bound t2
  ))
  (ensures (fun b ->
    array_group_bounded e.e_semenv.se_bound t1 /\
    array_group_bounded e.e_semenv.se_bound t2 /\
    (b == true ==> Spec.array_group3_equiv (array_group_sem e.e_semenv t1) (array_group_sem e.e_semenv t2))
  ))
  (decreases fuel)
= if t1 = t2
  then true
  else if fuel = 0
  then false
  else let fuel' : nat = fuel - 1 in
  match t1, t2 with
  | [], [] -> true
  | (_, TAAtom (TADef i1)) :: q1', _ ->
    let s1 = e.e_semenv.se_env i1 in
    if SEArrayGroup? s1
    then
      let t1' = e.e_array_group i1 in
      array_group_equiv e fuel' (t1' `List.Tot.append` q1') t2
    else false
  | _, (_, TAAtom (TADef _)) :: _ ->
    array_group_equiv e fuel' t2 t1
  | (_, TAAtom (TAElem t1)) :: q1, (_, TAAtom (TAElem t2)) :: q2 ->
    if typ_equiv e fuel' (TElem t1) (TElem t2)
    then array_group_equiv e fuel' q1 q2
    else false
  | (s1, TAZeroOrMore t1) :: q1, (s2, TAZeroOrMore t2) :: q2 ->
    if array_group_equiv e fuel' [s1, TAAtom t1] [s2, TAAtom t2]
    then begin
       assert (Spec.array_group3_equiv (atom_array_group_sem e.e_semenv t1) (atom_array_group_sem e.e_semenv t2));
       assert (Spec.array_group3_equiv (Spec.array_group3_zero_or_more (atom_array_group_sem e.e_semenv t1)) (Spec.array_group3_zero_or_more (atom_array_group_sem e.e_semenv t2)));
       array_group_equiv e fuel' q1 q2
    end
    else false
  | _ -> false

#pop-options

let spec_typ_disjoint (a1 a2: Spec.typ) : Tot prop
= (forall (l: CBOR.Spec.raw_data_item) . ~ (a1 l /\ a2 l))

#push-options "--z3rlimit 32"

#restart-solver
let rec typ_disjoint
  (e: env)
  (fuel: nat)
  (t1: typ)
  (t2: typ)
: Pure bool
  (requires (
    typ_bounded e.e_semenv.se_bound t1 /\
    typ_bounded e.e_semenv.se_bound t2
  ))
  (ensures (fun b ->
    typ_bounded e.e_semenv.se_bound t1 /\
    typ_bounded e.e_semenv.se_bound t2 /\
    (b == true ==> spec_typ_disjoint (typ_sem e.e_semenv t1) (typ_sem e.e_semenv t2))
  ))
  (decreases fuel)
= if fuel = 0
  then false
  else let fuel' : nat = fuel - 1 in
  match t1, t2 with
  | TElem (TDef i), _ ->
    let s1 = e.e_semenv.se_env i in
    if SEType? s1
    then
      let t1' = e.e_typ i in
      typ_disjoint e fuel' t1' t2
    else true
  | _, TElem (TDef _) ->
    typ_disjoint e fuel' t2 t1
  | TChoice [], _ -> true
  | TChoice (t1' :: q1'), _ ->
    if not (typ_disjoint e fuel' (TElem t1') t2)
    then false
    else typ_disjoint e fuel' (TChoice q1') t2
  | _, TChoice _ ->
    typ_disjoint e fuel' t2 t1
  | TTag tag1 t1, TTag tag2 t2 ->
    if tag1 <> tag2
    then true
    else typ_disjoint e fuel' (TElem t1) (TElem t2)
  | _, TTag _ _
  | TTag _ _, _ -> true
  | TElem (TArray i1), TElem (TArray i2) ->
    let s1 = e.e_semenv.se_env i1 in
    let s2 = e.e_semenv.se_env i2 in
    if SEArrayGroup? s1 && SEArrayGroup? s2
    then begin
      let t1' = e.e_array_group i1 in
      let t2' = e.e_array_group i2 in
      spec_array3_close_array_group (SEArrayGroup?._0 s1);
      spec_array3_close_array_group (SEArrayGroup?._0 s2);
      array_group_disjoint e fuel' true t1' t2'
    end
    else true
  | TElem TBool, TElem TFalse
  | TElem TBool, TElem TTrue -> false
  | _, TElem TBool ->
    typ_disjoint e fuel' t2 t1
  | TElem e1, TElem e2 -> e1 <> e2

and array_group_disjoint
  (e: env)
  (fuel: nat)
  (close: bool)
  (t1: array_group)
  (t2: array_group)
: Pure bool
  (requires (
    array_group_bounded e.e_semenv.se_bound t1 /\
    array_group_bounded e.e_semenv.se_bound t2
  ))
  (ensures (fun b ->
    array_group_bounded e.e_semenv.se_bound t1 /\
    array_group_bounded e.e_semenv.se_bound t2 /\
    (b == true ==> Spec.array_group3_disjoint
      (spec_maybe_close_array_group (array_group_sem e.e_semenv t1) close)
      (spec_maybe_close_array_group (array_group_sem e.e_semenv t2) close)
  )))
  (decreases fuel)
= if fuel = 0
  then false
  else let fuel' : nat = fuel - 1 in
  match t1, t2 with
  | (_, TAAtom (TADef i1)) :: q1, _ ->
    let s1 = e.e_semenv.se_env i1 in
    if SEArrayGroup? s1
    then
      let t1' = e.e_array_group i1 in
      array_group_disjoint e fuel' close (t1' `List.Tot.append` q1) t2
    else true
  | _, (_, TAAtom (TADef _)) :: _ ->
    array_group_disjoint e fuel' close t2 t1
  | (name, TAZeroOrMore t1') :: q, _ ->
    if not (array_group_disjoint e fuel' close q t2)
    then false
    else if array_group_disjoint e fuel' false [name, TAAtom t1'] t2 // loop-free shortcut, but will miss things like "disjoint? (a*) (ab)"
    then true
    else array_group_disjoint e fuel' close ((name, TAAtom t1') :: (name, TAZeroOrMore t1') :: q) t2 // general rule, possible source of loops
  | _, (_, TAZeroOrMore _) :: _ ->
    array_group_disjoint e fuel' close t2 t1
  | [], [] -> false
  | _, [] -> close
  | [], _ ->
    array_group_disjoint e fuel' close t2 t1
  | (_, TAAtom (TAElem t1')) :: q1, (_, TAAtom (TAElem t2')) :: q2 ->
    if typ_disjoint e fuel' (TElem t1') (TElem t2')
    then true
    else if typ_equiv e fuel' (TElem t1') (TElem t2')
    then array_group_disjoint e fuel' close q1 q2
    else false
//  | _ -> false
