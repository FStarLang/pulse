module CDDL.Interpreter
open Pulse.Lib.Pervasives

open CDDL.Pulse
module Spec = CDDL.Spec
module U64 = FStar.UInt64

type elem_typ =
| TDef: (i: string) -> elem_typ
| TFalse
| TTrue
| TBool
| TNil
| TUndefined
| TByteString
| TTextString
| TUIntLiteral: (v: U64.t) -> elem_typ
| TArray: (i: string) -> elem_typ
| TMap: (i: string) -> elem_typ

noeq
type typ =
| TElem: (t: elem_typ) -> typ
| TChoice: (l: list elem_typ) -> typ
| TTag: (tag: U64.t) -> (i: elem_typ) -> typ
| TEscapeHatch: (t: Spec.typ) -> typ

let typ_eq
  (t1 t2: typ)
: Pure bool
  (requires True)
  (ensures fun b ->
    b == true ==> t1 == t2
  )
= match t1, t2 with
  | TElem t1, TElem t2 -> t1 = t2
  | TChoice l1, TChoice l2 -> l1 = l2
  | TTag tag1 i1, TTag tag2 i2 -> tag1 = tag2 && i1 = i2
  | TEscapeHatch _, TEscapeHatch _ -> false
  | _ -> false

type atom_array_group =
| TADef: (i: string) -> atom_array_group
| TAElem: (t: elem_typ) -> atom_array_group

type elem_array_group =
| TAAtom: (t: atom_array_group) -> elem_array_group
| TAZeroOrMore: (t: atom_array_group) -> elem_array_group
| TAZeroOrOne: (t: atom_array_group) -> elem_array_group

type array_group = list (string & elem_array_group)

type name_env = FStar.GSet.set string

let name (e: name_env) : eqtype = (s: string { FStar.GSet.mem s e })

noeq
type semenv_elem =
| SEType of Spec.typ
| SEArrayGroup of Spec.array_group3 None
| SEMapGroup of Spec.map_group None

noeq
type semenv = {
  se_bound: name_env;
  se_env: (name se_bound -> semenv_elem);
}

[@@"opaque_to_smt"] irreducible
let name_empty_elim (t: Type) (x: name FStar.GSet.empty) : Tot t = false_elim ()

let empty_semenv = {
  se_bound = FStar.GSet.empty;
  se_env = name_empty_elim _;
}

let se_typ
  (se: semenv)
  (i: name se.se_bound)
: Tot Spec.typ
= match se.se_env i with
  | SEType t -> t
  | _ -> Spec.t_always_false

let se_array_group
  (se: semenv)
  (i: name se.se_bound)
: Tot (Spec.array_group3 None)
= match se.se_env i with
  | SEArrayGroup t -> t
  | _ -> Spec.array_group3_always_false

let se_map_group
  (se: semenv)
  (i: name se.se_bound)
: Tot (Spec.map_group None)
= match se.se_env i with
  | SEMapGroup t -> t
  | _ -> Spec.map_group_empty

let semenv_included (s1 s2: semenv) : Tot prop =
  s1.se_bound `FStar.GSet.subset` s2.se_bound /\
  (forall (i: name s1.se_bound) . s1.se_env i == s2.se_env i)

[@@"opaque_to_smt"]
let semenv_extend_gen
  (se: semenv)
  (new_name: string)
  (a: semenv_elem)
: Pure semenv
    (requires
      (~ (FStar.GSet.mem new_name se.se_bound))
    )
    (ensures fun se' ->
      se'.se_bound == se.se_bound `FStar.GSet.union` FStar.GSet.singleton new_name /\
      semenv_included se se' /\
      se'.se_env new_name == a
    )
= let se_bound' = se.se_bound `FStar.GSet.union` FStar.GSet.singleton new_name in
  {
    se_bound = se_bound';
    se_env = (fun (i: name se_bound') -> if i = new_name then a else se.se_env i);
  }

let semenv_extend_typ
  (se: semenv)
  (new_name: string)
  (a: Spec.typ)
: Pure semenv
    (requires
      (~ (FStar.GSet.mem new_name se.se_bound))
    )
    (ensures fun se' ->
      se'.se_bound == se.se_bound `FStar.GSet.union` FStar.GSet.singleton new_name /\
      semenv_included se se' /\
      se'.se_env new_name == SEType a
    )
= semenv_extend_gen se new_name (SEType a)

let semenv_extend_array_group
  (se: semenv)
  (new_name: string)
  (a: Spec.array_group3 None)
: Pure semenv
    (requires
      (~ (FStar.GSet.mem new_name se.se_bound))
    )
    (ensures fun se' ->
      se'.se_bound == se.se_bound `FStar.GSet.union` FStar.GSet.singleton new_name /\
      semenv_included se se' /\
      se'.se_env new_name == SEArrayGroup a
    )
= semenv_extend_gen se new_name (SEArrayGroup a)

let semenv_extend_map_group
  (se: semenv)
  (new_name: string)
  (a: Spec.map_group None)
: Pure semenv
    (requires
      (~ (FStar.GSet.mem new_name se.se_bound))
    )
    (ensures fun se' ->
      se'.se_bound == se.se_bound `FStar.GSet.union` FStar.GSet.singleton new_name /\
      semenv_included se se' /\
      se'.se_env new_name == SEMapGroup a
    )
= semenv_extend_gen se new_name (SEMapGroup a)

irreducible let bounded_attr : unit = ()

[@@ bounded_attr ]
let elem_typ_bounded
  (bound: name_env)
  (t: elem_typ)
: GTot bool
= match t with
  | TDef i -> i `FStar.GSet.mem` bound
  | TArray j -> j `FStar.GSet.mem` bound
  | TMap j -> j `FStar.GSet.mem` bound
  | _ -> true

irreducible let sem_attr : unit = ()

[@@ sem_attr ]
let elem_typ_sem
  (env: semenv)
  (t: elem_typ)
: Pure Spec.typ
  (requires elem_typ_bounded env.se_bound t)
  (ensures fun _ -> True)
= match t with
  | TDef i -> se_typ env i
  | TArray i -> Spec.t_array3 (se_array_group env i)
  | TMap i -> Spec.t_map (se_map_group env i)
  | TFalse -> Spec.t_false
  | TTrue -> Spec.t_true
  | TBool -> Spec.t_bool
  | TNil -> Spec.t_nil
  | TUndefined -> Spec.t_undefined
  | TByteString -> Spec.bstr
  | TTextString -> Spec.tstr
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

[@@ bounded_attr ]
let rec sem_typ_choice_bounded
  (bound: name_env)
  (l: list elem_typ)
: GTot bool
= match l with
  | [] -> true
  | e :: q -> elem_typ_bounded bound e && sem_typ_choice_bounded bound q

[@@ sem_attr ]
let rec sem_typ_choice
  (env: semenv)
  (l: list elem_typ)
: Pure Spec.typ
    (requires sem_typ_choice_bounded env.se_bound l)
    (ensures fun _ -> True)
    (decreases l)
= match l with
  | [] -> Spec.t_always_false
  | [t] -> elem_typ_sem env t
  | a :: q -> elem_typ_sem env a `Spec.t_choice` sem_typ_choice env q

let rec sem_typ_choice_bounded_incr
  (bound1 bound2: name_env)
  (l: list elem_typ)
: Lemma
  (requires
    bound1 `FStar.GSet.subset` bound2 /\
    sem_typ_choice_bounded bound1 l
  )
  (ensures sem_typ_choice_bounded bound2 l)
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> sem_typ_choice_bounded_incr bound1 bound2 q

let rec sem_typ_choice_included (s1 s2: semenv) (t: list elem_typ) : Lemma
  (requires 
    semenv_included s1 s2 /\
    sem_typ_choice_bounded s1.se_bound t
  )
  (ensures
    sem_typ_choice_bounded s1.se_bound t /\
    sem_typ_choice_bounded s2.se_bound t /\
    sem_typ_choice s2 t == sem_typ_choice s1 t
  )
  (decreases t)
= match t with
  | [] -> ()
  | [_] -> ()
  | _ :: q -> sem_typ_choice_included s1 s2 q

[@@ bounded_attr ]
let typ_bounded
  (bound: name_env)
  (t: typ)
: GTot bool
= match t with
  | TElem t -> elem_typ_bounded bound t
  | TChoice l -> sem_typ_choice_bounded bound l
  | TTag _tag t -> elem_typ_bounded bound t
  | TEscapeHatch _ -> true

let typ_bounded_incr
  (bound1 bound2: name_env)
  (t: typ)
: Lemma
  (requires
    bound1 `FStar.GSet.subset` bound2 /\
    typ_bounded bound1 t
  )
  (ensures typ_bounded bound2 t)
= match t with
  | TChoice l -> sem_typ_choice_bounded_incr bound1 bound2 l
  | _ -> ()

[@@ sem_attr ]
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
  | TEscapeHatch t -> t

let typ_sem_included (s1 s2: semenv) (t: typ) : Lemma
  (requires 
    semenv_included s1 s2 /\
    typ_bounded s1.se_bound t
  )
  (ensures
    typ_bounded s1.se_bound t /\
    typ_bounded s2.se_bound t /\
    typ_sem s2 t == typ_sem s1 t
  )
= match t with
  | TChoice l -> sem_typ_choice_included s1 s2 l
  | _ -> ()

[@@ bounded_attr ]
let atom_array_group_bounded
  (bound: name_env)
  (t: atom_array_group)
: GTot bool
= match t with
  | TADef i -> i `FStar.GSet.mem` bound
  | TAElem t -> elem_typ_bounded bound t

let atom_array_group_bounded_incr
  (bound1 bound2: name_env)
  (t: atom_array_group)
: Lemma
  (requires
    bound1 `FStar.GSet.subset` bound2 /\
    atom_array_group_bounded bound1 t
  )
  (ensures atom_array_group_bounded bound2 t)
= ()

[@@ bounded_attr ]
let elem_array_group_bounded
  (bound: name_env)
  (t: elem_array_group)
: GTot bool
= match t with
  | TAAtom t -> atom_array_group_bounded bound t
  | TAZeroOrMore t -> atom_array_group_bounded bound t
  | TAZeroOrOne t -> atom_array_group_bounded bound t

#push-options "--ifuel 4"

let elem_array_group_bounded_incr
  (bound1 bound2: name_env)
  (t: elem_array_group)
: Lemma
  (requires
    bound1 `FStar.GSet.subset` bound2 /\
    elem_array_group_bounded bound1 t
  )
  (ensures elem_array_group_bounded bound2 t)
= ()

[@@ bounded_attr ]
let rec array_group_bounded
  (bound: name_env)
  (t: array_group)
: GTot bool
= match t with
  | [] -> true
  | (_, a) :: q -> elem_array_group_bounded bound a && array_group_bounded bound q

let rec array_group_bounded_incr
  (bound1 bound2: name_env)
  (t: array_group)
: Lemma
  (requires
    bound1 `FStar.GSet.subset` bound2 /\
    array_group_bounded bound1 t
  )
  (ensures array_group_bounded bound2 t)
  (decreases t)
= match t with
  | [] -> ()
  | (_, a) :: q ->
    assert (elem_array_group_bounded bound2 a);
    array_group_bounded_incr bound1 bound2 q

#pop-options

let rec array_group_bounded_append
  (bound: name_env)
  (t1 t2: array_group)
: Lemma
  (ensures
    array_group_bounded bound (t1 `List.Tot.append` t2) <==>
    (array_group_bounded bound t1 /\
       array_group_bounded bound t2
    )
  )
  (decreases t1)
  [SMTPat (array_group_bounded bound (t1 `List.Tot.append` t2))]
= match t1 with
  | [] -> ()
  | _ :: q -> array_group_bounded_append bound q t2

[@@ sem_attr ]
let atom_array_group_sem
  (env: semenv)
  (t: atom_array_group)
: Pure (Spec.array_group3 None)
    (requires atom_array_group_bounded env.se_bound t)
    (ensures fun _ -> True)
= match t with
  | TADef i -> se_array_group env i
  | TAElem j -> Spec.array_group3_item (elem_typ_sem env j)

[@@ sem_attr ]
let elem_array_group_sem
  (env: semenv)
  (t: elem_array_group)
: Pure (Spec.array_group3 None)
    (requires elem_array_group_bounded env.se_bound t)
    (ensures fun _ -> True)
= match t with
  | TAAtom i -> atom_array_group_sem env i
  | TAZeroOrMore i -> Spec.array_group3_zero_or_more (atom_array_group_sem env i)
  | TAZeroOrOne i -> Spec.array_group3_zero_or_one (atom_array_group_sem env i)

#push-options "--ifuel 4"

let elem_array_group_sem_included (s1 s2: semenv) (t: elem_array_group) : Lemma
  (requires 
    semenv_included s1 s2 /\
    elem_array_group_bounded s1.se_bound t
  )
  (ensures
    elem_array_group_bounded s1.se_bound t /\
    elem_array_group_bounded s2.se_bound t /\
    elem_array_group_sem s2 t == elem_array_group_sem s1 t
  )
= ()

#pop-options

[@@ sem_attr ]
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

let rec array_group_sem_included (s1 s2: semenv) (t: array_group) : Lemma
  (requires 
    semenv_included s1 s2 /\
    array_group_bounded s1.se_bound t
  )
  (ensures
    array_group_bounded s1.se_bound t /\
    array_group_bounded s2.se_bound t /\
    array_group_sem s2 t == array_group_sem s1 t
  )
= match t with
  | [] -> ()
  | [_, a] -> elem_array_group_sem_included s1 s2 a
  | (_, a) :: q ->
    elem_array_group_sem_included s1 s2 a;
    array_group_sem_included s1 s2 q

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

let map_group = Spec.map_group None // TODO: add syntax support
[@@ bounded_attr ]
let map_group_bounded (_: name_env) (x: map_group) : Tot bool = true // TODO
[@@ sem_attr ]
let map_group_sem (_: semenv) (x: map_group) : Pure (Spec.map_group None)
  (requires True)
  (ensures (fun _ -> True))
= x // TODO

let env_elem0 (s: semenv_elem) : Type0 =
  match s with
  | SEType _ -> typ
  | SEArrayGroup _ -> array_group
  | SEMapGroup _ -> map_group

let env_elem_prop (e_semenv: semenv) (s: semenv_elem) (x: env_elem0 s) : Tot prop =
  match s with
  | SEType phi ->
    typ_bounded e_semenv.se_bound x /\
    Spec.typ_equiv (typ_sem e_semenv x) phi
  | SEArrayGroup phi ->
    array_group_bounded e_semenv.se_bound x /\
    Spec.array_group3_equiv (array_group_sem e_semenv x) phi
  | SEMapGroup phi ->
    map_group_bounded e_semenv.se_bound x /\
    Spec.map_group_equiv (map_group_sem e_semenv x) phi

let env_elem_prop_included (e1 e2: semenv) (s: semenv_elem) (x: env_elem0 s) : Lemma
  (requires semenv_included e1 e2 /\
    env_elem_prop e1 s x
  )
  (ensures env_elem_prop e2 s x)
= match s with
  | SEType _ -> typ_sem_included e1 e2 x
  | SEArrayGroup _ -> array_group_sem_included e1 e2 x
  | SEMapGroup _ -> () // TODO

let env_elem (e_semenv: semenv) (s: semenv_elem) =
  (x: env_elem0 s { env_elem_prop e_semenv s x })

noeq
type env = {
  e_semenv: semenv;
  e_env: (i: name e_semenv.se_bound) -> (env_elem e_semenv (e_semenv.se_env i));
}

[@@"opaque_to_smt"] irreducible // because of false_elim
let e_env_empty (i: name FStar.GSet.empty) : Tot (env_elem empty_semenv (empty_semenv.se_env i)) = false_elim ()

[@@"opaque_to_smt"]
let empty_env : (e: env {
  e.e_semenv.se_bound == FStar.GSet.empty
}) = {
  e_semenv = empty_semenv;
  e_env = e_env_empty;
}

let env_included
  (e1 e2: env)
: Tot prop
= semenv_included e1.e_semenv e2.e_semenv /\
  (forall (i: name e1.e_semenv.se_bound) . e2.e_env i == e1.e_env i)

[@@"opaque_to_smt"]
let env_extend_gen
  (e: env)
  (new_name: string)
  (s: semenv_elem)
  (x: env_elem e.e_semenv s)
: Pure env
    (requires
      (~ (new_name `FStar.GSet.mem` e.e_semenv.se_bound))
    )
    (ensures fun e' ->
      e'.e_semenv.se_bound == e.e_semenv.se_bound `FStar.GSet.union` FStar.GSet.singleton new_name /\
      env_included e e' /\
      e'.e_semenv.se_env new_name == s /\
      e'.e_env new_name == x
    )
= let se' = semenv_extend_gen e.e_semenv new_name s in
  {
    e_semenv = se';
    e_env = (fun (i: name se'.se_bound) ->
      let x' : env_elem e.e_semenv (se'.se_env i) =
        if i = new_name
        then x
        else e.e_env i
      in
      env_elem_prop_included e.e_semenv se' (se'.se_env i) x';
      x'
    );
  }

let env_extend_typ
  (e: env)
  (new_name: string {(~ (new_name `FStar.GSet.mem` e.e_semenv.se_bound))}) // ideally by SMT
  (a: typ)
  (sq: squash (
    typ_bounded e.e_semenv.se_bound a // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  ))
: Tot (e': env {
      e'.e_semenv.se_bound == e.e_semenv.se_bound `FStar.GSet.union` FStar.GSet.singleton new_name /\
      env_included e e' /\
      e'.e_semenv.se_env new_name == SEType (typ_sem e.e_semenv a)   /\
      e'.e_env new_name == a
  })
= env_extend_gen e new_name (SEType (typ_sem e.e_semenv a)) a

let env_extend_array_group
  (e: env)
  (new_name: string {(~ (new_name `FStar.GSet.mem` e.e_semenv.se_bound))}) // ideally by SMT
  (a: array_group)
  (sq: squash (
    array_group_bounded e.e_semenv.se_bound a // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  ))
: Tot (e': env {
      e'.e_semenv.se_bound == e.e_semenv.se_bound `FStar.GSet.union` FStar.GSet.singleton new_name /\
      env_included e e' /\
      e'.e_semenv.se_env new_name == SEArrayGroup (array_group_sem e.e_semenv a) /\
      e'.e_env new_name == a
  })
= env_extend_gen e new_name (SEArrayGroup (array_group_sem e.e_semenv a)) a

let env_extend_map_group
  (e: env)
  (new_name: string {(~ (new_name `FStar.GSet.mem` e.e_semenv.se_bound))}) // ideally by SMT
  (a: map_group)
  (sq: squash (
    map_group_bounded e.e_semenv.se_bound a // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  ))
: Tot (e': env {
      e'.e_semenv.se_bound == e.e_semenv.se_bound `FStar.GSet.union` FStar.GSet.singleton new_name /\
      env_included e e' /\
      e'.e_semenv.se_env new_name == SEMapGroup (map_group_sem e.e_semenv a) /\
      e'.e_env new_name == a
  })
= env_extend_gen e new_name (SEMapGroup (map_group_sem e.e_semenv a)) a

let spec_array_group3_zero_or_more_equiv #b
 (a1 a2: Spec.array_group3 b)
: Lemma
  (requires Spec.array_group3_equiv a1 a2)
  (ensures Spec.array_group3_equiv (Spec.array_group3_zero_or_more a1) (Spec.array_group3_zero_or_more a2))
  [SMTPat (Spec.array_group3_equiv (Spec.array_group3_zero_or_more a1) (Spec.array_group3_zero_or_more a2))]
= assert (Spec.array_group3_equiv a1 a2);
  let rec phi
    (l: list CBOR.Spec.raw_data_item { Spec.opt_precedes_list l b })
  : Lemma
    (ensures (Spec.array_group3_zero_or_more a1 l == Spec.array_group3_zero_or_more a2 l))
    (decreases (List.Tot.length l))
  = assert (a1 l == a2 l);
    match a1 l with
    | None -> ()
    | Some (l1, l2) ->
      List.Tot.append_length l1 l2;
      if Nil? l1
      then ()
      else phi l2
  in
  Classical.forall_intro phi

// This is nothing more than delta-equivalence

#push-options "--z3rlimit 16"

[@@"opaque_to_smt"]
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
= if t1 `typ_eq` t2
  then true
  else if fuel = 0
  then false
  else let fuel' : nat = fuel - 1 in
  match t1, t2 with
  | TElem (TDef i), _ ->
    let s1 = e.e_semenv.se_env i in
    if SEType? s1
    then
      let t1' = e.e_env i in
      typ_equiv e fuel' t1' t2
    else false
  | _, TElem (TDef _) ->
    typ_equiv e fuel' t2 t1
  | TEscapeHatch _, _
  | _, TEscapeHatch _ -> false
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
      let t1' = e.e_env i1 in
      let t2' = e.e_env i2 in
      array_group_equiv e fuel' t1' t2'
    else false
  | TElem (TMap i1), TElem (TMap i2) -> i1 = i2 // TODO
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
      let t1' = e.e_env i1 in
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
  | (s1, TAZeroOrOne t1) :: q1, (s2, TAZeroOrOne t2) :: q2 ->
    if array_group_equiv e fuel' [s1, TAAtom t1] [s2, TAAtom t2]
    then begin
       assert (Spec.array_group3_equiv (atom_array_group_sem e.e_semenv t1) (atom_array_group_sem e.e_semenv t2));
       assert (Spec.array_group3_equiv (Spec.array_group3_zero_or_one (atom_array_group_sem e.e_semenv t1)) (Spec.array_group3_zero_or_one (atom_array_group_sem e.e_semenv t2)));
       array_group_equiv e fuel' q1 q2
    end
    else false
  | _ -> false

#pop-options

let spec_typ_disjoint (a1 a2: Spec.typ) : Tot prop
= (forall (l: CBOR.Spec.raw_data_item) . ~ (a1 l /\ a2 l))

noeq
type result =
| ResultSuccess
| ResultFailure of string
| ResultOutOfFuel

#push-options "--z3rlimit 32"

#restart-solver
[@@"opaque_to_smt"]
let rec typ_disjoint
  (e: env)
  (fuel: nat)
  (t1: typ)
  (t2: typ)
: Pure result
  (requires (
    typ_bounded e.e_semenv.se_bound t1 /\
    typ_bounded e.e_semenv.se_bound t2
  ))
  (ensures (fun b ->
    typ_bounded e.e_semenv.se_bound t1 /\
    typ_bounded e.e_semenv.se_bound t2 /\
    (b == ResultSuccess ==> spec_typ_disjoint (typ_sem e.e_semenv t1) (typ_sem e.e_semenv t2))
  ))
  (decreases fuel)
= if fuel = 0
  then ResultOutOfFuel
  else let fuel' : nat = fuel - 1 in
  match t1, t2 with
  | TElem (TDef i), _ ->
    let s1 = e.e_semenv.se_env i in
    if SEType? s1
    then
      let t1' = e.e_env i in
      typ_disjoint e fuel' t1' t2
    else ResultSuccess
  | _, TElem (TDef _) ->
    typ_disjoint e fuel' t2 t1
  | TChoice [], _ -> ResultSuccess
  | TChoice (t1' :: q1'), _ ->
    let td1 = typ_disjoint e fuel' (TElem t1') t2 in
    if not (ResultSuccess? td1)
    then td1
    else typ_disjoint e fuel' (TChoice q1') t2
  | _, TChoice _ ->
    typ_disjoint e fuel' t2 t1
  | TEscapeHatch _, _
  | _, TEscapeHatch _ -> ResultFailure "typ_disjoint: TEscapeHatch"
  | TTag tag1 t1, TTag tag2 t2 ->
    if tag1 <> tag2
    then ResultSuccess
    else typ_disjoint e fuel' (TElem t1) (TElem t2)
  | _, TTag _ _
  | TTag _ _, _ -> ResultSuccess
  | TElem (TArray i1), TElem (TArray i2) ->
    let s1 = e.e_semenv.se_env i1 in
    let s2 = e.e_semenv.se_env i2 in
    if SEArrayGroup? s1 && SEArrayGroup? s2
    then begin
      let t1' = e.e_env i1 in
      let t2' = e.e_env i2 in
      spec_array3_close_array_group (SEArrayGroup?._0 s1);
      spec_array3_close_array_group (SEArrayGroup?._0 s2);
      array_group_disjoint e fuel' true t1' t2'
    end
    else ResultSuccess
  | TElem TBool, TElem TFalse -> ResultFailure "typ_disjoint: TBool, TFalse"
  | TElem TBool, TElem TTrue -> ResultFailure "typ_disjoint: TBool, TTrue"
  | _, TElem TBool ->
    typ_disjoint e fuel' t2 t1
  | TElem (TMap _), TElem (TMap _) -> ResultFailure "typ_disjoint: TMap, TMap" // TODO
  | TElem e1, TElem e2 ->
    if e1 <> e2
    then ResultSuccess
    else ResultFailure "typ_disjoint: TElem equal"

and array_group_disjoint
  (e: env)
  (fuel: nat)
  (close: bool)
  (t1: array_group)
  (t2: array_group)
: Pure result
  (requires (
    array_group_bounded e.e_semenv.se_bound t1 /\
    array_group_bounded e.e_semenv.se_bound t2
  ))
  (ensures (fun b ->
    array_group_bounded e.e_semenv.se_bound t1 /\
    array_group_bounded e.e_semenv.se_bound t2 /\
    (b == ResultSuccess ==> Spec.array_group3_disjoint
      (spec_maybe_close_array_group (array_group_sem e.e_semenv t1) close)
      (spec_maybe_close_array_group (array_group_sem e.e_semenv t2) close)
  )))
  (decreases fuel)
= if fuel = 0
  then ResultOutOfFuel
  else let fuel' : nat = fuel - 1 in
  match t1, t2 with
  | (_, TAAtom (TADef i1)) :: q1, _ ->
    let s1 = e.e_semenv.se_env i1 in
    if SEArrayGroup? s1
    then
      let t1' = e.e_env i1 in
      array_group_disjoint e fuel' close (t1' `List.Tot.append` q1) t2
    else ResultSuccess
  | _, (_, TAAtom (TADef _)) :: _ ->
    array_group_disjoint e fuel' close t2 t1
  | (name, TAZeroOrMore t1') :: q, _ ->
    let res1 = array_group_disjoint e fuel' close q t2 in
    if not (ResultSuccess? res1)
    then res1
    else if ResultSuccess? (array_group_disjoint e fuel' false [name, TAAtom t1'] t2) // loop-free shortcut, but will miss things like "disjoint? (a*) (ab)"
    then ResultSuccess
    else array_group_disjoint e fuel' close ((name, TAAtom t1') :: (name, TAZeroOrMore t1') :: q) t2 // general rule, possible source of loops
  | _, (_, TAZeroOrMore _) :: _ ->
    array_group_disjoint e fuel' close t2 t1
  | (name, TAZeroOrOne t1') :: q, _ ->
    let res1 = array_group_disjoint e fuel' close q t2 in
    if not (ResultSuccess? res1)
    then res1
    else array_group_disjoint e fuel' close ((name, TAAtom t1') :: q) t2
  | _, (_, TAZeroOrOne _) :: _ ->
    array_group_disjoint e fuel' close t2 t1
  | [], [] -> ResultFailure "array_group_disjoint: [], []"
  | _, [] -> if close then ResultSuccess else ResultFailure "array_group_disjoint: cons, nil, not close"
  | [], _ ->
    array_group_disjoint e fuel' close t2 t1
  | (_, TAAtom (TAElem t1')) :: q1, (_, TAAtom (TAElem t2')) :: q2 ->
    if ResultSuccess? (typ_disjoint e fuel' (TElem t1') (TElem t2'))
    then ResultSuccess
    else if typ_equiv e fuel' (TElem t1') (TElem t2')
    then array_group_disjoint e fuel' close q1 q2
    else ResultFailure "array_group_disjoint: TAElem"
//  | _ -> false

#pop-options

let rec spec_array_group_splittable
  (e: semenv)
  (a: array_group)
: Tot prop
= array_group_bounded e.se_bound a /\
  begin match a with
  | [] -> True
  | [_] -> True
  | (_, t) :: q ->
    Spec.array_group3_concat_unique_weak
      (elem_array_group_sem e t)
      (array_group_sem e q) /\
    spec_array_group_splittable e q
  end

let rec spec_array_group_splittable_included
  (e1 e2: semenv)
  (a: array_group)
: Lemma
  (requires
     semenv_included e1 e2 /\
     array_group_bounded e1.se_bound a
  )
  (ensures
    spec_array_group_splittable e1 a <==> spec_array_group_splittable e2 a
  )
= match a with
  | [] -> ()
  | [_, t] -> elem_array_group_sem_included e1 e2 t
  | (_, t) :: q ->
    elem_array_group_sem_included e1 e2 t;
    array_group_sem_included e1 e2 q;
    spec_array_group_splittable_included e1 e2 q

let spec_array_group3_concat_unique_weak_intro
  #b (a1 a3: Spec.array_group3 b)
  (prf1:
    (l: (l: list CBOR.Spec.raw_data_item { Spec.opt_precedes_list l b })) ->
    Lemma
    (requires Spec.array_group3_concat a1 a3 l == Some (l, []))
    (ensures
      (exists (l1 l2: list CBOR.Spec.raw_data_item) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, [])
    ))
//    [SMTPat (Spec.array_group3_concat a1 a3 l)]
  )
  (prf2:
    (l1: (l: list CBOR.Spec.raw_data_item { Spec.opt_precedes_list l b })) ->
    (l2: (l: list CBOR.Spec.raw_data_item { Spec.opt_precedes_list l b })) ->
    Lemma
    (requires
        a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, [])
    )
    (ensures       
      a1 (l1 `List.Tot.append` l2) == Some (l1, l2)
    )
//    [SMTPat (a1 (l1 `List.Tot.append` l2))]
  )
: Lemma
  (Spec.array_group3_concat_unique_weak a1 a3)
= let prf1'
    (l: (l: list CBOR.Spec.raw_data_item { Spec.opt_precedes_list l b }))
  : Lemma
    (Spec.array_group3_concat a1 a3 l == Some (l, []) ==>
      (exists (l1 l2: list CBOR.Spec.raw_data_item) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, [])
    ))
  = Classical.move_requires prf1 l
  in
  Classical.forall_intro prf1';
  let prf2'
    (l1: (l: list CBOR.Spec.raw_data_item { Spec.opt_precedes_list l b }))
    (l2: (l: list CBOR.Spec.raw_data_item { Spec.opt_precedes_list l b }))
  : Lemma
    ((
        a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, [])
    ) ==>
    (
      a1 (l1 `List.Tot.append` l2) == Some (l1, l2)
    ))
  = Classical.move_requires (prf2 l1) l2
  in
  Classical.forall_intro_2 prf2'

#push-options "--z3rlimit 16"

#restart-solver
let rec spec_array_group_splittable_fold
  (e: semenv)
  (g1 g2: array_group)
: Lemma
  (requires
    spec_array_group_splittable e g1 /\
    spec_array_group_splittable e (g1 `List.Tot.append` g2)
  )
  (ensures
    spec_array_group_splittable e g2 /\
    Spec.array_group3_concat_unique_weak
      (array_group_sem e g1)
      (array_group_sem e g2)
  )
  (decreases g1)
= match g1 with
  | [] -> ()
  | [_] -> ()
  | (n1, t1) :: g1' ->
    spec_array_group_splittable_fold e g1' g2;
    let a1 = array_group_sem e g1 in
    let a3 = array_group_sem e g2 in
    spec_array_group3_concat_unique_weak_intro a1 a3
      (fun l -> ())
      (fun l1 l2 ->
        let Some (l1l, l1r) = elem_array_group_sem e t1 l1 in
        List.Tot.append_assoc l1l l1r l2
      );
    assert (Spec.array_group3_concat_unique_weak a1 a3)

// the converse does not hold: consider a* b* a*, then [a] has two decompositions: [a] [] [] and [] [] [a]

#restart-solver
let rec spec_array_group_splittable_fold_gen
  (e: semenv)
  (g1 g2 g3: array_group)
  (n2: string)
  (g2': elem_array_group)
: Lemma
  (requires
    spec_array_group_splittable e g2 /\
    spec_array_group_splittable e (g1 `List.Tot.append` (g2 `List.Tot.append` g3)) /\
    elem_array_group_bounded e.se_bound g2' /\
    elem_array_group_sem e g2' `Spec.array_group3_equiv` array_group_sem e g2
  )
  (ensures
    spec_array_group_splittable e g3 /\
    spec_array_group_splittable e (g1 `List.Tot.append` ((n2, g2') :: g3))
  )
  (decreases g1)
= match g1 with
  | [] -> spec_array_group_splittable_fold e g2 g3
  | _ :: g1' ->
    spec_array_group_splittable_fold_gen e g1' g2 g3 n2 g2';
    assert (
      array_group_sem e ((n2, g2') :: g3) `Spec.array_group3_equiv`
      array_group_sem e (g2 `List.Tot.append` g3)
    );
//    array_group_bounded_append e.se_bound g1' (g2 `List.Tot.append` g3);
    array_group_sem_append e g1' ((n2, g2') :: g3);
    array_group_sem_append e g1' (g2 `List.Tot.append` g3);
    assert (Spec.array_group3_equiv
      (array_group_sem e (g1' `List.Tot.append` ((n2, g2') :: g3)))
      (array_group_sem e (g1' `List.Tot.append` (g2 `List.Tot.append` g3)))
    )

let spec_array_group3_concat_unique_strong'_concat_left
  (#b: _)
  (g1 g2 g3: Spec.array_group3 b)
: Lemma
  (requires
    Spec.array_group3_concat_unique_strong' g1 (Spec.array_group3_concat g2 g3) /\
    Spec.array_group3_concat_unique_strong' g2 g3 /\
    Spec.array_group3_concat_unique_weak g1 g2
  )
  (ensures
    Spec.array_group3_concat_unique_strong' (Spec.array_group3_concat g1 g2) g3
  )
= let a1 = Spec.array_group3_concat g1 g2 in
  let a3 = g3 in
  let prf
    (l1 l2:
      (l: list CBOR.Spec.raw_data_item { Spec.opt_precedes_list l b })
    )
  : Lemma
    (Some? (a3 l2) ==> (a1 (l1 `List.Tot.append` l2) == Some (l1, l2) <==> a1 l1 == Some (l1, [])))
  = if Some? (a3 l2)
    then begin
      if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 (l1 `List.Tot.append` l2) == Some (l1, l2))
      then assert (a1 l1 == Some (l1, []))
      else if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 l1 == Some (l1, []))
      then begin
        let Some (lg1, lg2) = g1 l1 in
        assert (g1 lg1 == Some (lg1, []));
        assert (g2 lg2 == Some (lg2, []));
        List.Tot.append_assoc lg1 lg2 l2
      end
    end
  in
  Classical.forall_intro_2 prf

let spec_array_group3_concat_unique_strong_concat_left
  (#b: _)
  (g1 g2 g3: Spec.array_group3 b)
: Lemma
  (requires
    Spec.array_group3_concat_unique_strong g1 (Spec.array_group3_concat g2 g3) /\
    Spec.array_group3_concat_unique_strong g2 g3 /\
    Spec.array_group3_concat_unique_weak g1 g2
  )
  (ensures
    Spec.array_group3_concat_unique_strong (Spec.array_group3_concat g1 g2) g3
  )
= spec_array_group3_concat_unique_strong'_concat_left g1 g2 g3

#restart-solver
let spec_array_group3_concat_unique_strong_zero_or_one_left
  #b (a1 a2: Spec.array_group3 b)
: Lemma
  (requires (
    Spec.array_group3_disjoint a1 a2 /\
    Spec.array_group3_concat_unique_strong a1 a2
  ))
  (ensures (
    Spec.array_group3_concat_unique_strong (Spec.array_group3_zero_or_one a1) a2
  ))
= ()

let spec_array_group_splittable_threshold
  (e: env)
: Tot Type
= (i: string) -> Pure bool
    (requires True)
    (ensures fun b ->
      b == true ==> 
      (i `FStar.GSet.mem` e.e_semenv.se_bound /\
        SEArrayGroup? (e.e_semenv.se_env i) /\
        spec_array_group_splittable e.e_semenv (e.e_env i)
    ))

#pop-options

#push-options "--z3rlimit 32 --split_queries always"

#restart-solver
[@@"opaque_to_smt"]
let rec array_group_concat_unique_strong
  (e: env)
  (e_thr: spec_array_group_splittable_threshold e)
  (fuel: nat)
  (a1 a2: array_group)
: Pure result
  (requires
    spec_array_group_splittable e.e_semenv a1 /\
    array_group_bounded e.e_semenv.se_bound a2
  )
  (ensures fun b ->
    b == ResultSuccess ==> Spec.array_group3_concat_unique_strong
      (array_group_sem e.e_semenv a1)
      (array_group_sem e.e_semenv a2)
  )
  (decreases fuel)
= if fuel = 0
  then ResultOutOfFuel
  else let fuel' : nat = fuel - 1 in
  match a1, a2 with
  | [], _ -> ResultSuccess
  | (n1, t1l) :: t1r :: q, _ ->
    let a1' = t1r :: q in
    let res1 = array_group_concat_unique_strong e e_thr fuel' a1' a2 in
    if not (ResultSuccess? res1)
    then res1
    else let res2 = array_group_concat_unique_strong e e_thr fuel' [n1, t1l] (a1' `List.Tot.append` a2) in
    if not (ResultSuccess? res2)
    then res2
    else begin
      spec_array_group3_concat_unique_strong_concat_left (elem_array_group_sem e.e_semenv t1l) (array_group_sem e.e_semenv a1') (array_group_sem e.e_semenv a2);
      ResultSuccess
    end
  | [_, TAAtom (TAElem _)], _ -> ResultSuccess
  | [n1, TAAtom (TADef i)], _ ->
    if SEArrayGroup? (e.e_semenv.se_env i)
    then
      if not (e_thr i)
      then ResultFailure "array_group_concat_unique_strong: unfold left, beyond threshold"
      else
        let t1 = e.e_env i in
        array_group_concat_unique_strong e e_thr fuel' t1 a2
    else ResultSuccess
  | _, (n2, TAAtom (TADef i)) :: a2' ->
    if SEArrayGroup? (e.e_semenv.se_env i)
    then
      let t1 = e.e_env i in
      array_group_concat_unique_strong e e_thr fuel' a1 (t1 `List.Tot.append` a2')
    else ResultSuccess
  | [n1, TAZeroOrMore t1], _ ->
    let res1 = array_group_disjoint e fuel false [n1, TAAtom t1] a2 in
    if not (ResultSuccess? res1)
    then res1
    else let res2 = array_group_concat_unique_strong e e_thr fuel' [n1, TAAtom t1] [n1, TAAtom t1] in
    if not (ResultSuccess? res2)
    then res2
    else let res3 = array_group_concat_unique_strong e e_thr fuel' [n1, TAAtom t1] a2 in
    if not (ResultSuccess? res3)
    then res3
    else begin
      Spec.array_group3_concat_unique_strong_zero_or_more_left
        (atom_array_group_sem e.e_semenv t1)
        (array_group_sem e.e_semenv a2);
      ResultSuccess
    end
  | [n1, TAZeroOrOne t1], _ ->
    let res1 = array_group_disjoint e fuel false [n1, TAAtom t1] a2 in
    if not (ResultSuccess? res1)
    then res1
    else let res2 = array_group_concat_unique_strong e e_thr fuel' [n1, TAAtom t1] a2 in
    if not (ResultSuccess? res2)
    then res2
    else begin
      spec_array_group3_concat_unique_strong_zero_or_one_left
        (atom_array_group_sem e.e_semenv t1)
        (array_group_sem e.e_semenv a2);
      ResultSuccess
    end
//  | _ -> false

#pop-options

#restart-solver
let spec_array_group3_concat_unique_weak_zero_or_one_left
  #b (a1 a2: Spec.array_group3 b)
: Lemma
  (requires (
    Spec.array_group3_disjoint a1 a2 /\
    Spec.array_group3_concat_unique_weak a1 a2
  ))
  (ensures (
    Spec.array_group3_concat_unique_weak (Spec.array_group3_zero_or_one a1) a2
  ))
= ()

#push-options "--z3rlimit 32 --split_queries always"

#restart-solver
[@@"opaque_to_smt"]
let rec array_group_splittable
  (e: env)
  (e_thr: spec_array_group_splittable_threshold e)
  (fuel: nat)
  (a1 a2: array_group)
: Pure result
  (requires spec_array_group_splittable e.e_semenv a2 /\
    array_group_bounded e.e_semenv.se_bound a1
  )
  (ensures fun b ->
    array_group_bounded e.e_semenv.se_bound (a1 `List.Tot.append` a2) /\
    (b == ResultSuccess ==> spec_array_group_splittable e.e_semenv (a1 `List.Tot.append` a2))
  )
  (decreases fuel)
= if fuel = 0
  then ResultOutOfFuel
  else let fuel' : nat = fuel - 1 in
  match a1, a2 with
  | [], _ -> ResultSuccess
  | t1l :: t1r :: q1, _ ->
    let a1' = t1r :: q1 in
    let res1 = array_group_splittable e e_thr fuel' a1' a2 in
    if not (ResultSuccess? res1)
    then res1
    else array_group_splittable e e_thr fuel' [t1l] (a1' `List.Tot.append` a2)
  | _, [] -> ResultSuccess
  | [_, TAAtom (TADef i)], _ ->
    if SEArrayGroup? (e.e_semenv.se_env i)
    then
      if not (e_thr i)
      then ResultFailure "array_group_splittable: unfold left, beyond threshold"
      else
        let t1 = e.e_env i in
        let res = array_group_splittable e e_thr fuel' t1 a2 in
        if not (ResultSuccess? res)
        then res
        else begin
          spec_array_group_splittable_fold e.e_semenv t1 a2;
          ResultSuccess
        end
    else ResultSuccess
  | [_, TAAtom (TAElem _)], _ -> ResultSuccess
  | _, (n2, TAAtom (TADef i)) :: a2' ->
    if SEArrayGroup? (e.e_semenv.se_env i)
    then
      if not (e_thr i)
      then ResultFailure "array_group_splittable: unfold right, beyond threshold"
      else
        let t1 = e.e_env i in
        let res1 = array_group_splittable e e_thr fuel' t1 a2' in // necessary because of the infamous a* b* a* counterexample
        if not (ResultSuccess? res1)
        then res1
        else let res2 = array_group_splittable e e_thr fuel' a1 (t1 `List.Tot.append` a2') in
        if not (ResultSuccess? res2)
        then res2
        else begin
            spec_array_group_splittable_fold_gen e.e_semenv a1 t1 a2' n2 (TAAtom (TADef i));
            ResultSuccess
        end
    else ResultSuccess
  | [n1, TAZeroOrMore t1], _ ->
    let res1 = array_group_disjoint e fuel false [n1, TAAtom t1] a2 in
    if not (ResultSuccess? res1)
    then res1
    else let res2 = array_group_concat_unique_strong e e_thr fuel [n1, TAAtom t1] [n1, TAAtom t1] in
    if not (ResultSuccess? res2)
    then res2
    else let res3 = array_group_splittable e e_thr fuel' [n1, TAAtom t1] a2 in
    if not (ResultSuccess? res3)
    then res3
    else begin
      Spec.array_group3_concat_unique_weak_zero_or_more_left
        (atom_array_group_sem e.e_semenv t1)
        (array_group_sem e.e_semenv a2);
      ResultSuccess
    end
  | [n1, TAZeroOrOne t1], _ ->
    let res1 = array_group_disjoint e fuel false [n1, TAAtom t1] a2 in
    if not (ResultSuccess? res1)
    then res1
    else let res2 = array_group_splittable e e_thr fuel' [n1, TAAtom t1] a2 in
    if not (ResultSuccess? res2)
    then res2
    else begin
      spec_array_group3_concat_unique_weak_zero_or_one_left
        (atom_array_group_sem e.e_semenv t1)
        (array_group_sem e.e_semenv a2);
      ResultSuccess
    end
//  | _ -> false

#pop-options

[@@"opaque_to_smt"]
let spec_array_group_splittable_threshold_empty
  (e: env)
: Tot (spec_array_group_splittable_threshold e)
= (fun _ -> false)

let spec_array_group_splittable_nil
  (e: semenv)
: Lemma
  (ensures (spec_array_group_splittable e []))
  [SMTPat (spec_array_group_splittable e [])]
= assert_norm (spec_array_group_splittable e []) // would need 1 fuel

let spec_array_group_splittable_fuel
  (#e: env)
  (e_thr: spec_array_group_splittable_threshold e)
  (new_name: name e.e_semenv.se_bound { SEArrayGroup? (e.e_semenv.se_env new_name) })
: Tot Type0
= (fuel: nat {
    array_group_splittable e e_thr fuel (e.e_env new_name) [] == ResultSuccess
  })

let spec_array_group_splittable_fuel_intro
  (fuel: nat)
  (e: env)
  (e_thr: spec_array_group_splittable_threshold e)
  (new_name: name e.e_semenv.se_bound { SEArrayGroup? (e.e_semenv.se_env new_name) })
  (prf: squash (array_group_splittable e e_thr fuel (e.e_env new_name) [] == ResultSuccess))
: Tot (spec_array_group_splittable_fuel e_thr new_name)
= fuel

[@@"opaque_to_smt"]
let spec_array_group_splittable_threshold_extend
  (#e: env)
  (e_thr: spec_array_group_splittable_threshold e)
  (new_name: name e.e_semenv.se_bound { SEArrayGroup? (e.e_semenv.se_env new_name) })
  (fuel: spec_array_group_splittable_fuel e_thr new_name)
: Tot (spec_array_group_splittable_threshold e)
= (fun i -> if i = new_name then true else e_thr i)

[@@"opaque_to_smt"]
let spec_array_group_splittable_threshold_extend_env
  (#e1: env)
  (e_thr: spec_array_group_splittable_threshold e1)
  (e2: env { env_included e1 e2 })
: Tot (spec_array_group_splittable_threshold e2)
= (fun i ->
     if e_thr i
     then begin
       spec_array_group_splittable_included e1.e_semenv e2.e_semenv (e1.e_env i);
       true
     end
     else false
  )

let solve_env_extend_array_group () : FStar.Tactics.Tac unit =
  FStar.Tactics.norm [delta_attr [`%bounded_attr]; iota; zeta; primops];
  FStar.Tactics.smt ()

exception ExceptionOutOfFuel

let solve_spec_array_group_splittable () : FStar.Tactics.Tac unit =
  let rec aux (n: nat) : FStar.Tactics.Tac unit =
    FStar.Tactics.try_with
    (fun _ ->
      FStar.Tactics.print ("solve_spec_array_group_splittable with fuel " ^ string_of_int n ^ "\n");
      FStar.Tactics.apply (FStar.Tactics.mk_app (`spec_array_group_splittable_fuel_intro) [quote n, FStar.Tactics.Q_Explicit]);
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.try_with
        (fun _ ->
          FStar.Tactics.trefl ()
        )
        (fun e -> 
          let g = FStar.Tactics.cur_goal () in
          FStar.Tactics.print ("solve_spec_array_group_splittable Failure: " ^ FStar.Tactics.term_to_string g ^ "\n");
          let g0 = quote (squash (ResultOutOfFuel == ResultSuccess)) in
          FStar.Tactics.print ("Comparing with " ^ FStar.Tactics.term_to_string g0 ^ "\n");
          let e' =
            if g `FStar.Tactics.term_eq` g0
            then ExceptionOutOfFuel
            else e
          in
          FStar.Tactics.raise e'
        )
      )
      (fun e ->
        match e with
        | ExceptionOutOfFuel -> aux (n + 1)
        | _ -> FStar.Tactics.raise e
      )
  in
  aux 0

let solve_sem_equiv () : FStar.Tactics.Tac unit =
  FStar.Tactics.norm [delta_attr [`%sem_attr]; iota; zeta; primops];
  FStar.Tactics.smt ()
