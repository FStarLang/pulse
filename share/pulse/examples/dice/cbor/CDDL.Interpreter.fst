module CDDL.Interpreter
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
| TElemArray: (i: elem_array_group) -> elem_typ // to avoid spurious alias-style type definitions
| TMap: (i: string) -> elem_typ

and atom_array_group =
| TADef: (i: string) -> atom_array_group
| TAElem: (t: elem_typ) -> atom_array_group

and elem_array_group =
| TAAtom: (t: atom_array_group) -> elem_array_group
| TAZeroOrMore: (t: atom_array_group) -> elem_array_group
| TAOneOrMore: (t: atom_array_group) -> elem_array_group
| TAZeroOrOne: (t: atom_array_group) -> elem_array_group

type array_group = list (string & elem_array_group)

noeq
type typ =
| TElem: (t: elem_typ) -> typ
| TChoice: (l: list elem_typ) -> typ
| TTag: (tag: U64.t) -> (i: elem_typ) -> typ
| TEscapeHatch: (t: Spec.typ) -> typ
| TArray: (a: array_group) -> typ

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

type name_env = (string -> GTot bool)

irreducible let bounded_attr : unit = ()

irreducible let sem_attr : unit = ()

[@@ bounded_attr]
let name_mem (s: string) (e: name_env) : GTot bool = e s

let name (e: name_env) : eqtype = (s: string { name_mem s e })

[@@ bounded_attr; sem_attr]
let name_intro (s: string) (e: name_env) (sq: squash (name_mem s e)) : Tot (name e) =
  s

[@@ bounded_attr; sem_attr]
noeq
type semenv_elem =
| SEType of Spec.typ
| SEArrayGroup of Spec.array_group3 None
| SEMapGroup of Spec.map_group None

[@@ bounded_attr; sem_attr]
noeq
type semenv = {
  se_bound: name_env;
  se_env: (name se_bound -> semenv_elem);
}

[@@bounded_attr]
let empty_name_env (_: string) : GTot bool = false

[@@bounded_attr]
let extend_name_env (e: name_env) (new_name: string) (s: string) : GTot bool =
  if s = new_name then true else name_mem s e

[@@"opaque_to_smt"] irreducible
let name_empty_elim (t: Type) (x: name empty_name_env) : Tot t = false_elim ()

[@@ bounded_attr; sem_attr]
let empty_semenv = {
  se_bound = empty_name_env;
  se_env = name_empty_elim _;
}

[@@ sem_attr]
let se_typ
  (se: semenv)
  (i: name se.se_bound)
: Tot Spec.typ
= match se.se_env i with
  | SEType t -> t
  | _ -> Spec.t_always_false

[@@ sem_attr]
let se_array_group
  (se: semenv)
  (i: name se.se_bound)
: Tot (Spec.array_group3 None)
= match se.se_env i with
  | SEArrayGroup t -> t
  | _ -> Spec.array_group3_always_false

[@@ sem_attr]
let se_map_group
  (se: semenv)
  (i: name se.se_bound)
: Tot (Spec.map_group None)
= match se.se_env i with
  | SEMapGroup t -> t
  | _ -> Spec.map_group_empty

let name_env_included (s1 s2: name_env) : Tot prop =
  (forall (i: name s1) . i `name_mem` s2)

let semenv_included (s1 s2: semenv) : Tot prop =
  name_env_included s1.se_bound s2.se_bound /\
  (forall (i: name s1.se_bound) . s1.se_env i == s2.se_env i)

let semenv_included_trans (s1 s2 s3: semenv) : Lemma
  (requires (semenv_included s1 s2 /\ semenv_included s2 s3))
  (ensures (semenv_included s1 s3))
  [SMTPat (semenv_included s1 s3); SMTPat (semenv_included s1 s2)]
= ()

[@@"opaque_to_smt"; bounded_attr; sem_attr]
let semenv_extend_gen
  (se: semenv)
  (new_name: string)
  (a: semenv_elem)
: Pure semenv
    (requires
      (~ (name_mem new_name se.se_bound))
    )
    (ensures fun se' ->
      se'.se_bound == se.se_bound `extend_name_env` new_name /\
      semenv_included se se' /\
      se'.se_env new_name == a
    )
= let se_bound' = se.se_bound `extend_name_env` new_name in
  {
    se_bound = se_bound';
    se_env = (fun (i: name se_bound') -> if i = new_name then a else se.se_env i);
  }

[@@bounded_attr; sem_attr]
let semenv_extend_typ
  (se: semenv)
  (new_name: string)
  (a: Spec.typ)
: Pure semenv
    (requires
      (~ (name_mem new_name se.se_bound))
    )
    (ensures fun se' ->
      se'.se_bound == se.se_bound `extend_name_env` new_name /\
      semenv_included se se' /\
      se'.se_env new_name == SEType a
    )
= semenv_extend_gen se new_name (SEType a)

[@@bounded_attr; sem_attr]
let semenv_extend_array_group
  (se: semenv)
  (new_name: string)
  (a: Spec.array_group3 None)
: Pure semenv
    (requires
      (~ (name_mem new_name se.se_bound))
    )
    (ensures fun se' ->
      se'.se_bound == se.se_bound `extend_name_env` new_name /\
      semenv_included se se' /\
      se'.se_env new_name == SEArrayGroup a
    )
= semenv_extend_gen se new_name (SEArrayGroup a)

[@@bounded_attr; sem_attr]
let semenv_extend_map_group
  (se: semenv)
  (new_name: string)
  (a: Spec.map_group None)
: Pure semenv
    (requires
      (~ (name_mem new_name se.se_bound))
    )
    (ensures fun se' ->
      se'.se_bound == se.se_bound `extend_name_env` new_name /\
      semenv_included se se' /\
      se'.se_env new_name == SEMapGroup a
    )
= semenv_extend_gen se new_name (SEMapGroup a)

[@@ bounded_attr ]
let rec elem_typ_bounded
  (bound: name_env)
  (t: elem_typ)
: GTot bool
= match t with
  | TDef i -> i `name_mem` bound
  | TElemArray j -> elem_array_group_bounded bound j
  | TMap j -> j `name_mem` bound
  | _ -> true

and atom_array_group_bounded
  (bound: name_env)
  (t: atom_array_group)
: GTot bool
= match t with
  | TADef i -> i `name_mem` bound
  | TAElem t -> elem_typ_bounded bound t

and elem_array_group_bounded
  (bound: name_env)
  (t: elem_array_group)
: GTot bool
= match t with
  | TAAtom t -> atom_array_group_bounded bound t
  | TAZeroOrMore t -> atom_array_group_bounded bound t
  | TAOneOrMore t -> atom_array_group_bounded bound t
  | TAZeroOrOne t -> atom_array_group_bounded bound t

[@@ sem_attr ]
let rec elem_typ_sem
  (env: semenv)
  (t: elem_typ)
: Pure Spec.typ
  (requires elem_typ_bounded env.se_bound t)
  (ensures fun _ -> True)
= match t with
  | TDef i -> se_typ env i
  | TElemArray i -> Spec.t_array3 (elem_array_group_sem env i)
  | TMap i -> Spec.t_map (se_map_group env i)
  | TFalse -> Spec.t_false
  | TTrue -> Spec.t_true
  | TBool -> Spec.t_bool
  | TNil -> Spec.t_nil
  | TUndefined -> Spec.t_undefined
  | TByteString -> Spec.bstr
  | TTextString -> Spec.tstr
  | TUIntLiteral n -> Spec.t_uint_literal n

and atom_array_group_sem
  (env: semenv)
  (t: atom_array_group)
: Pure (Spec.array_group3 None)
    (requires atom_array_group_bounded env.se_bound t)
    (ensures fun _ -> True)
= match t with
  | TADef i -> se_array_group env i
  | TAElem j -> Spec.array_group3_item (elem_typ_sem env j)

and elem_array_group_sem
  (env: semenv)
  (t: elem_array_group)
: Pure (Spec.array_group3 None)
    (requires elem_array_group_bounded env.se_bound t)
    (ensures fun _ -> True)
= match t with
  | TAAtom i -> atom_array_group_sem env i
  | TAZeroOrMore i -> Spec.array_group3_zero_or_more (atom_array_group_sem env i)
  | TAOneOrMore i -> Spec.array_group3_one_or_more (atom_array_group_sem env i)
  | TAZeroOrOne i -> Spec.array_group3_zero_or_one (atom_array_group_sem env i)

let rec elem_typ_bounded_incr
  (bound1 bound2: name_env)
  (t: elem_typ)
: Lemma
  (requires
    bound1 `name_env_included` bound2 /\
    elem_typ_bounded bound1 t
  )
  (ensures elem_typ_bounded bound2 t)
  [SMTPatOr [
    [SMTPat (elem_typ_bounded bound1 t); SMTPat (bound1 `name_env_included` bound2)];
    [SMTPat (elem_typ_bounded bound2 t); SMTPat (bound1 `name_env_included` bound2)];
  ]]
= match t with
  | TElemArray i -> elem_array_group_bounded_incr bound1 bound2 i
  | _ -> ()

and atom_array_group_bounded_incr
  (bound1 bound2: name_env)
  (t: atom_array_group)
: Lemma
  (requires
    bound1 `name_env_included` bound2 /\
    atom_array_group_bounded bound1 t
  )
  (ensures atom_array_group_bounded bound2 t)
  [SMTPatOr [
    [SMTPat (atom_array_group_bounded bound1 t); SMTPat (bound1 `name_env_included` bound2)];
    [SMTPat (atom_array_group_bounded bound2 t); SMTPat (bound1 `name_env_included` bound2)];
  ]]
= match t with
  | TAElem t -> elem_typ_bounded_incr bound1 bound2 t
  | _ -> ()

and elem_array_group_bounded_incr
  (bound1 bound2: name_env)
  (t: elem_array_group)
: Lemma
  (requires
    bound1 `name_env_included` bound2 /\
    elem_array_group_bounded bound1 t
  )
  (ensures elem_array_group_bounded bound2 t)
  [SMTPatOr [
    [SMTPat (elem_array_group_bounded bound1 t); SMTPat (bound1 `name_env_included` bound2)];
    [SMTPat (elem_array_group_bounded bound2 t); SMTPat (bound1 `name_env_included` bound2)];
  ]]
= match t with
  | TAAtom t
  | TAZeroOrMore t
  | TAOneOrMore t
  | TAZeroOrOne t
  -> atom_array_group_bounded_incr bound1 bound2 t

let rec elem_typ_sem_included (s1 s2: semenv) (t: elem_typ) : Lemma
  (requires 
    semenv_included s1 s2 /\
    elem_typ_bounded s1.se_bound t
  )
  (ensures
    elem_typ_bounded s1.se_bound t /\
    elem_typ_bounded s2.se_bound t /\
    elem_typ_sem s2 t == elem_typ_sem s1 t
  )
  [SMTPatOr [
    [SMTPat (elem_typ_sem s1 t); SMTPat (semenv_included s1 s2)];
    [SMTPat (elem_typ_sem s2 t); SMTPat (semenv_included s1 s2)];
  ]]
= match t with
  | TElemArray l -> elem_array_group_sem_included s1 s2 l
  | _ -> ()

and atom_array_group_sem_included (s1 s2: semenv) (t: atom_array_group) : Lemma
  (requires 
    semenv_included s1 s2 /\
    atom_array_group_bounded s1.se_bound t
  )
  (ensures
    atom_array_group_bounded s1.se_bound t /\
    atom_array_group_bounded s2.se_bound t /\
    atom_array_group_sem s2 t == atom_array_group_sem s1 t
  )
  [SMTPatOr [
    [SMTPat (atom_array_group_sem s1 t); SMTPat (semenv_included s1 s2)];
    [SMTPat (atom_array_group_sem s2 t); SMTPat (semenv_included s1 s2)];
  ]]
= match t with
  | TAElem t -> elem_typ_sem_included s1 s2 t
  | _ -> ()

and elem_array_group_sem_included (s1 s2: semenv) (t: elem_array_group) : Lemma
  (requires 
    semenv_included s1 s2 /\
    elem_array_group_bounded s1.se_bound t
  )
  (ensures
    elem_array_group_bounded s1.se_bound t /\
    elem_array_group_bounded s2.se_bound t /\
    elem_array_group_sem s2 t == elem_array_group_sem s1 t
  )
  [SMTPatOr [
    [SMTPat (elem_array_group_sem s1 t); SMTPat (semenv_included s1 s2)];
    [SMTPat (elem_array_group_sem s2 t); SMTPat (semenv_included s1 s2)];
  ]]
= match t with
  | TAAtom t
  | TAZeroOrMore t
  | TAOneOrMore t
  | TAZeroOrOne t
  -> atom_array_group_sem_included s1 s2 t

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
    bound1 `name_env_included` bound2 /\
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
    bound1 `name_env_included` bound2 /\
    array_group_bounded bound1 t
  )
  (ensures array_group_bounded bound2 t)
  (decreases t)
  [SMTPatOr [
    [SMTPat (array_group_bounded bound1 t); SMTPat (bound1 `name_env_included` bound2)];
    [SMTPat (array_group_bounded bound2 t); SMTPat (bound1 `name_env_included` bound2)];
  ]]
= match t with
  | [] -> ()
  | (_, a) :: q ->
    assert (elem_array_group_bounded bound2 a);
    array_group_bounded_incr bound1 bound2 q

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
  [SMTPatOr [
    [SMTPat (array_group_sem s1 t); SMTPat (semenv_included s1 s2)];
    [SMTPat (array_group_sem s2 t); SMTPat (semenv_included s1 s2)];
  ]]
= match t with
  | [] -> ()
  | [_, a] -> elem_array_group_sem_included s1 s2 a
  | (_, a) :: q ->
    elem_array_group_sem_included s1 s2 a;
    array_group_sem_included s1 s2 q

[@@ bounded_attr ]
let typ_bounded
  (bound: name_env)
  (t: typ)
: GTot bool
= match t with
  | TElem t -> elem_typ_bounded bound t
  | TChoice l -> sem_typ_choice_bounded bound l
  | TTag _tag t -> elem_typ_bounded bound t
  | TArray a -> array_group_bounded bound a
  | TEscapeHatch _ -> true

let typ_bounded_incr
  (bound1 bound2: name_env)
  (t: typ)
: Lemma
  (requires
    bound1 `name_env_included` bound2 /\
    typ_bounded bound1 t
  )
  (ensures typ_bounded bound2 t)
  [SMTPatOr [
    [SMTPat (typ_bounded bound1 t); SMTPat (bound1 `name_env_included` bound2)];
    [SMTPat (typ_bounded bound2 t); SMTPat (bound1 `name_env_included` bound2)];
  ]]
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
  | TArray a -> Spec.t_array3 (array_group_sem env a)
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
  [SMTPatOr [
    [SMTPat (typ_sem s1 t); SMTPat (semenv_included s1 s2)];
    [SMTPat (typ_sem s2 t); SMTPat (semenv_included s1 s2)];
  ]]
= match t with
  | TChoice l -> sem_typ_choice_included s1 s2 l
  | _ -> ()

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

let array_group_sem_cons
  (env: semenv)
  (n: string)
  (t: elem_array_group)
  (q: array_group)
: Lemma
  (requires array_group_bounded env.se_bound ((n, t) :: q))
  (ensures array_group_sem env ((n, t) :: q) `Spec.array_group3_equiv` (elem_array_group_sem env t `Spec.array_group3_concat` array_group_sem env q))
= ()

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

[@@ sem_attr]
let ast_env_elem0 (s: semenv_elem) : Type0 =
  match s with
  | SEType _ -> typ
  | SEArrayGroup _ -> array_group
  | SEMapGroup _ -> map_group

let ast_env_elem_prop (e_semenv: semenv) (s: semenv_elem) (x: ast_env_elem0 s) : Tot prop =
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

let ast_env_elem_prop_included (e1 e2: semenv) (s: semenv_elem) (x: ast_env_elem0 s) : Lemma
  (requires semenv_included e1 e2 /\
    ast_env_elem_prop e1 s x
  )
  (ensures ast_env_elem_prop e2 s x)
= match s with
  | SEType _ -> typ_sem_included e1 e2 x
  | SEArrayGroup _ -> array_group_sem_included e1 e2 x
  | SEMapGroup _ -> () // TODO

[@@ sem_attr]
let ast_env_elem (e_semenv: semenv) (s: semenv_elem) =
  (x: ast_env_elem0 s { ast_env_elem_prop e_semenv s x })

[@@ bounded_attr; sem_attr]
noeq
type ast_env = {
  e_semenv: semenv;
  e_env: (i: name e_semenv.se_bound) -> (ast_env_elem e_semenv (e_semenv.se_env i));
}

[@@sem_attr]
let rec elem_typ_env_sem
  (e: ast_env)
  (fuel: nat)
  (t: elem_typ)
: Pure Spec.typ
  (requires elem_typ_bounded e.e_semenv.se_bound t)
  (ensures fun t' -> t' `Spec.typ_equiv` elem_typ_sem e.e_semenv t)
  (decreases fuel)
= if fuel = 0
  then elem_typ_sem e.e_semenv t
  else let fuel' : nat = fuel - 1 in
  match t with
  | TDef i ->
    if SEType? (e.e_semenv.se_env i)
    then typ_env_sem e fuel' (e.e_env i)
    else elem_typ_sem e.e_semenv t
  | _ ->  elem_typ_sem e.e_semenv t

and typ_env_sem
  (e: ast_env)
  (fuel: nat)
  (t: typ)
: Pure Spec.typ
  (requires typ_bounded e.e_semenv.se_bound t)
  (ensures fun t' -> t' `Spec.typ_equiv` typ_sem e.e_semenv t)
  (decreases fuel)
= if fuel = 0
  then typ_sem e.e_semenv t
  else let fuel' : nat = fuel - 1 in
  match t with
  | TElem t -> elem_typ_env_sem e fuel' t
  | TTag tag t -> Spec.t_tag tag (elem_typ_env_sem e fuel' t)
  | _ -> typ_sem e.e_semenv t

[@@"opaque_to_smt"] irreducible // because of false_elim
let e_env_empty (i: name empty_name_env) : Tot (ast_env_elem empty_semenv (empty_semenv.se_env i)) = false_elim ()

[@@"opaque_to_smt"; bounded_attr; sem_attr]
let empty_ast_env : (e: ast_env {
  e.e_semenv.se_bound == empty_name_env
}) = {
  e_semenv = empty_semenv;
  e_env = e_env_empty;
}

let ast_env_included
  (e1 e2: ast_env)
: Tot prop
= semenv_included e1.e_semenv e2.e_semenv /\
  (forall (i: name e1.e_semenv.se_bound) . e2.e_env i == e1.e_env i)

let ast_env_included_trans (s1 s2 s3: ast_env) : Lemma
  (requires (ast_env_included s1 s2 /\ ast_env_included s2 s3))
  (ensures (ast_env_included s1 s3))
  [SMTPat (ast_env_included s1 s3); SMTPat (ast_env_included s1 s2)]
= ()

[@@"opaque_to_smt"; bounded_attr; sem_attr]
let ast_env_extend_gen
  (e: ast_env)
  (new_name: string)
  (s: semenv_elem)
  (x: ast_env_elem e.e_semenv s)
: Pure ast_env
    (requires
      (~ (new_name `name_mem` e.e_semenv.se_bound))
    )
    (ensures fun e' ->
      e'.e_semenv.se_bound == e.e_semenv.se_bound `extend_name_env` new_name /\
      ast_env_included e e' /\
      e'.e_semenv.se_env new_name == s /\
      e'.e_env new_name == x
    )
= let se' = semenv_extend_gen e.e_semenv new_name s in
  {
    e_semenv = se';
    e_env = (fun (i: name se'.se_bound) ->
      let x' : ast_env_elem e.e_semenv (se'.se_env i) =
        if i = new_name
        then x
        else e.e_env i
      in
      ast_env_elem_prop_included e.e_semenv se' (se'.se_env i) x';
      x'
    );
  }

[@@ bounded_attr; sem_attr]
let ast_env_extend_typ
  (e: ast_env)
  (new_name: string)
  (new_name_fresh: squash (~ (new_name `name_mem` e.e_semenv.se_bound))) // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  (a: typ)
  (sq: squash (
    typ_bounded e.e_semenv.se_bound a // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  ))
: Tot (e': ast_env {
      e'.e_semenv.se_bound == e.e_semenv.se_bound `extend_name_env` new_name /\
      ast_env_included e e' /\
      e'.e_semenv.se_env new_name == SEType (typ_sem e.e_semenv a)   /\
      e'.e_env new_name == a
  })
= ast_env_extend_gen e new_name (SEType (typ_sem e.e_semenv a)) a

[@@ bounded_attr; sem_attr]
let ast_env_extend_array_group
  (e: ast_env)
  (new_name: string) // ideally by SMT
  (new_name_fresh: squash (~ (new_name `name_mem` e.e_semenv.se_bound))) // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  (a: array_group)
  (sq: squash (
    array_group_bounded e.e_semenv.se_bound a // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  ))
: Tot (e': ast_env {
      e'.e_semenv.se_bound == e.e_semenv.se_bound `extend_name_env` new_name /\
      ast_env_included e e' /\
      e'.e_semenv.se_env new_name == SEArrayGroup (array_group_sem e.e_semenv a) /\
      e'.e_env new_name == a
  })
= ast_env_extend_gen e new_name (SEArrayGroup (array_group_sem e.e_semenv a)) a

[@@ bounded_attr; sem_attr]
let ast_env_extend_map_group
  (e: ast_env)
  (new_name: string) // ideally by SMT
  (new_name_fresh: squash (~ (new_name `name_mem` e.e_semenv.se_bound))) // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  (a: map_group)
  (sq: squash (
    map_group_bounded e.e_semenv.se_bound a // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  ))
: Tot (e': ast_env {
      e'.e_semenv.se_bound == e.e_semenv.se_bound `extend_name_env` new_name /\
      ast_env_included e e' /\
      e'.e_semenv.se_env new_name == SEMapGroup (map_group_sem e.e_semenv a) /\
      e'.e_env new_name == a
  })
= ast_env_extend_gen e new_name (SEMapGroup (map_group_sem e.e_semenv a)) a

(* Recursion *)

let restrict_typ_spec
  (bound: CBOR.Spec.raw_data_item)
  (f: (x: CBOR.Spec.raw_data_item { x << bound }) -> GTot bool)
  (x: CBOR.Spec.raw_data_item)
: GTot bool
= if FStar.StrongExcludedMiddle.strong_excluded_middle (x << bound)
  then f x
  else false

let strong_excluded_middle_true_intro
  (x: Type0)
: Lemma
  (requires x)
  (ensures (FStar.StrongExcludedMiddle.strong_excluded_middle x == true))
= ()

#restart-solver
let restrict_typ_spec_eq_intro
  (bound: CBOR.Spec.raw_data_item)
  (f: (x: CBOR.Spec.raw_data_item { x << bound }) -> GTot bool)
  (x: CBOR.Spec.raw_data_item)
: Lemma
  (requires (x << bound))
  (ensures (restrict_typ_spec bound f x == f x))
= strong_excluded_middle_true_intro (x << bound)

let rec array_group3_zero_or_more_bounded_ext
  (#t: Type)
  (a1 a2: Spec.array_group3 None)
  (x0: t)
  (phi: (x: list CBOR.Spec.raw_data_item {Spec.opt_precedes_list x (Some x0)}) ->
    Lemma (a1 x == a2 x)
  )
  (x: list CBOR.Spec.raw_data_item {Spec.opt_precedes_list x (Some x0)})
: Lemma
  (ensures (Spec.array_group3_zero_or_more a1 x == Spec.array_group3_zero_or_more a2 x))
  (decreases (List.Tot.length x))
= phi x;
  match a1 x with
  | None -> ()
  | Some (x1, x2) ->
    List.Tot.append_length x1 x2;
    if Nil? x1
    then ()
    else array_group3_zero_or_more_bounded_ext a1 a2 x0 phi x2

let array_group3_one_or_more_bounded_ext
  (#t: Type)
  (a1 a2: Spec.array_group3 None)
  (x0: t)
  (phi: (x: list CBOR.Spec.raw_data_item {Spec.opt_precedes_list x (Some x0)}) ->
    Lemma (a1 x == a2 x)
  )
  (x: list CBOR.Spec.raw_data_item {Spec.opt_precedes_list x (Some x0)})
: Lemma
  (ensures (Spec.array_group3_one_or_more a1 x == Spec.array_group3_one_or_more a2 x))
= phi x;
  match a1 x with
  | None -> ()
  | Some (x1, x2) -> array_group3_zero_or_more_bounded_ext a1 a2 x0 phi x2

#restart-solver
let rec elem_typ_sem_restrict_typ_spec_correct
  (e: ast_env)
  (new_name: string {~ (name_mem new_name e.e_semenv.se_bound) })
  (s: CDDL.Spec.typ)
  (x0: CBOR.Spec.raw_data_item)
  (t: elem_typ { elem_typ_bounded (extend_name_env e.e_semenv.se_bound new_name) t })
  (x: CBOR.Spec.raw_data_item { x << x0 })
: Lemma
  (ensures (
    elem_typ_sem
      (semenv_extend_gen e.e_semenv new_name (SEType s))
      t
      x
    ==
    elem_typ_sem
      (semenv_extend_gen e.e_semenv new_name (SEType (restrict_typ_spec x0 s)))
      t
      x
  ))
  (decreases t)
= restrict_typ_spec_eq_intro x0 s x;
  match t with
  | TElemArray i ->
    begin match x with
    | CBOR.Spec.Array x' ->
      elem_array_group_sem_restrict_typ_spec_correct e new_name s x0 i x'
    | _ -> ()
    end
  | _ -> ()

and atom_array_group_sem_restrict_typ_spec_correct
  (e: ast_env)
  (new_name: string {~ (name_mem new_name e.e_semenv.se_bound) })
  (s: CDDL.Spec.typ)
  (x0: CBOR.Spec.raw_data_item)
  (t: atom_array_group { atom_array_group_bounded (extend_name_env e.e_semenv.se_bound new_name) t })
  (x: list CBOR.Spec.raw_data_item { Spec.opt_precedes_list x (Some x0) })
: Lemma
  (ensures (
    atom_array_group_sem
      (semenv_extend_gen e.e_semenv new_name (SEType s))
      t
      x
    ==
    atom_array_group_sem
      (semenv_extend_gen e.e_semenv new_name (SEType (restrict_typ_spec x0 s)))
      t
      x
  ))
  (decreases t)
= match t with
  | TAElem t ->
    begin match x with
    | [] -> ()
    | x' :: _ ->
      elem_typ_sem_restrict_typ_spec_correct e new_name s x0 t x'
    end
  | _ -> ()

and elem_array_group_sem_restrict_typ_spec_correct
  (e: ast_env)
  (new_name: string {~ (name_mem new_name e.e_semenv.se_bound) })
  (s: CDDL.Spec.typ)
  (x0: CBOR.Spec.raw_data_item)
  (t: elem_array_group { elem_array_group_bounded (extend_name_env e.e_semenv.se_bound new_name) t })
  (x: list CBOR.Spec.raw_data_item { Spec.opt_precedes_list x (Some x0) })
: Lemma
  (ensures (
    elem_array_group_sem
      (semenv_extend_gen e.e_semenv new_name (SEType s))
      t
      x
    ==
    elem_array_group_sem
      (semenv_extend_gen e.e_semenv new_name (SEType (restrict_typ_spec x0 s)))
      t
      x
  ))
  (decreases t)
= match t with
  | TAZeroOrOne t
  | TAAtom t ->
    atom_array_group_sem_restrict_typ_spec_correct e new_name s x0 t x
  | TAZeroOrMore t ->
    array_group3_zero_or_more_bounded_ext
      (atom_array_group_sem
        (semenv_extend_gen e.e_semenv new_name (SEType s))
        t
      )
      (atom_array_group_sem
        (semenv_extend_gen e.e_semenv new_name (SEType (restrict_typ_spec x0 s)))
        t
      )
      x0
      (fun x -> atom_array_group_sem_restrict_typ_spec_correct e new_name s x0 t x)
      x
  | TAOneOrMore t ->
    array_group3_one_or_more_bounded_ext
      (atom_array_group_sem
        (semenv_extend_gen e.e_semenv new_name (SEType s))
        t
      )
      (atom_array_group_sem
        (semenv_extend_gen e.e_semenv new_name (SEType (restrict_typ_spec x0 s)))
        t
      )
      x0
      (fun x -> atom_array_group_sem_restrict_typ_spec_correct e new_name s x0 t x)
      x

let rec sem_typ_choice_restrict_typ_spec_correct
  (e: ast_env)
  (new_name: string {~ (name_mem new_name e.e_semenv.se_bound) })
  (s: CDDL.Spec.typ)
  (x0: CBOR.Spec.raw_data_item)
  (t: list elem_typ { sem_typ_choice_bounded (extend_name_env e.e_semenv.se_bound new_name) t })
  (x: CBOR.Spec.raw_data_item { x << x0 })
: Lemma
  (ensures (
    sem_typ_choice
      (semenv_extend_gen e.e_semenv new_name (SEType s))
      t
      x
    ==
    sem_typ_choice
      (semenv_extend_gen e.e_semenv new_name (SEType (restrict_typ_spec x0 s)))
      t
      x
  ))
  (decreases t)
= match t with
  | [] -> ()
  | a :: q ->
    elem_typ_sem_restrict_typ_spec_correct e new_name s x0 a x;
    sem_typ_choice_restrict_typ_spec_correct e new_name s x0 q x

let rec array_group_sem_restrict_typ_spec_correct
  (e: ast_env)
  (new_name: string {~ (name_mem new_name e.e_semenv.se_bound) })
  (s: CDDL.Spec.typ)
  (x0: CBOR.Spec.raw_data_item)
  (t: array_group { array_group_bounded (extend_name_env e.e_semenv.se_bound new_name) t })
  (x: list CBOR.Spec.raw_data_item { Spec.opt_precedes_list x (Some x0) })
: Lemma
  (ensures (
    array_group_sem
      (semenv_extend_gen e.e_semenv new_name (SEType s))
      t
      x
    ==
    array_group_sem
      (semenv_extend_gen e.e_semenv new_name (SEType (restrict_typ_spec x0 s)))
      t
      x
  ))
  (decreases t)
= match t with
  | [] -> ()
  | [_, t] -> elem_array_group_sem_restrict_typ_spec_correct e new_name s x0 t x
  | (_, t) :: t' ->
    elem_array_group_sem_restrict_typ_spec_correct e new_name s x0 t x;
    begin match 
      elem_array_group_sem
        (semenv_extend_gen e.e_semenv new_name (SEType s))
        t
        x
    with
    | None -> ()
    | Some (_, x') -> array_group_sem_restrict_typ_spec_correct e new_name s x0 t' x'
    end

#restart-solver
let typ_sem_restrict_typ_spec_correct
  (e: ast_env)
  (new_name: string {~ (name_mem new_name e.e_semenv.se_bound) })
  (s: CDDL.Spec.typ)
  (x0: CBOR.Spec.raw_data_item)
  (t: typ { typ_bounded (extend_name_env e.e_semenv.se_bound new_name) t })
  (x: CBOR.Spec.raw_data_item { x << x0 })
: Lemma
  (ensures (
    typ_sem
      (semenv_extend_gen e.e_semenv new_name (SEType s))
      t
      x
    ==
    typ_sem
      (semenv_extend_gen e.e_semenv new_name (SEType (restrict_typ_spec x0 s)))
      t
      x
  ))
= let se1 = (semenv_extend_gen e.e_semenv new_name (SEType s)) in
  let se2 = (semenv_extend_gen e.e_semenv new_name (SEType (restrict_typ_spec x0 s))) in
  match t with
  | TElem t' -> elem_typ_sem_restrict_typ_spec_correct e new_name s x0 t' x
  | TChoice l -> sem_typ_choice_restrict_typ_spec_correct e new_name s x0 l x
  | TArray a ->
    begin match x with
    | CBOR.Spec.Array x' -> array_group_sem_restrict_typ_spec_correct e new_name s x0 a x'
    | _ -> ()
    end
  | TTag tag' t' ->
    begin match x with
    | CBOR.Spec.Tagged tag x' ->
      if tag = tag'
      then elem_typ_sem_restrict_typ_spec_correct e new_name s x0 t' x'
      else ()
    | _ -> ()
    end
  | TEscapeHatch _ -> ()

noeq
type result =
| ResultSuccess
| ResultFailure of string
| ResultOutOfFuel

#restart-solver
let rec elem_typ_productive
  (fuel: nat)
  (e: ast_env)
  (new_name: string {~ (name_mem new_name e.e_semenv.se_bound) })
  (t: elem_typ { elem_typ_bounded (extend_name_env e.e_semenv.se_bound new_name) t })
: Tot result
  (decreases fuel)
= match t with
  | TDef i ->
    if fuel = 0
    then ResultOutOfFuel
    else if i = new_name
    then ResultFailure "elem_typ_productive: unguarded recursive call"
    else if SEType? (e.e_semenv.se_env i)
    then begin
      let t = e.e_env i in
      typ_bounded_incr e.e_semenv.se_bound (extend_name_env e.e_semenv.se_bound new_name) t;
      typ_productive (fuel - 1) e new_name t
    end
    else ResultSuccess
  | _ -> ResultSuccess

and typ_productive
  (fuel: nat)
  (e: ast_env)
  (new_name: string {~ (name_mem new_name e.e_semenv.se_bound) })
  (t: typ { typ_bounded (extend_name_env e.e_semenv.se_bound new_name) t })
: Tot result
  (decreases fuel)
= if fuel = 0
  then ResultOutOfFuel
  else let fuel' : nat = fuel - 1 in
  match t with
  | TElem t -> elem_typ_productive fuel' e new_name t
  | TChoice l -> choice_typ_productive fuel' e new_name l
  | _ -> ResultSuccess

and choice_typ_productive
  (fuel: nat)
  (e: ast_env)
  (new_name: string {~ (name_mem new_name e.e_semenv.se_bound) })
  (t: list elem_typ { sem_typ_choice_bounded (extend_name_env e.e_semenv.se_bound new_name) t })
: Tot result
  (decreases fuel)
= if fuel = 0
  then ResultOutOfFuel
  else let fuel' : nat = fuel - 1 in
  match t with
  | [] -> ResultSuccess
  | a :: q ->
    let res1 = elem_typ_productive fuel' e new_name a in
    if not (ResultSuccess? res1)
    then res1
    else choice_typ_productive fuel' e new_name q

let rec elem_typ_productive_correct
  (fuel: nat)
  (e: ast_env)
  (new_name: string {~ (name_mem new_name e.e_semenv.se_bound) })
  (s: CDDL.Spec.typ)
  (t: elem_typ { elem_typ_bounded (extend_name_env e.e_semenv.se_bound new_name) t /\
    elem_typ_productive fuel e new_name t == ResultSuccess
  })
  (x: CBOR.Spec.raw_data_item)
: Lemma
  (ensures (
    elem_typ_sem
      (semenv_extend_gen e.e_semenv new_name (SEType s))
      t
      x
    ==
    elem_typ_sem
      (semenv_extend_gen e.e_semenv new_name (SEType (restrict_typ_spec x s)))
      t
      x
  ))
  (decreases fuel)
= match t with
  | TDef i ->
    if SEType? (e.e_semenv.se_env i)
    then begin
      let t = e.e_env i in
      typ_bounded_incr e.e_semenv.se_bound (extend_name_env e.e_semenv.se_bound new_name) t;
      typ_productive_correct (fuel - 1) e new_name s t x
    end
    else ()
  | TElemArray t ->
    begin match x with
    | CBOR.Spec.Array x' ->
      elem_array_group_sem_restrict_typ_spec_correct e new_name s x t x'
    | _ -> ()
    end
  | _ -> ()

and typ_productive_correct
  (fuel: nat)
  (e: ast_env)
  (new_name: string {~ (name_mem new_name e.e_semenv.se_bound) })
  (s: CDDL.Spec.typ)
  (t: typ { typ_bounded (extend_name_env e.e_semenv.se_bound new_name) t /\
    typ_productive fuel e new_name t == ResultSuccess
  })
  (x: CBOR.Spec.raw_data_item)
: Lemma
  (ensures (
    typ_sem
      (semenv_extend_gen e.e_semenv new_name (SEType s))
      t
      x
    ==
    typ_sem
      (semenv_extend_gen e.e_semenv new_name (SEType (restrict_typ_spec x s)))
      t
      x
  ))
  (decreases fuel)
= match t with
  | TElem t -> elem_typ_productive_correct (fuel - 1) e new_name s t x
  | TChoice l -> choice_typ_productive_correct (fuel - 1) e new_name s l x
  | TTag tag t' ->
    begin match x with
    | CBOR.Spec.Tagged tag' x' ->
      if tag = tag'
      then elem_typ_sem_restrict_typ_spec_correct e new_name s x t' x'
      else ()
    | _ -> ()
    end
  | TArray t ->
    begin match x with
    | CBOR.Spec.Array x' ->
      array_group_sem_restrict_typ_spec_correct e new_name s x t x'
    | _ -> ()
    end
  | TEscapeHatch _ -> ()

and choice_typ_productive_correct
  (fuel: nat)
  (e: ast_env)
  (new_name: string {~ (name_mem new_name e.e_semenv.se_bound) })
  (s: CDDL.Spec.typ)
  (t: list elem_typ { sem_typ_choice_bounded (extend_name_env e.e_semenv.se_bound new_name) t /\
    choice_typ_productive fuel e new_name t == ResultSuccess
  })
  (x: CBOR.Spec.raw_data_item)
: Lemma
  (ensures (
    sem_typ_choice
      (semenv_extend_gen e.e_semenv new_name (SEType s))
      t
      x
    ==
    sem_typ_choice
      (semenv_extend_gen e.e_semenv new_name (SEType (restrict_typ_spec x s)))
      t
      x
  ))
  (decreases fuel)
= match t with
  | [] -> ()
  | a :: q ->
    elem_typ_productive_correct (fuel - 1) e new_name s a x;
    choice_typ_productive_correct (fuel - 1) e new_name s q x

[@@"opaque_to_smt"]
let rec rec_typ_sem
  (e: semenv)
  (new_name: string {~ (name_mem new_name e.se_bound) })
  (t: typ { typ_bounded (extend_name_env e.se_bound new_name) t })
  (x: CBOR.Spec.raw_data_item)
: GTot bool
  (decreases x)
= typ_sem
    (semenv_extend_gen e new_name (SEType (restrict_typ_spec x (rec_typ_sem e new_name t))))
    t
    x

#restart-solver
let rec_typ_sem_correct
  (fuel: nat)
  (e: ast_env)
  (new_name: string {~ (name_mem new_name e.e_semenv.se_bound) })
  (t: typ { typ_bounded (extend_name_env e.e_semenv.se_bound new_name) t /\
    typ_productive fuel e new_name t == ResultSuccess
  })
: Lemma
  (ensures (
    rec_typ_sem e.e_semenv new_name t
    `CDDL.Spec.typ_equiv`
    typ_sem
      (semenv_extend_gen e.e_semenv new_name (SEType (rec_typ_sem e.e_semenv new_name t)))
      t
  ))
= let prf
    (x: CBOR.Spec.raw_data_item)
  : Lemma
    (
      rec_typ_sem e.e_semenv new_name t x ==
      typ_sem
        (semenv_extend_gen e.e_semenv new_name (SEType (rec_typ_sem e.e_semenv new_name t)))
        t
        x
    )
  = assert_norm (rec_typ_sem e.e_semenv new_name t x ==
      typ_sem
        (semenv_extend_gen e.e_semenv new_name (SEType (restrict_typ_spec x (rec_typ_sem e.e_semenv new_name t))))
        t
        x
    );
    typ_productive_correct fuel e new_name (rec_typ_sem e.e_semenv new_name t) t x
  in
  Classical.forall_intro prf

let ast_env_extend_rec_typ_post
  (e: ast_env)
  (new_name: string)
  (new_name_fresh: squash (~ (new_name `name_mem` e.e_semenv.se_bound))) // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  (a: typ)
  (sq: squash (
    typ_bounded (extend_name_env e.e_semenv.se_bound new_name) a // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  ))
  (e': ast_env)
: Tot prop
=
      e'.e_semenv.se_bound == e.e_semenv.se_bound `extend_name_env` new_name /\
      ast_env_included e e' /\
      typ_bounded e'.e_semenv.se_bound a /\
      new_name `name_mem` e'.e_semenv.se_bound == true /\
      SEType? (e'.e_semenv.se_env new_name) /\
      e'.e_env new_name == a

let ast_env_extend_rec_typ_fuel
  (e: ast_env)
  (new_name: string { ~ (new_name `name_mem` e.e_semenv.se_bound)})
  (a: typ {
    typ_bounded (extend_name_env e.e_semenv.se_bound new_name) a
  })
: Type0
= (fuel: nat { typ_productive fuel e new_name a == ResultSuccess })

[@@ bounded_attr; sem_attr]
let ast_env_extend_rec_typ
  (e: ast_env)
  (new_name: string)
  (new_name_fresh: squash (~ (new_name `name_mem` e.e_semenv.se_bound))) // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  (a: typ)
  (sq: squash (
    typ_bounded (extend_name_env e.e_semenv.se_bound new_name) a // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  ))
  (fuel: ast_env_extend_rec_typ_fuel e new_name a)
: Tot (e': ast_env { ast_env_extend_rec_typ_post e new_name new_name_fresh a sq e' })
= let s = SEType (rec_typ_sem e.e_semenv new_name a) in
  rec_typ_sem_correct fuel e new_name a;
  let se' = semenv_extend_gen e.e_semenv new_name s in
  {
    e_semenv = se';
    e_env = (fun (i: name se'.se_bound) ->
      if i = new_name
      then a
      else begin
        let x' = e.e_env i in
        ast_env_elem_prop_included e.e_semenv se' (se'.se_env i) x';
        x'
      end
    );
  }

(* Equivalence, disjointness, splittability *)

// This is nothing more than delta-equivalence

#push-options "--z3rlimit 16"

[@@"opaque_to_smt"]
let rec typ_equiv
  (e: ast_env)
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
  | TArray t1, TArray t2 ->
    array_group_equiv e fuel' t1 t2
  | TElem (TElemArray i1), TElem (TElemArray i2) ->
    array_group_equiv e fuel' ["", i1] ["", i2]
  | TElem (TMap i1), TElem (TMap i2) -> i1 = i2 // TODO
  | _ -> false

and array_group_equiv
  (e: ast_env)
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
  | (s1, TAOneOrMore t1) :: q1, (s2, TAOneOrMore t2) :: q2 ->
    if array_group_equiv e fuel' [s1, TAAtom t1] [s2, TAAtom t2]
    then begin
       assert (Spec.array_group3_equiv (atom_array_group_sem e.e_semenv t1) (atom_array_group_sem e.e_semenv t2));
       assert (Spec.array_group3_equiv (Spec.array_group3_one_or_more (atom_array_group_sem e.e_semenv t1)) (Spec.array_group3_one_or_more (atom_array_group_sem e.e_semenv t2)));
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

#push-options "--z3rlimit 64 --split_queries always"

#restart-solver
[@@"opaque_to_smt"]
let rec typ_disjoint
  (e: ast_env)
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
    (b == ResultSuccess ==> Spec.typ_disjoint (typ_sem e.e_semenv t1) (typ_sem e.e_semenv t2))
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
  | TArray i1, TArray i2 ->
    Spec.array3_close_array_group (array_group_sem e.e_semenv i1);
    Spec.array3_close_array_group (array_group_sem e.e_semenv i2);
    array_group_disjoint e fuel' true i1 i2
  | TElem (TElemArray i1), TElem (TElemArray i2) ->
    Spec.array3_close_array_group (array_group_sem e.e_semenv ["", i1]);
    Spec.array3_close_array_group (array_group_sem e.e_semenv ["", i2]);
    array_group_disjoint e fuel' true ["", i1] ["", i2]
  | TArray i1, TElem (TElemArray i2)
    ->
    Spec.array3_close_array_group (array_group_sem e.e_semenv i1);
    Spec.array3_close_array_group (array_group_sem e.e_semenv ["", i2]);
    array_group_disjoint e fuel' true i1 ["", i2]
  | TElem (TElemArray i2), TArray i1
    ->
    Spec.array3_close_array_group (array_group_sem e.e_semenv i1);
    Spec.array3_close_array_group (array_group_sem e.e_semenv ["", i2]);
    array_group_disjoint e fuel' true ["", i2] i1
  | TArray _, _
  | _, TArray _ -> ResultSuccess
  | TElem TFalse, TElem TBool -> ResultFailure "typ_disjoint: TFalse, TBool"
  | TElem TBool, TElem TFalse -> ResultFailure "typ_disjoint: TBool, TFalse"
  | TElem TTrue, TElem TBool -> ResultFailure "typ_disjoint: TTrue, TBool"
  | TElem TBool, TElem TTrue -> ResultFailure "typ_disjoint: TBool, TTrue"
  | TElem (TMap _), TElem (TMap _) -> ResultFailure "typ_disjoint: TMap, TMap" // TODO
  | TElem e1, TElem e2 ->
    if e1 <> e2
    then ResultSuccess
    else ResultFailure "typ_disjoint: TElem equal"

and array_group_disjoint
  (e: ast_env)
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
      (Spec.maybe_close_array_group (array_group_sem e.e_semenv t1) close)
      (Spec.maybe_close_array_group (array_group_sem e.e_semenv t2) close)
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
  | (name, TAOneOrMore t1') :: q, _ ->
    array_group_disjoint e fuel' close ((name, TAAtom t1') :: (name, TAZeroOrMore t1') :: q) t2
  | _, (_, TAOneOrMore _) :: _ ->
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
  | (n1, TAAtom (TAElem t1')) :: q1, (n2, TAAtom (TAElem t2')) :: q2 ->
    array_group_sem_cons e.e_semenv n1 (TAAtom (TAElem t1')) q1;
    array_group_sem_cons e.e_semenv n2 (TAAtom (TAElem t2')) q2;
    if ResultSuccess? (typ_disjoint e fuel' (TElem t1') (TElem t2'))
    then ResultSuccess
    else if typ_equiv e fuel' (TElem t1') (TElem t2')
    then
      let res = array_group_disjoint e fuel' close q1 q2 in
      res
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

#push-options "--z3rlimit 32"

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
    Spec.array_group3_concat_unique_weak_intro a1 a3
      (fun l -> ())
      (fun l1 l2 ->
        let Some (l1l, l1r) = elem_array_group_sem e t1 l1 in
        List.Tot.append_assoc l1l l1r l2
      );
    assert (Spec.array_group3_concat_unique_weak a1 a3)

#pop-options

// the converse does not hold: consider a* b* a*, then [a] has two decompositions: [a] [] [] and [] [] [a]

#push-options "--z3rlimit 32"

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

#pop-options

let spec_array_group_splittable_threshold
  (e: ast_env)
: Tot Type
= (i: string) -> Pure bool
    (requires True)
    (ensures fun b ->
      b == true ==> 
      (i `name_mem` e.e_semenv.se_bound /\
        SEArrayGroup? (e.e_semenv.se_env i) /\
        spec_array_group_splittable e.e_semenv (e.e_env i)
    ))

#push-options "--z3rlimit 64 --split_queries always --ifuel 4 --fuel 4 --query_stats"

#restart-solver
[@@"opaque_to_smt"]
let rec array_group_concat_unique_strong
  (e: ast_env)
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
      assert (Spec.array_group3_concat_unique_strong
        (array_group_sem e.e_semenv [n1, t1l])
        (array_group_sem e.e_semenv (a1' `List.Tot.append` a2))
      );
      array_group_sem_cons e.e_semenv n1 t1l a1';
      array_group_sem_append e.e_semenv a1' a2;
      assert (array_group_sem e.e_semenv [n1, t1l] == elem_array_group_sem e.e_semenv t1l);
      Spec.array_group3_concat_unique_strong_equiv
        (array_group_sem e.e_semenv [n1, t1l])
        (elem_array_group_sem e.e_semenv t1l)
        (array_group_sem e.e_semenv (a1' `List.Tot.append` a2))
        (array_group_sem e.e_semenv a1' `Spec.array_group3_concat` array_group_sem e.e_semenv a2);
      assert (Spec.array_group3_concat_unique_strong
        (elem_array_group_sem e.e_semenv t1l)
        (array_group_sem e.e_semenv a1' `Spec.array_group3_concat` array_group_sem e.e_semenv a2)
      );
      Spec.array_group3_concat_unique_strong_concat_left (elem_array_group_sem e.e_semenv t1l) (array_group_sem e.e_semenv a1') (array_group_sem e.e_semenv a2);
      assert (Spec.array_group3_concat_unique_strong
        (array_group_sem e.e_semenv a1)
        (array_group_sem e.e_semenv a2)
      );
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
        let res = array_group_concat_unique_strong e e_thr fuel' t1 a2 in
        assert (res == ResultSuccess ==> Spec.array_group3_concat_unique_strong
          (array_group_sem e.e_semenv a1)
          (array_group_sem e.e_semenv a2)
        );
        res
    else ResultSuccess
  | _, (n2, TAAtom (TADef i)) :: a2' ->
    array_group_sem_cons e.e_semenv n2 (TAAtom (TADef i)) a2';
    if SEArrayGroup? (e.e_semenv.se_env i)
    then
      let t1 = e.e_env i in
      array_group_sem_append e.e_semenv t1 a2';
      Spec.array_group3_concat_equiv
        (elem_array_group_sem e.e_semenv (TAAtom (TADef i)))
        (array_group_sem e.e_semenv t1)
        (array_group_sem e.e_semenv a2')
        (array_group_sem e.e_semenv a2');
      let res = array_group_concat_unique_strong e e_thr fuel' a1 (t1 `List.Tot.append` a2') in
      if ResultSuccess? res
      then begin
        assert (Spec.array_group3_concat_unique_strong
          (array_group_sem e.e_semenv a1)
          (array_group_sem e.e_semenv a2)
        );
        ResultSuccess
      end
      else res
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
  | [n1, TAOneOrMore t1], _ ->
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
      Spec.array_group3_concat_unique_strong_one_or_more_left
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
      Spec.array_group3_concat_unique_strong_zero_or_one_left
        (atom_array_group_sem e.e_semenv t1)
        (array_group_sem e.e_semenv a2);
      ResultSuccess
    end
//  | _ -> false

#pop-options

#push-options "--z3rlimit 32 --split_queries always"

#restart-solver
[@@"opaque_to_smt"]
let rec array_group_splittable
  (e: ast_env)
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
  | [n1, TAOneOrMore t1], _ ->
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
      Spec.array_group3_concat_unique_weak_one_or_more_left
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
      Spec.array_group3_concat_unique_weak_zero_or_one_left
        (atom_array_group_sem e.e_semenv t1)
        (array_group_sem e.e_semenv a2);
      ResultSuccess
    end
//  | _ -> false

#pop-options

let rec spec_choice_typ_well_formed
  (env: semenv)
  (l: list elem_typ)
: Tot prop
= typ_bounded env.se_bound (TChoice l) /\
  begin match l with
  | [] -> True
  | [_] -> True
  | a :: q ->
    Spec.typ_disjoint (typ_sem env (TElem a)) (typ_sem env (TChoice q)) /\
    spec_choice_typ_well_formed env q
  end

let rec spec_choice_typ_well_formed_included
  (env1 env2: semenv)
  (l: list elem_typ)
: Lemma
  (requires
    semenv_included env1 env2 /\
    spec_choice_typ_well_formed env1 l
  )
  (ensures
    spec_choice_typ_well_formed env2 l
  )
= match l with
  | [] -> ()
  | [_] -> ()
  | a :: q ->
    spec_choice_typ_well_formed_included env1 env2 q

let rec choice_typ_well_formed
  (e: ast_env)
  (fuel: nat)
  (l: list elem_typ)
: Pure result
  (requires typ_bounded e.e_semenv.se_bound (TChoice l))
  (ensures fun b ->
    b == ResultSuccess ==>  spec_choice_typ_well_formed e.e_semenv l
  )
  (decreases l)
= match l with
  | [] -> ResultSuccess
  | [_] -> ResultSuccess
  | a :: q ->
    let res1 = typ_disjoint e fuel (TElem a) (TChoice q) in
    if not (ResultSuccess? res1)
    then res1
    else choice_typ_well_formed e fuel q

let spec_ast_env_elem_well_formed
  (env: semenv)
  (#s: semenv_elem)
  (e: ast_env_elem env s)
: GTot prop
= match s with
  | SEType _ ->
    let e' : typ = e in
    begin match e' with
    | TArray l -> spec_array_group_splittable env l
    | TChoice l -> spec_choice_typ_well_formed env l
    | _ -> True
    end
  | SEArrayGroup _ -> spec_array_group_splittable env e
  | SEMapGroup _ -> True

let ast_env_elem_well_formed'
  (e: ast_env)
  (e_thr: spec_array_group_splittable_threshold e)
  (fuel: nat)
  (#s: semenv_elem)
  (x: ast_env_elem e.e_semenv s)
: Pure result
    (requires True)
    (ensures fun res ->
      res == ResultSuccess ==> spec_ast_env_elem_well_formed e.e_semenv x
    )
= match s with
  | SEType _ ->
    let e' : typ = x in
    begin match e' with
    | TArray l -> array_group_splittable e e_thr fuel l []
    | TChoice l -> choice_typ_well_formed e fuel l
    | _ -> ResultSuccess
    end
  | SEArrayGroup _ -> array_group_splittable e e_thr fuel x []
  | SEMapGroup _ -> ResultSuccess

let spec_ast_env_elem_well_formed_threshold
  (e: ast_env)
: Tot Type
= (i: string) -> Pure bool
    (requires True)
    (ensures fun b ->
      b == true ==> 
      (i `name_mem` e.e_semenv.se_bound /\
        spec_ast_env_elem_well_formed e.e_semenv (e.e_env i)
    ))

[@@ bounded_attr; sem_attr]
noeq
type wf_ast_env = {
  we_env: ast_env;
  we_env_wf: spec_ast_env_elem_well_formed_threshold we_env;
  we_env_wf_prop: squash (forall (i: name we_env.e_semenv.se_bound) . we_env_wf i == true);
}

[@@"opaque_to_smt"]
let spec_array_group_splittable_threshold_of_ast_elem_well_formed_threshold
  (e: ast_env)
  (f: spec_ast_env_elem_well_formed_threshold e)
: Tot (spec_array_group_splittable_threshold e)
= (fun i ->
    if f i
    then SEArrayGroup? (e.e_semenv.se_env i)
    else false
  )

let ast_env_elem_well_formed
  (e: ast_env)
  (e_thr: spec_ast_env_elem_well_formed_threshold e)
  (fuel: nat)
  (#s: semenv_elem)
  (x: ast_env_elem e.e_semenv s)
: Pure result
    (requires True)
    (ensures fun res ->
      res == ResultSuccess ==> spec_ast_env_elem_well_formed e.e_semenv x
    )
= ast_env_elem_well_formed' e (spec_array_group_splittable_threshold_of_ast_elem_well_formed_threshold e e_thr) fuel x

[@@"opaque_to_smt"]
let spec_ast_env_elem_well_formed_threshold_empty
  (e: ast_env)
: Tot (spec_ast_env_elem_well_formed_threshold e)
= (fun _ -> false)

[@@ bounded_attr; sem_attr]
let empty_wf_ast_env = {
  we_env = empty_ast_env;
  we_env_wf = spec_ast_env_elem_well_formed_threshold_empty _;
  we_env_wf_prop = ();
}

let spec_array_group_splittable_nil
  (e: semenv)
: Lemma
  (ensures (spec_array_group_splittable e []))
  [SMTPat (spec_array_group_splittable e [])]
= assert_norm (spec_array_group_splittable e []) // would need 1 fuel

let spec_ast_env_elem_well_formed_threshold_fuel
  (#e: ast_env)
  (e_thr: spec_ast_env_elem_well_formed_threshold e)
  (new_name: name e.e_semenv.se_bound)
: Tot Type0
= (fuel: nat {
    ast_env_elem_well_formed e e_thr fuel (e.e_env new_name) == ResultSuccess
  })

let spec_ast_env_elem_well_formed_threshold_fuel_intro
  (fuel: nat)
  (e: ast_env)
  (e_thr: spec_ast_env_elem_well_formed_threshold e)
  (new_name: name e.e_semenv.se_bound)
  (prf: squash (ast_env_elem_well_formed e e_thr fuel (e.e_env new_name) == ResultSuccess))
: Tot (spec_ast_env_elem_well_formed_threshold_fuel e_thr new_name)
= fuel

let spec_ast_env_elem_well_formed_threshold_extend
  (#e: ast_env)
  (e_thr: spec_ast_env_elem_well_formed_threshold e)
  (new_name: name e.e_semenv.se_bound)
  (fuel: spec_ast_env_elem_well_formed_threshold_fuel e_thr new_name)
: Tot (spec_ast_env_elem_well_formed_threshold e)
= (fun i -> if i = new_name then true else e_thr i)

let spec_ast_env_elem_well_formed_included
  (e1 e2: semenv)
  (#s: semenv_elem)
  (x: ast_env_elem e1 s)
: Lemma
  (requires
    semenv_included e1 e2 /\
    spec_ast_env_elem_well_formed e1 x
  )
  (ensures
    spec_ast_env_elem_well_formed e2 x
  )
= match s with
  | SEType _ ->
    let e' : typ = x in
    begin match e' with
    | TArray l -> spec_array_group_splittable_included e1 e2 l
    | TChoice l -> spec_choice_typ_well_formed_included e1 e2 l
    | _ -> ()
    end
  | SEArrayGroup _ -> spec_array_group_splittable_included e1 e2 x
  | SEMapGroup _ -> ()

let spec_ast_env_elem_well_formed_threshold_extend_env
  (#e1: ast_env)
  (e_thr: spec_ast_env_elem_well_formed_threshold e1)
  (e2: ast_env { ast_env_included e1 e2 })
: Tot (spec_ast_env_elem_well_formed_threshold e2)
= (fun i ->
     if e_thr i
     then begin
       spec_ast_env_elem_well_formed_included e1.e_semenv e2.e_semenv (e1.e_env i);
       true
     end
     else false
  )

let wf_ast_env_included
  (e1 e2: wf_ast_env)
: Tot prop
= ast_env_included e1.we_env e2.we_env

[@@"opaque_to_smt"; bounded_attr; sem_attr]
let wf_ast_env_extend_gen
  (e: wf_ast_env)
  (new_name: string { (~ (new_name `name_mem` e.we_env.e_semenv.se_bound)) } )
  (s: semenv_elem)
  (x: ast_env_elem e.we_env.e_semenv s)
  (fuel: spec_ast_env_elem_well_formed_threshold_fuel
    (spec_ast_env_elem_well_formed_threshold_extend_env
      e.we_env_wf
      (ast_env_extend_gen e.we_env new_name s x))
    new_name
  )
: Pure wf_ast_env
    (requires True)
    (ensures fun e' ->
      e'.we_env.e_semenv.se_bound == e.we_env.e_semenv.se_bound `extend_name_env` new_name /\
      wf_ast_env_included e e' /\
      e'.we_env.e_semenv.se_env new_name == s /\
      e'.we_env.e_env new_name == x
    )
= let ae' = ast_env_extend_gen e.we_env new_name s x in
  {
    we_env = ae';
    we_env_wf = spec_ast_env_elem_well_formed_threshold_extend
      (spec_ast_env_elem_well_formed_threshold_extend_env e.we_env_wf ae')
      new_name
      fuel;
    we_env_wf_prop = ();
  }

[@@ bounded_attr; sem_attr]
let wf_ast_env_extend_typ
  (e: wf_ast_env)
  (new_name: string)
  (new_name_fresh: squash (~ (new_name `name_mem` e.we_env.e_semenv.se_bound))) // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  (a: typ)
  (sq: squash (
    typ_bounded e.we_env.e_semenv.se_bound a // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  ))
  (fuel: spec_ast_env_elem_well_formed_threshold_fuel
    (spec_ast_env_elem_well_formed_threshold_extend_env
      e.we_env_wf
      (ast_env_extend_typ e.we_env new_name new_name_fresh a sq))
    (name_intro new_name (ast_env_extend_typ e.we_env new_name new_name_fresh a sq).e_semenv.se_bound new_name_fresh)
  )
: Tot (e': wf_ast_env {
      e'.we_env.e_semenv.se_bound == e.we_env.e_semenv.se_bound `extend_name_env` new_name /\
      wf_ast_env_included e e' /\
      e'.we_env.e_semenv.se_env new_name == SEType (typ_sem e.we_env.e_semenv a)   /\
      e'.we_env.e_env new_name == a
  })
= wf_ast_env_extend_gen e new_name (SEType (typ_sem e.we_env.e_semenv a)) a fuel

[@@ bounded_attr; sem_attr]
let wf_ast_env_extend_array_group
  (e: wf_ast_env)
  (new_name: string) // ideally by SMT
  (new_name_fresh: squash (~ (new_name `name_mem` e.we_env.e_semenv.se_bound))) // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  (a: array_group)
  (sq: squash (
    array_group_bounded e.we_env.e_semenv.se_bound a // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  ))
  (fuel: spec_ast_env_elem_well_formed_threshold_fuel
    (spec_ast_env_elem_well_formed_threshold_extend_env
      e.we_env_wf
      (ast_env_extend_array_group e.we_env new_name new_name_fresh a sq))
    (name_intro new_name (ast_env_extend_array_group e.we_env new_name new_name_fresh a sq).e_semenv.se_bound new_name_fresh)
  )
: Tot (e': wf_ast_env {
      e'.we_env.e_semenv.se_bound == e.we_env.e_semenv.se_bound `extend_name_env` new_name /\
      wf_ast_env_included e e' /\
      e'.we_env.e_semenv.se_env new_name == SEArrayGroup (array_group_sem e.we_env.e_semenv a) /\
      e'.we_env.e_env new_name == a
  })
= wf_ast_env_extend_gen e new_name (SEArrayGroup (array_group_sem e.we_env.e_semenv a)) a fuel

[@@ bounded_attr; sem_attr]
let wf_ast_env_extend_map_group
  (e: wf_ast_env)
  (new_name: string) // ideally by SMT
  (new_name_fresh: squash (~ (new_name `name_mem` e.we_env.e_semenv.se_bound))) // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  (a: map_group)
  (sq: squash (
    map_group_bounded e.we_env.e_semenv.se_bound a // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  ))
  (fuel: spec_ast_env_elem_well_formed_threshold_fuel
    (spec_ast_env_elem_well_formed_threshold_extend_env
      e.we_env_wf
      (ast_env_extend_map_group e.we_env new_name new_name_fresh a sq))
    (name_intro new_name (ast_env_extend_map_group e.we_env new_name new_name_fresh a sq).e_semenv.se_bound new_name_fresh)
  )
: Tot (e': wf_ast_env {
      e'.we_env.e_semenv.se_bound == e.we_env.e_semenv.se_bound `extend_name_env` new_name /\
      wf_ast_env_included e e' /\
      e'.we_env.e_semenv.se_env new_name == SEMapGroup (map_group_sem e.we_env.e_semenv a) /\
      e'.we_env.e_env new_name == a
  })
= wf_ast_env_extend_gen e new_name (SEMapGroup (map_group_sem e.we_env.e_semenv a)) a fuel

let solve_bounded () : FStar.Tactics.Tac unit =
  FStar.Tactics.norm [delta_attr [`%bounded_attr]; iota; zeta; primops; nbe];
  FStar.Tactics.smt ()

exception ExceptionOutOfFuel

let solve_spec_ast_env_elem_well_formed () : FStar.Tactics.Tac unit =
  let rec aux (n: nat) : FStar.Tactics.Tac unit =
    FStar.Tactics.try_with
    (fun _ ->
      FStar.Tactics.print ("solve_spec_ast_env_elem_well_formed with fuel " ^ string_of_int n ^ "\n");
      FStar.Tactics.apply (FStar.Tactics.mk_app (`spec_ast_env_elem_well_formed_threshold_fuel_intro) [quote n, FStar.Tactics.Q_Explicit]);
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.try_with
        (fun _ ->
          FStar.Tactics.trefl ()
        )
        (fun e -> 
          let g = FStar.Tactics.cur_goal () in
          FStar.Tactics.print ("solve_spec_ast_env_elem_well_formed Failure: " ^ FStar.Tactics.term_to_string g ^ "\n");
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
  FStar.Tactics.norm [delta_attr [`%sem_attr]; iota; zeta; primops; nbe];
  FStar.Tactics.smt ()
