module CDDL.Interpreter.AST
module Spec = CDDL.Spec
module U64 = FStar.UInt64

irreducible let bounded_attr : unit = ()

irreducible let sem_attr : unit = ()

let char_is_ascii (c: FStar.Char.char) : Tot bool =
  FStar.UInt32.lt (FStar.Char.u32_of_char c) 256ul

let string_is_ascii (s: string) : Tot bool =
  List.Tot.for_all char_is_ascii (FStar.String.list_of_string s)

let ascii_string : eqtype = (s: string { string_is_ascii s })

unfold
let mk_ascii_string (s: string) (prf: squash (string_is_ascii s)) : Tot ascii_string = s

let test_ascii_string: ascii_string = mk_ascii_string "hello" (_ by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ()))

[@@sem_attr]
type literal =
| LSimple of CBOR.Spec.simple_value
| LInt: (ty: CBOR.Spec.major_type_uint64_or_neg_int64) -> (v: U64.t) -> literal
| LString: (ty: CBOR.Spec.major_type_byte_string_or_text_string) -> (s: ascii_string { FStar.String.length s < pow2 64 }) -> literal // FIXME: support utf8

[@@sem_attr]
let cddl_major_type_uint64 : CBOR.Spec.major_type_uint64_or_neg_int64 =
  (_ by (FStar.Tactics.exact (FStar.Tactics.norm_term [delta] (`CBOR.Spec.cbor_major_type_uint64))))

[@@sem_attr]
let cddl_major_type_neg_int64 : CBOR.Spec.major_type_uint64_or_neg_int64 =
  (_ by (FStar.Tactics.exact (FStar.Tactics.norm_term [delta] (`CBOR.Spec.cbor_major_type_neg_int64))))

[@@sem_attr]
let cddl_major_type_byte_string : CBOR.Spec.major_type_byte_string_or_text_string =
  (_ by (FStar.Tactics.exact (FStar.Tactics.norm_term [delta] (`CBOR.Spec.cbor_major_type_byte_string))))

[@@sem_attr]
let cddl_major_type_text_string : CBOR.Spec.major_type_byte_string_or_text_string =
  (_ by (FStar.Tactics.exact (FStar.Tactics.norm_term [delta] (`CBOR.Spec.cbor_major_type_text_string))))

[@@sem_attr]
let literal_eq (l1 l2: literal) : Pure bool
  (requires True)
  (ensures (fun b -> b == true <==> l1 == l2))
= match l1, l2 with
  | LSimple v1, LSimple v2 -> v1 = v2
  | LInt ty1 v1, LInt ty2 v2 ->
    if ty1 = ty2
    then v1 = v2
    else false
  | LString ty1 s1, LString ty2 s2 ->
    if ty1 = ty2
    then s1 = s2
    else false
  | _ -> false

type elem_typ =
| ELiteral of literal
| EBool
| EByteString
| ETextString

type name_env_elem =
| NType
| NArrayGroup
| NMapGroup

type group (kind: name_env_elem) =
| GDef of string
| GArrayElem: squash (kind == NArrayGroup) -> typ -> group kind
| GMapElem: squash (kind == NMapGroup) -> (cut: bool) -> (key: typ) -> (value: typ) -> group kind
| GAlwaysFalse
| GNop
| GZeroOrOne of group kind
| GZeroOrMore of group kind
| GOneOrMore of group kind
| GConcat: group kind -> group kind -> group kind
| GChoice: group kind -> group kind -> group kind

and typ =
| TElem of elem_typ
| TDef of string
| TArray of group NArrayGroup
| TMap of group NMapGroup
| TChoice: typ -> typ -> typ

type name_env = (string -> Tot (option name_env_elem))

[@@ bounded_attr]
let name_mem (s: string) (e: name_env) : Tot bool = Some? (e s)

let name (e: name_env) : eqtype = (s: string { name_mem s e })

let typ_name (e: name_env) : eqtype = (s: string { e s == Some NType })
let array_group_name (e: name_env) : eqtype = (s: string { e s == Some NArrayGroup })
let map_group_name (e: name_env) : eqtype = (s: string { e s == Some NMapGroup })

[@@ bounded_attr; sem_attr]
let name_intro (s: string) (e: name_env) (sq: squash (name_mem s e)) : Tot (name e) =
  s

[@@bounded_attr]
let empty_name_env (_: string) : Tot (option name_env_elem) = None

[@@"opaque_to_smt"] irreducible
let name_empty_elim (t: Type) (x: name empty_name_env) : Tot t = false_elim ()

[@@bounded_attr]
let extend_name_env (e: name_env) (new_name: string) (elem: name_env_elem) (s: string) : Tot (option name_env_elem) =
  if s = new_name then Some elem else e s

let name_env_included (s1 s2: name_env) : Tot prop =
  (forall (i: name s1) . s2 i == s1 i)

[@@bounded_attr; sem_attr]
let rec group_bounded
  (kind: name_env_elem)
  (env: name_env)
  (g: group kind)
: Tot bool
  (decreases g)
= match g with
  | GDef d -> env d = Some kind
  | GMapElem _ _ key value -> typ_bounded env key && typ_bounded env value
  | GArrayElem _ t -> typ_bounded env t
  | GZeroOrMore g'
  | GZeroOrOne g'
  | GOneOrMore g'
  -> group_bounded kind env g'
  | GConcat g1 g2
  | GChoice g1 g2
  -> group_bounded kind env g1 &&
    group_bounded kind env g2
  | GAlwaysFalse
  | GNop -> true

and typ_bounded
  (env: name_env)
  (t: typ)
: Tot bool
  (decreases t)
= match t with
  | TElem _ -> true
  | TDef s -> env s = Some NType
  | TArray g -> group_bounded NArrayGroup env g
  | TMap g -> group_bounded NMapGroup env g
  | TChoice t1 t2 ->
    typ_bounded env t1 &&
    typ_bounded env t2

let rec group_bounded_incr
  (kind: name_env_elem)
  (env env': name_env)
  (g: group kind)
: Lemma
  (requires (
    name_env_included env env' /\
    group_bounded kind env g
  ))
  (ensures (
    group_bounded kind env' g
  ))
  (decreases g)
  [SMTPatOr [
    [SMTPat (name_env_included env env'); SMTPat (group_bounded kind env g)];
    [SMTPat (name_env_included env env'); SMTPat (group_bounded kind env' g)];
  ]]
= match g with
  | GDef _ -> ()
  | GArrayElem _ t -> typ_bounded_incr env env' t
  | GMapElem _ _ key value -> typ_bounded_incr env env' key; typ_bounded_incr env env' value
  | GZeroOrMore g'
  | GZeroOrOne g'
  | GOneOrMore g'
  -> group_bounded_incr kind env env' g'
  | GConcat g1 g2
  | GChoice g1 g2
  -> group_bounded_incr kind env env' g1; group_bounded_incr kind env env' g2
  | GAlwaysFalse
  | GNop -> ()

and typ_bounded_incr
  (env env': name_env)
  (t: typ)
: Lemma
  (requires (
    name_env_included env env' /\
    typ_bounded env t
  ))
  (ensures (
    typ_bounded env' t
  ))
  (decreases t)
  [SMTPatOr [
    [SMTPat (name_env_included env env'); SMTPat (typ_bounded env t)];
    [SMTPat (name_env_included env env'); SMTPat (typ_bounded env' t)];
  ]]
= match t with
  | TElem _
  | TDef _
  -> ()
  | TArray g -> group_bounded_incr NArrayGroup env env' g
  | TMap g -> group_bounded_incr NMapGroup env env' g
  | TChoice t1 t2 -> typ_bounded_incr env env' t1; typ_bounded_incr env env' t2

module MapSpec = CDDL.Spec.MapGroupGen

[@@ bounded_attr; sem_attr]
let sem_env_elem
  (kind: name_env_elem)
: Tot Type
= match kind with
  | NType -> Spec.typ
  | NArrayGroup -> Spec.array_group3 None
  | NMapGroup -> MapSpec.map_group

let se_map_group_is_productive_codom
  (kind: name_env_elem)
  (se: sem_env_elem kind)
: eqtype
= (x: bool { x == true ==> (kind == NMapGroup /\ MapSpec.map_group_is_productive se) })

[@@erasable]
noeq
type se_map_group_metadata
  (kind: name_env_elem)
  (se: sem_env_elem kind)
= {
    g_footprint: Spec.typ;
    g_restrict: MapSpec.map_group;
    g_restrict_footprint: Spec.typ;
    g_is_filter: bool;
    g_prf: squash (
      kind == NMapGroup /\
      MapSpec.map_group_footprint se g_footprint /\
      MapSpec.restrict_map_group se g_restrict /\
      MapSpec.map_group_footprint g_restrict g_restrict_footprint /\
      Spec.typ_included g_restrict_footprint g_footprint /\
      (g_is_filter == true ==> (exists f . se == MapSpec.map_group_filter f))
    );
  }

let se_map_group_metadata_codom kind se = option (se_map_group_metadata kind se)

[@@ bounded_attr; sem_attr]
noeq
type sem_env = {
  se_bound: name_env;
  se_env: ((n: name se_bound) -> sem_env_elem (Some?.v (se_bound n)));
  se_map_group_is_productive: (n: name se_bound) -> se_map_group_is_productive_codom (Some?.v (se_bound n)) (se_env n);
  se_map_group_metadata: (n: name se_bound) -> se_map_group_metadata_codom (Some?.v (se_bound n)) (se_env n);
}

[@@"opaque_to_smt"] irreducible // because of false_elim
let se_env_empty
  (n: name empty_name_env)
: Tot (sem_env_elem (Some?.v (empty_name_env n)))
= false_elim ()

[@@"opaque_to_smt"] irreducible // because of false_elim
let se_map_group_is_productive_empty
  (n: name empty_name_env)
: Tot (se_map_group_is_productive_codom (Some?.v (empty_name_env n)) (se_env_empty n))
= false_elim ()

[@@"opaque_to_smt"] irreducible // because of false_elim
let se_map_group_metadata_empty
  (n: name empty_name_env)
: Tot (se_map_group_metadata_codom (Some?.v (empty_name_env n)) (se_env_empty n))
= false_elim ()

[@@ bounded_attr; sem_attr]
let empty_sem_env = {
  se_bound = empty_name_env;
  se_env = se_env_empty;
  se_map_group_is_productive = se_map_group_is_productive_empty;
  se_map_group_metadata = se_map_group_metadata_empty;
}

let sem_env_included (s1 s2: sem_env) : Tot prop =
  name_env_included s1.se_bound s2.se_bound /\
  (forall (i: name s1.se_bound) . s1.se_env i == s2.se_env i) /\
  (forall (i: name s1.se_bound) . s1.se_map_group_is_productive i ==> s2.se_map_group_is_productive i) /\
  (forall (i: name s1.se_bound) . let fp = s1.se_map_group_metadata i in Some? fp ==> fp == s2.se_map_group_metadata i)

let sem_env_included_trans (s1 s2 s3: sem_env) : Lemma
  (requires (sem_env_included s1 s2 /\ sem_env_included s2 s3))
  (ensures (sem_env_included s1 s3))
  [SMTPat (sem_env_included s1 s3); SMTPat (sem_env_included s1 s2)]
= ()

[@@"opaque_to_smt"; bounded_attr; sem_attr]
let sem_env_extend_gen
  (se: sem_env)
  (new_name: string)
  (nelem: name_env_elem)
  (a: sem_env_elem nelem)
: Pure sem_env
    (requires
      (~ (name_mem new_name se.se_bound))
    )
    (ensures fun se' ->
      se'.se_bound == extend_name_env se.se_bound new_name nelem /\
      sem_env_included se se' /\
      se'.se_env new_name == a
    )
= let se_bound' = extend_name_env se.se_bound new_name nelem in
  {
    se_bound = se_bound';
    se_env = (fun (i: name se_bound') -> if i = new_name then a else se.se_env i);
    se_map_group_is_productive = (fun (i: name se_bound') -> if i = new_name then false else se.se_map_group_is_productive i);
    se_map_group_metadata = (fun (i: name se_bound') -> if i = new_name then None else se.se_map_group_metadata i);
  }

[@@"opaque_to_smt"; bounded_attr; sem_attr]
let sem_env_set_map_group_is_productive
  (se: sem_env)
  (n: map_group_name se.se_bound)
: Pure sem_env
    (requires MapSpec.map_group_is_productive (se.se_env n))
    (ensures fun se' ->
      se'.se_bound == se.se_bound /\
      sem_env_included se se' /\
      se'.se_map_group_is_productive n == true
    )
= {
    se with
    se_map_group_is_productive = (fun (i: name se.se_bound) -> if i = n then true else se.se_map_group_is_productive i);
  }

[@@"opaque_to_smt"; bounded_attr; sem_attr]
let sem_env_set_map_group_metadata
  (se: sem_env)
  (n: map_group_name se.se_bound)
  (fp: se_map_group_metadata NMapGroup (se.se_env n))
: Pure sem_env
    (requires None? (se.se_map_group_metadata n))
    (ensures fun se' ->
      se'.se_bound == se.se_bound /\
      sem_env_included se se' /\
      se'.se_map_group_metadata n == Some fp
    )
= {
    se with
    se_map_group_metadata = (fun (i: name se.se_bound) -> if i = n then Some fp else se.se_map_group_metadata i);
  }

let byte_list_of_char_list
  (l: list FStar.Char.char)
: Tot (list FStar.UInt8.t)
= List.Tot.map FStar.Int.Cast.uint32_to_uint8 (List.Tot.map FStar.Char.u32_of_char l)

let char_list_of_byte_list
  (l: list FStar.UInt8.t)
: Tot (list FStar.Char.char)
= List.Tot.map FStar.Char.char_of_u32 (List.Tot.map FStar.Int.Cast.uint8_to_uint32 l)

let rec char_list_of_byte_list_is_ascii
  (l: list FStar.UInt8.t)
: Lemma
  (List.Tot.for_all char_is_ascii (char_list_of_byte_list l))
  [SMTPat (char_list_of_byte_list l)]
= match l with 
  | [] -> ()
  | _ :: q -> char_list_of_byte_list_is_ascii q

let rec char_list_of_byte_list_of_char_list
  (l: list FStar.Char.char)
: Lemma
  (requires List.Tot.for_all char_is_ascii l)
  (ensures char_list_of_byte_list (byte_list_of_char_list l) == l)
  [SMTPat (byte_list_of_char_list l)]
= match l with
  | [] -> ()
  | a :: q ->
    let a' = FStar.Char.u32_of_char a in
    FStar.Math.Lemmas.small_mod (FStar.UInt32.v a') 256;
    assert (FStar.Int.Cast.uint8_to_uint32 (FStar.Int.Cast.uint32_to_uint8 a') == a');
    char_list_of_byte_list_of_char_list q

let byte_seq_of_ascii_string
  (s: ascii_string)
: Tot (Seq.seq FStar.UInt8.t)
= Seq.seq_of_list (byte_list_of_char_list (FStar.String.list_of_string s))

let ascii_string_of_byte_seq
  (s: Seq.seq FStar.UInt8.t)
: Tot ascii_string
= let l = char_list_of_byte_list (Seq.seq_to_list s) in
  FStar.String.list_of_string_of_list l;
  FStar.String.string_of_list l

let ascii_string_of_byte_seq_of_ascii_string
  (s: ascii_string)
: Lemma
  (ascii_string_of_byte_seq (byte_seq_of_ascii_string s) == s)
  [SMTPat (byte_seq_of_ascii_string s)]
= FStar.String.string_of_list_of_string s

[@@ sem_attr ]
let eval_literal
  (l: literal)
: Tot CBOR.Spec.raw_data_item
= match l with
  | LSimple v -> CBOR.Spec.Simple v
  | LInt ty v -> CBOR.Spec.Int64 ty v
  | LString ty s -> CBOR.Spec.String ty (byte_seq_of_ascii_string s)

let spec_type_of_literal
  (l: literal)
: Tot Spec.typ
= Spec.t_literal (eval_literal l)

[@@ sem_attr ]
let elem_typ_sem
  (t: elem_typ)
: Tot Spec.typ
= match t with
  | ELiteral l -> spec_type_of_literal l
  | EBool -> Spec.t_bool
  | EByteString -> Spec.bstr
  | ETextString -> Spec.tstr

[@@ sem_attr ]
let rec array_group_sem
  (env: sem_env)
  (g: group NArrayGroup)
: Pure (Spec.array_group3 None)
    (requires group_bounded NArrayGroup env.se_bound g)
    (ensures fun _ -> True)
= match g with
  | GDef d -> env.se_env d
  | GArrayElem _ t -> Spec.array_group3_item (typ_sem env t)
  | GAlwaysFalse -> Spec.array_group3_always_false
  | GNop -> Spec.array_group3_empty
  | GZeroOrOne g -> Spec.array_group3_zero_or_one (array_group_sem env g)
  | GZeroOrMore g -> Spec.array_group3_zero_or_more (array_group_sem env g)
  | GOneOrMore g -> Spec.array_group3_one_or_more (array_group_sem env g)
  | GConcat g1 g2 -> Spec.array_group3_concat (array_group_sem env g1) (array_group_sem env g2)
  | GChoice g1 g2 -> Spec.array_group3_choice (array_group_sem env g1) (array_group_sem env g2)

and map_group_sem
  (env: sem_env)
  (g: group NMapGroup)
: Pure (MapSpec.map_group)
    (requires group_bounded NMapGroup env.se_bound g)
    (ensures fun _ -> True)
= match g with
  | GDef d -> env.se_env d
  | GMapElem _ cut key value -> MapSpec.map_group_match_item cut (typ_sem env key) (typ_sem env value)
  | GAlwaysFalse -> MapSpec.map_group_always_false
  | GNop -> MapSpec.map_group_nop
  | GZeroOrOne g -> MapSpec.map_group_zero_or_one (map_group_sem env g)
  | GZeroOrMore g -> MapSpec.map_group_zero_or_more (map_group_sem env g)
  | GOneOrMore g -> MapSpec.map_group_one_or_more (map_group_sem env g)
  | GConcat g1 g2 -> MapSpec.map_group_concat (map_group_sem env g1) (map_group_sem env g2)
  | GChoice g1 g2 -> MapSpec.map_group_choice (map_group_sem env g1) (map_group_sem env g2)

and typ_sem
  (env: sem_env)
  (x: typ)
: Pure Spec.typ
    (requires typ_bounded env.se_bound x)
    (ensures (fun _ -> True))
= match x with
  | TElem t -> elem_typ_sem t
  | TDef s -> env.se_env s
  | TArray g ->
    Spec.t_array3 (array_group_sem env g)
  | TMap g ->
    MapSpec.t_map (map_group_sem env g)
  | TChoice t1 t2 ->
    Spec.t_choice
      (typ_sem env t1)
      (typ_sem env t2)

let rec array_group_sem_incr
  (env env': sem_env)
  (g: group NArrayGroup)
: Lemma
  (requires (
    sem_env_included env env' /\
    group_bounded NArrayGroup env.se_bound g
  ))
  (ensures (
    group_bounded NArrayGroup env.se_bound g /\
    group_bounded NArrayGroup env'.se_bound g /\
    array_group_sem env g == array_group_sem env' g
  ))
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (array_group_sem env g)];
    [SMTPat (sem_env_included env env'); SMTPat (array_group_sem env' g)];
  ]]
= match g with
  | GAlwaysFalse
  | GNop
  | GDef _ -> ()
  | GArrayElem _ t -> typ_sem_incr env env' t
  | GZeroOrOne g
  | GZeroOrMore g
  | GOneOrMore g
  -> array_group_sem_incr env env' g
  | GConcat g1 g2
  | GChoice g1 g2
  -> array_group_sem_incr env env' g1;
  array_group_sem_incr env env' g2

and map_group_sem_incr
  (env env': sem_env)
  (g: group NMapGroup)
: Lemma
  (requires (
    sem_env_included env env' /\
    group_bounded NMapGroup env.se_bound g
  ))
  (ensures (
    group_bounded NMapGroup env.se_bound g /\
    group_bounded NMapGroup env'.se_bound g /\
    map_group_sem env g == map_group_sem env' g
  ))
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (map_group_sem env g)];
    [SMTPat (sem_env_included env env'); SMTPat (map_group_sem env' g)];
  ]]
= match g with
  | GAlwaysFalse
  | GNop
  | GDef _ -> ()
  | GMapElem _ _ key value ->
    typ_sem_incr env env' key;
    typ_sem_incr env env' value
  | GZeroOrOne g
  | GZeroOrMore g
  | GOneOrMore g
  -> map_group_sem_incr env env' g
  | GConcat g1 g2
  | GChoice g1 g2
  -> map_group_sem_incr env env' g1;
    map_group_sem_incr env env' g2

and typ_sem_incr
  (env env': sem_env)
  (x: typ)
: Lemma
  (requires (
    sem_env_included env env' /\
    typ_bounded env.se_bound x
  ))
  (ensures (
    typ_bounded env.se_bound x /\
    typ_bounded env'.se_bound x /\
    typ_sem env x == typ_sem env' x
  ))
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (typ_sem env x)];
    [SMTPat (sem_env_included env env'); SMTPat (typ_sem env' x)];
  ]]
= match x with
  | TElem _
  | TDef _
  -> ()
  | TArray g ->
    array_group_sem_incr env env' g
  | TMap g ->
    map_group_sem_incr env env' g
  | TChoice t1 t2 ->
    typ_sem_incr env env' t1;
    typ_sem_incr env env' t2

(* Rewriting *)

[@@ sem_attr]
let rec map_group_is_productive
  (env: sem_env)
  (g: group NMapGroup)
: Pure bool
    (requires group_bounded NMapGroup env.se_bound g)
    (ensures (fun _ -> True))
= match g with
  | GOneOrMore g' -> map_group_is_productive env g'
  | GMapElem _ _ _ _ -> true
  | GAlwaysFalse
  | GNop
  | GZeroOrOne _
  | GZeroOrMore _ -> false
  | GChoice g1 g2 -> map_group_is_productive env g1 && map_group_is_productive env g2
  | GConcat g1 g2 -> map_group_is_productive env g1 || map_group_is_productive env g2
  | GDef n -> env.se_map_group_is_productive n

[@@ sem_attr]
let rec map_group_is_productive_incr
  (env env': sem_env)
  (g: group NMapGroup)
: Lemma
  (requires sem_env_included env env' /\
    group_bounded NMapGroup env.se_bound g /\
    map_group_is_productive env g
  )
  (ensures
      group_bounded NMapGroup env'.se_bound g /\
      map_group_is_productive env' g
  )
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (map_group_is_productive env g)];
    [SMTPat (sem_env_included env env'); SMTPat (map_group_is_productive env' g)];
  ]]
= match g with
  | GOneOrMore g' -> map_group_is_productive_incr env env' g'
  | GConcat g1 g2 ->
    if map_group_is_productive env g1
    then map_group_is_productive_incr env env' g1
    else map_group_is_productive_incr env env' g2
  | GChoice g1 g2 ->
    map_group_is_productive_incr env env' g1;
    map_group_is_productive_incr env env' g2
  | _ -> ()

let rec map_group_is_productive_correct
  (env: sem_env)
  (g: group NMapGroup)
: Lemma
  (requires (
    group_bounded NMapGroup env.se_bound g /\
    map_group_is_productive env g == true
  ))
  (ensures (
    MapSpec.map_group_is_productive (map_group_sem env g)
  ))
= match g with
  | GOneOrMore g' ->
    map_group_is_productive_correct env g'
  | GChoice g1 g2 ->
    map_group_is_productive_correct env g1;
    map_group_is_productive_correct env g2
  | GConcat g1 g2 ->
    if map_group_is_productive env g1
    then map_group_is_productive_correct env g1
    else map_group_is_productive_correct env g2
  | _ -> ()

[@@ sem_attr]
let rec rewrite_typ
  (env: sem_env)
  (fuel: nat)
  (t: typ)
: Pure typ
  (requires typ_bounded env.se_bound t)
  (ensures fun t' -> typ_bounded env.se_bound t')
  (decreases fuel)
= if fuel = 0
  then t
  else let fuel' : nat = fuel - 1 in
  match t with
  | TChoice (TChoice t1 t2) t3 -> rewrite_typ env fuel' (TChoice t1 (TChoice t2 t3))
  | TChoice t1 t2 ->
    let t' = TChoice (rewrite_typ env fuel' t1) (rewrite_typ env fuel' t2) in
    if t' = t
    then t'
    else rewrite_typ env fuel' t'
  | TArray g -> TArray (rewrite_group env fuel' NArrayGroup g)
  | TMap g -> TMap (rewrite_group env fuel' NMapGroup g)
  | _ -> t

and rewrite_group
  (env: sem_env)
  (fuel: nat)
  (kind: name_env_elem)
  (g: group kind)
: Pure (group kind)
  (requires group_bounded kind env.se_bound g)
  (ensures fun g' -> group_bounded kind env.se_bound g')
  (decreases fuel)
= if fuel = 0
  then g
  else let fuel' : nat = fuel - 1 in
  match g with
  | GConcat (GConcat t1 t2) t3 -> rewrite_group env fuel' kind (GConcat t1 (GConcat t2 t3))
  | GConcat t1 t2 ->
    let g' = GConcat (rewrite_group env fuel' kind t1) (rewrite_group env fuel' kind t2) in
    if g' = g
    then g'
    else rewrite_group env fuel' kind g'
  | GChoice (GChoice t1 t2) t3 -> rewrite_group env fuel' kind (GChoice t1 (GChoice t2 t3))
  | GChoice t1 t2 ->
    let g' = GChoice (rewrite_group env fuel' kind t1) (rewrite_group env fuel' kind t2) in
    if g' = g
    then g'
    else rewrite_group env fuel' kind g'
  | GZeroOrMore (GMapElem sq cut (TElem (ELiteral key)) value) ->
    rewrite_group env fuel' kind (GZeroOrOne (GMapElem sq cut (TElem (ELiteral key)) value))
  | GZeroOrMore (GChoice (GMapElem sq cut key value) g') ->
    if map_group_is_productive env g'
    then rewrite_group env fuel' kind (GConcat (GZeroOrMore (GMapElem sq cut key value)) (GZeroOrMore g'))
    else g
  | GZeroOrMore g1 -> 
    let g' = GZeroOrMore (rewrite_group env fuel' kind g1) in
    if g' = g
    then g'
    else rewrite_group env fuel' kind g'
  | GZeroOrOne g -> GZeroOrOne (rewrite_group env fuel' kind g)
  | GOneOrMore g -> GOneOrMore (rewrite_group env fuel' kind g)
  | GArrayElem sq ty -> GArrayElem sq (rewrite_typ env fuel' ty)
  | GMapElem sq cut key value -> GMapElem sq cut (rewrite_typ env fuel' key) (rewrite_typ env fuel' value)
  | GDef n -> GDef n
  | GAlwaysFalse -> GAlwaysFalse
  | GNop -> GNop

#restart-solver
let rec rewrite_typ_correct
  (env: sem_env)
  (fuel: nat)
  (t: typ)
: Lemma
  (requires (
    typ_bounded env.se_bound t
  ))
  (ensures (
    let t' = rewrite_typ env fuel t in
    typ_bounded env.se_bound t' /\
    Spec.typ_equiv (typ_sem env t) (typ_sem env t')
  ))
  (decreases fuel)
= if fuel = 0
  then ()
  else let fuel' : nat = fuel - 1 in
  match t with
  | TChoice (TChoice t1 t2) t3 ->
    rewrite_typ_correct env fuel' (TChoice t1 (TChoice t2 t3))
  | TChoice t1 t2 ->
    rewrite_typ_correct env fuel' t1;
    rewrite_typ_correct env fuel' t2;
    rewrite_typ_correct env fuel' (TChoice (rewrite_typ env fuel' t1) (rewrite_typ env fuel' t2))
  | TArray g ->
    rewrite_group_correct env fuel' g
  | TMap g ->
    rewrite_group_correct env fuel' g
  | _ -> ()

and rewrite_group_correct
  (env: sem_env)
  (fuel: nat)
  (#kind: name_env_elem)
  (t: group kind)
: Lemma
  (requires (
    group_bounded kind env.se_bound t
  ))
  (ensures (
    let t' = rewrite_group env fuel kind t in
    group_bounded kind env.se_bound t' /\
    begin match kind with
    | NArrayGroup -> Spec.array_group3_equiv (array_group_sem env t) (array_group_sem env t')
    | NMapGroup -> map_group_sem env t == map_group_sem env t'
    | _ -> True
    end
  ))
  (decreases fuel)
= if fuel = 0
  then ()
  else let fuel' : nat = fuel - 1 in
  match t with
  | GConcat (GConcat t1 t2) t3 ->
    rewrite_group_correct env fuel' (GConcat t1 (GConcat t2 t3))
  | GConcat t1 t2 ->
    let t1' = rewrite_group env fuel' kind t1 in
    let t2' = rewrite_group env fuel' kind t2 in
    rewrite_group_correct env fuel' t1;
    rewrite_group_correct env fuel' t2;
    rewrite_group_correct env fuel' (GConcat t1' t2');
    begin match kind with
    | NArrayGroup -> Spec.array_group3_concat_equiv (array_group_sem env t1) (array_group_sem env t1') (array_group_sem env t2) (array_group_sem env t2')
    | _ -> ()
    end
  | GChoice (GChoice t1 t2) t3 ->
    rewrite_group_correct env fuel' (GChoice t1 (GChoice t2 t3))
  | GChoice t1 t2 ->
    let t1' = rewrite_group env fuel' kind t1 in
    let t2' = rewrite_group env fuel' kind t2 in
    rewrite_group_correct env fuel' t1;
    rewrite_group_correct env fuel' t2;
    rewrite_group_correct env fuel' (GChoice t1' t2')
  | GZeroOrMore (GMapElem sq cut (TElem (ELiteral key)) value) ->
    MapSpec.map_group_zero_or_more_map_group_match_item_for cut (eval_literal key) (typ_sem env value);
    rewrite_group_correct env fuel' (GZeroOrOne (GMapElem sq cut (TElem (ELiteral key)) value))
  | GZeroOrMore (GChoice (GMapElem sq cut key value) g') ->
    if map_group_is_productive env g'
    then begin
      map_group_is_productive_correct env g';
      MapSpec.map_group_zero_or_more_choice (MapSpec.map_group_match_item cut (typ_sem env key) (typ_sem env value)) (map_group_sem env g');
      rewrite_group_correct env fuel' (GConcat (GZeroOrMore (GMapElem sq cut key value)) (GZeroOrMore g'))
    end
  | GZeroOrOne g1 ->
    rewrite_group_correct env fuel' g1
  | GZeroOrMore g1 ->
    rewrite_group_correct env fuel' g1;
    let g2 = rewrite_group env fuel' kind g1 in
    rewrite_group_correct env fuel' (GZeroOrMore g2);
    begin match kind with
    | NArrayGroup -> Spec.array_group3_zero_or_more_equiv (array_group_sem env g1) (array_group_sem env g2)
    | _ -> ()
    end
  | GOneOrMore g1 ->
    rewrite_group_correct env fuel' g1;
    let g2 = rewrite_group env fuel' kind g1 in
    rewrite_group_correct env fuel' (GOneOrMore g2);
    begin match kind with
    | NArrayGroup -> Spec.array_group3_zero_or_more_equiv (array_group_sem env g1) (array_group_sem env g2)
    | _ -> ()
    end
  | GArrayElem sq ty ->
    rewrite_typ_correct env fuel' ty;
    Spec.array_group3_item_equiv (typ_sem env ty) (typ_sem env (rewrite_typ env fuel' ty))
  | GMapElem sq cut key value ->
    rewrite_typ_correct env fuel' key;
    rewrite_typ_correct env fuel' value;
    MapSpec.map_group_match_item_ext cut (typ_sem env key) (typ_sem env value) (typ_sem env (rewrite_typ env fuel' key)) (typ_sem env (rewrite_typ env fuel' value))
  | GAlwaysFalse
  | GNop
  | GDef _ -> ()

let rec spec_map_group_footprint
  (env: sem_env)
  (g: group NMapGroup)
: Pure (option Spec.typ)
    (requires group_bounded NMapGroup env.se_bound g)
    (ensures fun res -> match res with
    | None -> True
    | Some ty -> MapSpec.map_group_footprint (map_group_sem env g) ty)
= match g with
  | GDef n ->
    begin match env.se_map_group_metadata n with
    | None -> None
    | Some md -> Some md.g_footprint
    end
  | GMapElem _ cut (TElem (ELiteral key)) value
  -> MapSpec.map_group_footprint_match_item_for cut (eval_literal key) (typ_sem env value);
    Some (Spec.t_literal (eval_literal key))
  | GZeroOrMore (GMapElem _ false key _) // TODO: extend to GOneOrMore
  -> Some (typ_sem env key)
  | GZeroOrOne g -> spec_map_group_footprint env g
  | GChoice g1 g2
  | GConcat g1 g2 ->
    begin match spec_map_group_footprint env g1, spec_map_group_footprint env g2 with
    | Some ty1, Some ty2 -> Some (ty1 `Spec.t_choice` ty2)
    | _ -> None
    end
  | GAlwaysFalse
  | GNop
  | GMapElem _ _ _ _
  | GZeroOrMore _
  | GOneOrMore _ -> None

let rec spec_map_group_footprint_incr
  (env env': sem_env)
  (g: group NMapGroup)
: Lemma
  (requires
    sem_env_included env env' /\
    group_bounded NMapGroup env.se_bound g /\
    Some? (spec_map_group_footprint env g)
  )
  (ensures
    group_bounded NMapGroup env'.se_bound g /\
    spec_map_group_footprint env' g == spec_map_group_footprint env g
  )
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (spec_map_group_footprint env g)];
    [SMTPat (sem_env_included env env'); SMTPat (spec_map_group_footprint env' g)];
  ]]
= match g with
  | GZeroOrOne g ->
    spec_map_group_footprint_incr env env' g
  | GChoice g1 g2
  | GConcat g1 g2 ->
    spec_map_group_footprint_incr env env' g1;
    spec_map_group_footprint_incr env env' g2
  | _ -> ()

[@@ sem_attr]
noeq
type ast0_wf_typ
: typ -> Type
= 
| WfTArray:
  (g: group NArrayGroup) ->
  (s: ast0_wf_array_group g) ->
  ast0_wf_typ (TArray g)
| WfTMap:
  (g: group NMapGroup) ->
  (g1 : group NMapGroup) ->
  (s1: ast0_restrict_map_group Spec.t_always_false g g1) ->
  (g2: group NMapGroup) ->
  (s2: ast0_wf_map_group g2) ->
  ast0_wf_typ (TMap g)
| WfTChoice:
  (t1: typ) ->
  (t2: typ) ->
  (s1: ast0_wf_typ t1) ->
  (s2: ast0_wf_typ t2) ->
  ast0_wf_typ (TChoice t1 t2)
| WfTElem:
  (e: elem_typ) ->
  ast0_wf_typ (TElem e)
| WfTDef:
  (n: string) ->
  ast0_wf_typ (TDef n)

and ast0_wf_array_group
: group NArrayGroup -> Type
= 
| WfAElem:
  ty: typ ->
  prf: ast0_wf_typ ty ->
  ast0_wf_array_group (GArrayElem () ty)
| WfAZeroOrOne:
  g: group NArrayGroup ->
  s: ast0_wf_array_group g ->
  ast0_wf_array_group (GZeroOrOne g)
| WfAZeroOrOneOrMore:
  g: group NArrayGroup ->
  s: ast0_wf_array_group g ->
  g': group NArrayGroup { g' == GZeroOrMore g \/ g' == GOneOrMore g } ->
  ast0_wf_array_group g'
| WfAConcat:
  g1: group NArrayGroup ->
  g2: group NArrayGroup ->
  s1: ast0_wf_array_group g1 ->
  s2: ast0_wf_array_group g2 ->
  ast0_wf_array_group (GConcat g1 g2)
| WfAChoice:
  g1: group NArrayGroup ->
  g2: group NArrayGroup ->
  s1: ast0_wf_array_group g1 ->
  s2: ast0_wf_array_group g2 ->
  ast0_wf_array_group (GChoice g1 g2)
| WfADef:
  n: string ->
  ast0_wf_array_group (GDef n) // will be taken into account by the syntax environment

and ast0_wf_map_group
: group NMapGroup -> Type
=
| WfMDef:
    n: string ->
    ast0_wf_map_group (GDef n)
| WfMChoice:
    g1': group NMapGroup ->
    s1: ast0_wf_map_group g1' ->
    g2': group NMapGroup ->
    s2: ast0_wf_map_group g2' ->
    ast0_wf_map_group (GChoice g1' g2')
| WfMConcat:
    g1: group NMapGroup ->
    s1: ast0_wf_map_group g1 ->
    g2: group NMapGroup ->
    s2: ast0_wf_map_group g2 ->
    ast0_wf_map_group (GConcat g1 g2)
| WfMZeroOrOne:
    g: group NMapGroup ->
    s: ast0_wf_map_group g ->
    ast0_wf_map_group (GZeroOrOne g)
| WfMLiteral:
    cut: bool ->
    key: literal ->
    value: typ ->
    s: ast0_wf_typ value ->
    ast0_wf_map_group (GMapElem () cut (TElem (ELiteral key)) value)
| WfMZeroOrMore:
    key: typ ->
    value: typ ->
    s_key: ast0_wf_typ key ->
    s_value: ast0_wf_typ value ->
    ast0_wf_map_group (GZeroOrMore (GMapElem () false key value))

and ast0_restrict_map_group
: Spec.typ -> group NMapGroup -> group NMapGroup -> Type
=
| RMDefKeep:
    left: Spec.typ ->
    n: string ->
    ast0_restrict_map_group left (GDef n) (GDef n)
| RMDefSkip:
    left: Spec.typ ->
    n: string ->
    ast0_restrict_map_group left (GDef n) GNop
| RMChoice:
    left: Spec.typ ->
    g1: group NMapGroup ->
    g1': group NMapGroup ->
    s1: ast0_restrict_map_group left g1 g1' ->
    g2: group NMapGroup ->
    g2': group NMapGroup ->
    s2: ast0_restrict_map_group left g2 g2' ->
    ast0_restrict_map_group left (GChoice g1 g2) (GChoice g1' g2')
| RMConcat:
    left: Spec.typ ->
    g1: group NMapGroup ->
    g1': group NMapGroup ->
    s1: ast0_restrict_map_group left g1 g1' ->
    fp1: Spec.typ ->
    g2: group NMapGroup ->
    g2': group NMapGroup ->
    s2: ast0_restrict_map_group (left `Spec.t_choice` fp1) g2 g2' ->
    ast0_restrict_map_group left (GConcat g1 g2) (GConcat g1' g2')
| RMZeroOrOne:
    left: Spec.typ ->
    g: group NMapGroup ->
    g': group NMapGroup ->
    s: ast0_restrict_map_group left g g' ->
    ast0_restrict_map_group left (GZeroOrOne g) (GZeroOrOne g')
| RMElemLiteral:
    left: Spec.typ ->
    cut: bool ->
    key: literal ->
    value: typ ->
    s: ast0_wf_typ value ->
    ast0_restrict_map_group left (GMapElem () cut (TElem (ELiteral key)) value) (GMapElem () cut (TElem (ELiteral key)) value)
| RMZeroOrMoreKeep:
    left: Spec.typ ->
    key: typ ->
    value: typ ->
    s_key: ast0_wf_typ key ->
    s_value: ast0_wf_typ value ->
    ast0_restrict_map_group left (GZeroOrMore (GMapElem () false key value)) (GZeroOrMore (GMapElem () false key value))
| RMZeroOrMoreSkip:
    left: Spec.typ ->
    key: typ ->
    value: typ ->
    s_key: ast0_wf_typ key ->
    s_value: ast0_wf_typ value ->
    ast0_restrict_map_group left (GZeroOrMore (GMapElem () false key value)) GNop

let rec spec_wf_typ
  (env: sem_env)
  (t: typ)
  (wf: ast0_wf_typ t)
: Tot prop
  (decreases wf)
= match wf with
| WfTArray g s ->
  spec_wf_array_group env g s
| WfTMap g g1 s1 g2 s2 ->
    group_bounded NMapGroup env.se_bound g1 /\
    group_bounded NMapGroup env.se_bound g2 /\
    map_group_sem env g1 == map_group_sem env g2 /\
    spec_restrict_map_group env Spec.t_always_false g g1 s1 /\
    spec_wf_map_group env g2 s2
| WfTChoice t1 t2 s1 s2 ->
  typ_bounded env.se_bound t1 /\
  typ_bounded env.se_bound t2 /\
  spec_wf_typ env t1 s1 /\
  spec_wf_typ env t2 s2 /\
  Spec.typ_disjoint (typ_sem env t1) (typ_sem env t2)
| WfTElem e -> True
| WfTDef n ->
  env.se_bound n == Some NType

and spec_wf_array_group
  (env: sem_env)
  (g: group NArrayGroup)
  (wf: ast0_wf_array_group g)
: Tot prop
  (decreases wf)
= match wf with
| WfAElem ty prf ->
  spec_wf_typ env ty prf
| WfAZeroOrOne g s ->
  group_bounded NArrayGroup env.se_bound g /\
  spec_wf_array_group env g s /\
  Spec.array_group3_is_nonempty (array_group_sem env g)
| WfAZeroOrOneOrMore g s g' ->
  group_bounded NArrayGroup env.se_bound g /\
  spec_wf_array_group env g s /\
  (
      let a = array_group_sem env g in
      Spec.array_group3_is_nonempty a /\
      Spec.array_group3_concat_unique_strong a a
  )
| WfAConcat g1 g2 s1 s2 ->
  group_bounded NArrayGroup env.se_bound g1 /\
  group_bounded NArrayGroup env.se_bound g2 /\
  spec_wf_array_group env g1 s1 /\
  spec_wf_array_group env g2 s2 /\
  Spec.array_group3_concat_unique_weak (array_group_sem env g1) (array_group_sem env g2)
| WfAChoice g1 g2 s1 s2 ->
  group_bounded NArrayGroup env.se_bound g1 /\
  group_bounded NArrayGroup env.se_bound g2 /\
  spec_wf_array_group env g1 s1 /\
  spec_wf_array_group env g2 s2 /\
  Spec.array_group3_disjoint (array_group_sem env g1) (array_group_sem env g2)
| WfADef n ->
  env.se_bound n == Some NArrayGroup

and spec_wf_map_group
  (env: sem_env)
  (g: group NMapGroup)
  (wf: ast0_wf_map_group g)
: Tot prop
  (decreases wf)
= match wf with
| WfMDef n ->
    env.se_bound n == Some NMapGroup
| WfMChoice g1' s1 g2' s2 ->
    group_bounded NMapGroup env.se_bound g1' /\
    spec_wf_map_group env g1' s1 /\
    group_bounded NMapGroup env.se_bound g2' /\
    spec_wf_map_group env g2' s2 /\
    MapSpec.map_group_choice_compatible
      (map_group_sem env g1')
      (map_group_sem env g2')
| WfMConcat g1 s1 g2 s2 ->
    group_bounded NMapGroup env.se_bound g1 /\
    spec_wf_map_group env g1 s1 /\
    group_bounded NMapGroup env.se_bound g2 /\
    spec_wf_map_group env g2 s2 /\
    (
      match spec_map_group_footprint env g1, spec_map_group_footprint env g2 with
      | Some fp1, Some fp2 -> Spec.typ_disjoint fp1 fp2
      | _ -> False
    )
| WfMZeroOrOne g s ->
    group_bounded NMapGroup env.se_bound g /\
    spec_wf_map_group env g s /\
    MapSpec.map_group_is_productive (map_group_sem env g)
| WfMLiteral cut key value s ->
    spec_wf_typ env value s
| WfMZeroOrMore key value s_key s_value ->
    typ_bounded env.se_bound key /\
    spec_wf_typ env key s_key /\
    spec_wf_typ env value s_value

and spec_restrict_map_group
  (env: sem_env)
  (left: Spec.typ)
  (g: group NMapGroup)
  (g' : group NMapGroup)
  (s: ast0_restrict_map_group left g g')
: Tot prop
  (decreases s)
= match s with
| RMDefKeep left n ->
    env.se_bound n == Some NMapGroup /\
    (
      match env.se_map_group_metadata n with
      | Some md -> Spec.typ_disjoint left md.g_restrict_footprint
      | _ -> False
    )
| RMDefSkip left n ->
    env.se_bound n == Some NMapGroup /\
    (
      match env.se_map_group_metadata n with
      | Some md -> md.g_is_filter
      | _ -> False
    )
| RMChoice left g1 g1' s1 g2 g2' s2 ->
    group_bounded NMapGroup env.se_bound g1' /\
    spec_restrict_map_group env left g1 g1' s1 /\
    group_bounded NMapGroup env.se_bound g2' /\
    spec_restrict_map_group env left g2 g2' s2 /\
    MapSpec.map_group_choice_compatible
      (map_group_sem env g1')
      (map_group_sem env g2')
| RMConcat left g1 g1' s1 fp1 g2 g2' s2 ->
    group_bounded NMapGroup env.se_bound g1 /\
    spec_restrict_map_group env left g1 g1' s1 /\
    spec_map_group_footprint env g1 == Some fp1 /\
    spec_restrict_map_group env (left `Spec.t_choice` fp1) g2 g2' s2
| RMZeroOrOne left g g' s ->
    spec_restrict_map_group env left g g' s
| RMElemLiteral left cut key value s' ->
    spec_wf_typ env value s' /\
    Spec.typ_disjoint left (Spec.t_literal (eval_literal key))
| RMZeroOrMoreKeep left key value s_key s_value ->
    typ_bounded env.se_bound key /\
    spec_wf_typ env key s_key /\
    spec_wf_typ env value s_value /\
    Spec.typ_disjoint left (typ_sem env key)
| RMZeroOrMoreSkip left key value s_key s_value ->
    spec_wf_typ env key s_key /\
    spec_wf_typ env value s_value

[@@ sem_attr]
let rec spec_wf_typ_incr
  (env env': sem_env)
  (g: typ)
  (wf: ast0_wf_typ g)
: Lemma
  (requires sem_env_included env env' /\
    spec_wf_typ env g wf
  )
  (ensures
      spec_wf_typ env' g wf
  )
  (decreases wf)
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_typ env g wf)];
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_typ env' g wf)];
  ]]
= match wf with
  | WfTArray g s ->
    spec_wf_array_group_incr env env' g s
  | WfTMap g g1 s1 g2 s2 ->
    spec_restrict_map_group_incr env env' Spec.t_always_false g g1 s1;
    spec_wf_map_group_incr env env' g2 s2
  | WfTChoice t1 t2 s1 s2 ->
    spec_wf_typ_incr env env' t1 s1;
    spec_wf_typ_incr env env' t2 s2
  | WfTElem _
  | WfTDef _ -> ()

and spec_wf_array_group_incr
  (env env': sem_env)
  (g: group NArrayGroup)
  (wf: ast0_wf_array_group g)
: Lemma
  (requires sem_env_included env env' /\
    spec_wf_array_group env g wf
  )
  (ensures
      spec_wf_array_group env' g wf
  )
  (decreases wf)
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_array_group env g wf)];
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_array_group env' g wf)];
  ]]
= match wf with
  | WfAElem ty prf ->
    spec_wf_typ_incr env env' ty prf
  | WfAZeroOrOne g s ->
    spec_wf_array_group_incr env env' g s
  | WfAZeroOrOneOrMore g s g' ->
    spec_wf_array_group_incr env env' g s
  | WfAConcat g1 g2 s1 s2
  | WfAChoice g1 g2 s1 s2 ->
    spec_wf_array_group_incr env env' g1 s1;
    spec_wf_array_group_incr env env' g2 s2
  | WfADef _ -> ()

and spec_restrict_map_group_incr
  (env env': sem_env)
  (left: Spec.typ)
  (g1 g2: group NMapGroup)
  (wf: ast0_restrict_map_group left g1 g2)
: Lemma
  (requires sem_env_included env env' /\
    spec_restrict_map_group env left g1 g2 wf
  )
  (ensures
      spec_restrict_map_group env' left g1 g2 wf
  )
  (decreases wf)
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (spec_restrict_map_group env left g1 g2 wf)];
    [SMTPat (sem_env_included env env'); SMTPat (spec_restrict_map_group env' left g1 g2 wf)];
  ]]
= match wf with
  | RMChoice left g1 g1' s1 g2 g2' s2 ->
    spec_restrict_map_group_incr env env' left g1 g1' s1;
    spec_restrict_map_group_incr env env' left g2 g2' s2
  | RMConcat left g1 g1' s1 fp1 g2 g2' s2 ->
    spec_restrict_map_group_incr env env' left g1 g1' s1;
    spec_restrict_map_group_incr env env' (left `Spec.t_choice` fp1) g2 g2' s2
  | RMZeroOrOne left g g' s ->
    spec_restrict_map_group_incr env env' left g g' s
  | RMElemLiteral left cut key value s' ->
    spec_wf_typ_incr env env' value s'
  | RMZeroOrMoreKeep _ key value s_key s_value
  | RMZeroOrMoreSkip _ key value s_key s_value ->
    spec_wf_typ_incr env env' key s_key;
    spec_wf_typ_incr env env' value s_value    
  | RMDefKeep _ _
  | RMDefSkip _ _ -> ()

and spec_wf_map_group_incr
  (env env': sem_env)
  (g: group NMapGroup)
  (wf: ast0_wf_map_group g)
: Lemma
  (requires sem_env_included env env' /\
    group_bounded NMapGroup env.se_bound g /\
    spec_wf_map_group env g wf
  )
  (ensures
      group_bounded NMapGroup env'.se_bound g /\
      spec_wf_map_group env' g wf
  )
  (decreases wf)
  [SMTPatOr [
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_map_group env g wf)];
    [SMTPat (sem_env_included env env'); SMTPat (spec_wf_map_group env' g wf)];
  ]]
= match wf with
  | WfMConcat g1' s1 g2' s2
  | WfMChoice g1' s1 g2' s2 ->
    spec_wf_map_group_incr env env' g1' s1;
    spec_wf_map_group_incr env env' g2' s2
  | WfMZeroOrOne g s ->
    spec_wf_map_group_incr env env' g s
  | WfMLiteral cut key value s ->
    spec_wf_typ_incr env env' value s
  | WfMZeroOrMore key value s_key s_value ->
    spec_wf_typ_incr env env' key s_key;
    spec_wf_typ_incr env env' value s_value
  | WfMDef _ -> ()

[@@ sem_attr]
let ast_env_elem0 (s: name_env_elem) : Type0 =
  match s with
  | NType -> typ
  | NArrayGroup -> group NArrayGroup
  | NMapGroup -> group NMapGroup

let ast_env_elem_prop (e_sem_env: sem_env) (s: name_env_elem) (phi: sem_env_elem s) (x: ast_env_elem0 s) : Tot prop =
  match s with
  | NType ->
    typ_bounded e_sem_env.se_bound x /\
    Spec.typ_equiv (typ_sem e_sem_env x) phi
  | NArrayGroup ->
    group_bounded NArrayGroup e_sem_env.se_bound x /\
    Spec.array_group3_equiv (array_group_sem e_sem_env x) phi
  | NMapGroup ->
    group_bounded NMapGroup e_sem_env.se_bound x /\
    map_group_sem e_sem_env x == phi

let ast_env_elem_prop_included (e1 e2: sem_env) (s: name_env_elem) (phi: sem_env_elem s) (x: ast_env_elem0 s) : Lemma
  (requires sem_env_included e1 e2 /\
    ast_env_elem_prop e1 s phi x
  )
  (ensures ast_env_elem_prop e2 s phi x)
  [SMTPat (ast_env_elem_prop e1 s phi x); SMTPat (ast_env_elem_prop e2 s phi x)]
= ()

[@@ sem_attr]
let ast_env_elem (e_sem_env: sem_env) (s: name_env_elem) (phi: sem_env_elem s) =
  (x: ast_env_elem0 s { ast_env_elem_prop e_sem_env s phi x })

[@@ bounded_attr; sem_attr]
noeq
type ast_env = {
  e_sem_env: sem_env;
  e_env: (i: name e_sem_env.se_bound) -> (ast_env_elem e_sem_env (Some?.v (e_sem_env.se_bound i)) (e_sem_env.se_env i));
}

[@@"opaque_to_smt"] irreducible // because of false_elim
let e_env_empty (i: name empty_name_env) : Tot (ast_env_elem empty_sem_env (Some?.v (empty_name_env i)) (empty_sem_env.se_env i)) = false_elim ()

[@@"opaque_to_smt"; bounded_attr; sem_attr]
let empty_ast_env : (e: ast_env {
  e.e_sem_env.se_bound == empty_name_env
}) = {
  e_sem_env = empty_sem_env;
  e_env = e_env_empty;
}

let ast_env_included
  (e1 e2: ast_env)
: Tot prop
= sem_env_included e1.e_sem_env e2.e_sem_env /\
  (forall (i: name e1.e_sem_env.se_bound) . e2.e_env i == e1.e_env i)

let ast_env_included_trans (s1 s2 s3: ast_env) : Lemma
  (requires (ast_env_included s1 s2 /\ ast_env_included s2 s3))
  (ensures (ast_env_included s1 s3))
  [SMTPat (ast_env_included s1 s3); SMTPat (ast_env_included s1 s2)]
= ()

[@@"opaque_to_smt"; bounded_attr; sem_attr]
let ast_env_extend_gen
  (e: ast_env)
  (new_name: string)
  (kind: name_env_elem)
  (s: sem_env_elem kind)
  (x: ast_env_elem e.e_sem_env kind s)
: Pure ast_env
    (requires
      (~ (new_name `name_mem` e.e_sem_env.se_bound))
    )
    (ensures fun e' ->
      e'.e_sem_env == sem_env_extend_gen e.e_sem_env new_name kind s /\
      ast_env_included e e' /\
      e'.e_env new_name == x
    )
= let se' = sem_env_extend_gen e.e_sem_env new_name kind s in
  {
    e_sem_env = se';
    e_env = (fun (i: name se'.se_bound) ->
      if i = new_name
      then x
      else e.e_env i
    );
  }




(*

let forall_intro_requires_2
      (#a: Type)
      (#b: (a -> Type))
      (#p: (x: a -> b x -> GTot Type0))
      (#q: (x: a -> b x -> GTot Type0))
      ($prf: (x: a -> y: b x -> Lemma (requires p x y) (ensures q x y)))
    : Lemma (forall (x: a) (y: b x). p x y ==> q x y)
= Classical.forall_intro_2 (fun x y -> Classical.move_requires (prf x) y)

#push-options "--z3rlimit 32"

#restart-solver
let rec spec_map_group_restrict_correct
  (env: sem_env)
  (g: group NMapGroup)
  (left: Spec.typ)
  (g'fp' : (MapSpec.map_group & Spec.typ))
: Lemma
    (requires 
      group_bounded NMapGroup env.se_bound g /\
      spec_map_group_restrict env left g g'fp'
    )
    (ensures (
      group_bounded NMapGroup env.se_bound g /\
      spec_map_group_restrict env left g g'fp' /\
      begin match spec_map_group_footprint env g with
      | Some fp ->
        let (g', fp') = g'fp' in
        MapSpec.restrict_map_group (map_group_sem env g) g' /\
        MapSpec.map_group_footprint g' fp' /\
        Spec.typ_included fp' fp /\
        Spec.typ_disjoint left fp'
      | _ -> False
      end
    ))
    (decreases g)
= match g with
  | GDef n -> ()
  | GChoice g1 g2 ->
    let g1'fp1' = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun g1'fp1' ->
      spec_map_group_restrict env left g1 g1'fp1' /\
      (exists g2'fp2' . spec_map_group_restrict env left g2 g2'fp2' /\
        (let (g1', fp1') = g1'fp1' in
        let (g2', fp2') = g2'fp2' in
        g'fp' == (g1' `MapSpec.map_group_choice` g2', fp1' `Spec.t_choice` fp2')))
    )
    in
    let g2'fp2' = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun g2'fp2' ->
      spec_map_group_restrict env left g2 g2'fp2' /\
        (let (g1', fp1') = g1'fp1' in
        let (g2', fp2') = g2'fp2' in
        g'fp' == (g1' `MapSpec.map_group_choice` g2', fp1' `Spec.t_choice` fp2'))
    )
    in
    let (g1', fp1') = g1'fp1' in
    let (g2', fp2') = g2'fp2' in
    spec_map_group_restrict_correct env g1 left g1'fp1';
    spec_map_group_restrict_correct env g2 left g2'fp2';
    MapSpec.restrict_map_group_choice (map_group_sem env g1) g1' (map_group_sem env g2) g2';
    ()
  | _ -> assume False

#pop-options


(*
          MapSpec.restrict_map_group_concat
            (map_group_sem env g1)
            fp1
            g1'
            (map_group_sem env g2)
            g2'
            fp2';
          assert (MapSpec.restrict_map_group (map_group_sem env g) g');
          MapSpec.map_group_footprint_concat g1' g2' fp1' fp2';
          assert (MapSpec.map_group_footprint g' fp');
          assert (Spec.typ_included fp' (fp1 `Spec.t_choice` fp2));
          assert (Spec.typ_disjoint left fp');


    MapSpec.map_group_footprint_match_item_for cut vkey (typ_sem env value);

*)


(*

(* TODO: support recursion on types *)

noeq
type result =
| ResultSuccess
| ResultFailure of string
| ResultOutOfFuel

(* Equivalence and disjointness *)

#push-options "--z3rlimit 32"

[@@"opaque_to_smt"]
let rec typ_equiv
  (e: ast_env)
  (fuel: nat)
  (t1: typ)
  (t2: typ)
: Pure bool
  (requires (
    typ_bounded e.e_sem_env.se_bound t1 /\
    typ_bounded e.e_sem_env.se_bound t2
  ))
  (ensures (fun b ->
    typ_bounded e.e_sem_env.se_bound t1 /\
    typ_bounded e.e_sem_env.se_bound t2 /\
    (b == true ==> Spec.typ_equiv (typ_sem e.e_sem_env t1) (typ_sem e.e_sem_env t2))
  ))
  (decreases fuel)
= if t1 `typ_eq` t2
  then true
  else if fuel = 0
  then false
  else let fuel' : nat = fuel - 1 in
  match t1, t2 with
  | TElem (TDef i), _ ->
    let s1 = e.e_sem_env.se_env i in
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
  | (TMap i1), (TMap i2) -> i1 = i2 // TODO
  | _ -> false

and array_group_equiv
  (e: ast_env)
  (fuel: nat)
  (t1: array_group)
  (t2: array_group)
: Pure bool
  (requires (
    array_group_bounded e.e_sem_env.se_bound t1 /\
    array_group_bounded e.e_sem_env.se_bound t2
  ))
  (ensures (fun b ->
    array_group_bounded e.e_sem_env.se_bound t1 /\
    array_group_bounded e.e_sem_env.se_bound t2 /\
    (b == true ==> Spec.array_group3_equiv (array_group_sem e.e_sem_env t1) (array_group_sem e.e_sem_env t2))
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
    let s1 = e.e_sem_env.se_env i1 in
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
       assert (Spec.array_group3_equiv (atom_array_group_sem e.e_sem_env t1) (atom_array_group_sem e.e_sem_env t2));
       assert (Spec.array_group3_equiv (Spec.array_group3_zero_or_more (atom_array_group_sem e.e_sem_env t1)) (Spec.array_group3_zero_or_more (atom_array_group_sem e.e_sem_env t2)));
       array_group_equiv e fuel' q1 q2
    end
    else false
  | (s1, TAOneOrMore t1) :: q1, (s2, TAOneOrMore t2) :: q2 ->
    if array_group_equiv e fuel' [s1, TAAtom t1] [s2, TAAtom t2]
    then begin
       assert (Spec.array_group3_equiv (atom_array_group_sem e.e_sem_env t1) (atom_array_group_sem e.e_sem_env t2));
       assert (Spec.array_group3_equiv (Spec.array_group3_one_or_more (atom_array_group_sem e.e_sem_env t1)) (Spec.array_group3_one_or_more (atom_array_group_sem e.e_sem_env t2)));
       array_group_equiv e fuel' q1 q2
    end
    else false
  | (s1, TAZeroOrOne t1) :: q1, (s2, TAZeroOrOne t2) :: q2 ->
    if array_group_equiv e fuel' [s1, TAAtom t1] [s2, TAAtom t2]
    then begin
       assert (Spec.array_group3_equiv (atom_array_group_sem e.e_sem_env t1) (atom_array_group_sem e.e_sem_env t2));
       assert (Spec.array_group3_equiv (Spec.array_group3_zero_or_one (atom_array_group_sem e.e_sem_env t1)) (Spec.array_group3_zero_or_one (atom_array_group_sem e.e_sem_env t2)));
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
    typ_bounded e.e_sem_env.se_bound t1 /\
    typ_bounded e.e_sem_env.se_bound t2
  ))
  (ensures (fun b ->
    typ_bounded e.e_sem_env.se_bound t1 /\
    typ_bounded e.e_sem_env.se_bound t2 /\
    (b == ResultSuccess ==> Spec.typ_disjoint (typ_sem e.e_sem_env t1) (typ_sem e.e_sem_env t2))
  ))
  (decreases fuel)
= if fuel = 0
  then ResultOutOfFuel
  else let fuel' : nat = fuel - 1 in
  match t1, t2 with
  | TElem (TDef i), _ ->
    let s1 = e.e_sem_env.se_env i in
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
    Spec.array3_close_array_group (array_group_sem e.e_sem_env i1);
    Spec.array3_close_array_group (array_group_sem e.e_sem_env i2);
    array_group_disjoint e fuel' true i1 i2
  | TElem (TElemArray i1), TElem (TElemArray i2) ->
    Spec.array3_close_array_group (array_group_sem e.e_sem_env ["", i1]);
    Spec.array3_close_array_group (array_group_sem e.e_sem_env ["", i2]);
    array_group_disjoint e fuel' true ["", i1] ["", i2]
  | TArray i1, TElem (TElemArray i2)
    ->
    Spec.array3_close_array_group (array_group_sem e.e_sem_env i1);
    Spec.array3_close_array_group (array_group_sem e.e_sem_env ["", i2]);
    array_group_disjoint e fuel' true i1 ["", i2]
  | TElem (TElemArray i2), TArray i1
    ->
    Spec.array3_close_array_group (array_group_sem e.e_sem_env i1);
    Spec.array3_close_array_group (array_group_sem e.e_sem_env ["", i2]);
    array_group_disjoint e fuel' true ["", i2] i1
  | TArray _, _
  | _, TArray _ -> ResultSuccess
  | TElem (TLiteral (TLSimple l1)) , TElem TBool
  | TElem TBool, TElem (TLiteral (TLSimple l1))
  -> if l1 = Spec.simple_value_false || l1 = Spec.simple_value_true
    then ResultFailure "typ_disjoint: TFalse, TBool"
    else ResultSuccess
  | TElem (TLiteral (TLString ty1 _)), TElem TByteString
  | TElem TByteString, TElem (TLiteral (TLString ty1 _))
  -> if ty1 = cddl_major_type_byte_string
    then ResultFailure "typ_disjoint: byte_string"
    else ResultSuccess
  | TElem (TLiteral (TLString ty1 _)), TElem TTextString
  | TElem TTextString, TElem (TLiteral (TLString ty1 _))
  -> if ty1 = cddl_major_type_text_string
    then ResultFailure "typ_disjoint: byte_string"
    else ResultSuccess
  | (TMap _), (TMap _) -> ResultFailure "typ_disjoint: TMap, TMap" // TODO
  | TMap _, _ | _, TMap _ -> ResultSuccess
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
    array_group_bounded e.e_sem_env.se_bound t1 /\
    array_group_bounded e.e_sem_env.se_bound t2
  ))
  (ensures (fun b ->
    array_group_bounded e.e_sem_env.se_bound t1 /\
    array_group_bounded e.e_sem_env.se_bound t2 /\
    (b == ResultSuccess ==> Spec.array_group3_disjoint
      (Spec.maybe_close_array_group (array_group_sem e.e_sem_env t1) close)
      (Spec.maybe_close_array_group (array_group_sem e.e_sem_env t2) close)
  )))
  (decreases fuel)
= if fuel = 0
  then ResultOutOfFuel
  else let fuel' : nat = fuel - 1 in
  match t1, t2 with
  | (_, TAAtom (TADef i1)) :: q1, _ ->
    let s1 = e.e_sem_env.se_env i1 in
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
    else if ResultSuccess? (array_group_disjoint e fuel' false [name, TAAtom t1'] t2) // loop-free shortcut, but will miss things like "disjoint? (a* ) (ab)"
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
    array_group_sem_cons e.e_sem_env n1 (TAAtom (TAElem t1')) q1;
    array_group_sem_cons e.e_sem_env n2 (TAAtom (TAElem t2')) q2;
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
  (e: sem_env)
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
  (e1 e2: sem_env)
  (a: array_group)
: Lemma
  (requires
     sem_env_included e1 e2 /\
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
  (e: sem_env)
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

#push-options "--z3rlimit 64"

#restart-solver
let rec spec_array_group_splittable_fold_gen
  (e: sem_env)
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
      (i `name_mem` e.e_sem_env.se_bound /\
        SEArrayGroup? (e.e_sem_env.se_env i) /\
        spec_array_group_splittable e.e_sem_env (e.e_env i)
    ))

#push-options "--z3rlimit 256 --split_queries always --ifuel 8 --fuel 8 --query_stats"

#restart-solver
[@@"opaque_to_smt"]
let rec array_group_concat_unique_strong
  (e: ast_env)
  (e_thr: spec_array_group_splittable_threshold e)
  (fuel: nat)
  (a1 a2: array_group)
: Pure result
  (requires
    spec_array_group_splittable e.e_sem_env a1 /\
    array_group_bounded e.e_sem_env.se_bound a2
  )
  (ensures fun b ->
    b == ResultSuccess ==> Spec.array_group3_concat_unique_strong
      (array_group_sem e.e_sem_env a1)
      (array_group_sem e.e_sem_env a2)
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
        (array_group_sem e.e_sem_env [n1, t1l])
        (array_group_sem e.e_sem_env (a1' `List.Tot.append` a2))
      );
      array_group_sem_cons e.e_sem_env n1 t1l a1';
      array_group_sem_append e.e_sem_env a1' a2;
      assert (array_group_sem e.e_sem_env [n1, t1l] == elem_array_group_sem e.e_sem_env t1l);
      Spec.array_group3_concat_unique_strong_equiv
        (array_group_sem e.e_sem_env [n1, t1l])
        (elem_array_group_sem e.e_sem_env t1l)
        (array_group_sem e.e_sem_env (a1' `List.Tot.append` a2))
        (array_group_sem e.e_sem_env a1' `Spec.array_group3_concat` array_group_sem e.e_sem_env a2);
      assert (Spec.array_group3_concat_unique_strong
        (elem_array_group_sem e.e_sem_env t1l)
        (array_group_sem e.e_sem_env a1' `Spec.array_group3_concat` array_group_sem e.e_sem_env a2)
      );
      Spec.array_group3_concat_unique_strong_concat_left (elem_array_group_sem e.e_sem_env t1l) (array_group_sem e.e_sem_env a1') (array_group_sem e.e_sem_env a2);
      assert (Spec.array_group3_concat_unique_strong
        (array_group_sem e.e_sem_env a1)
        (array_group_sem e.e_sem_env a2)
      );
      ResultSuccess
    end
  | [_, TAAtom (TAElem _)], _ -> ResultSuccess
  | [n1, TAAtom (TADef i)], _ ->
    if SEArrayGroup? (e.e_sem_env.se_env i)
    then
      if not (e_thr i)
      then ResultFailure "array_group_concat_unique_strong: unfold left, beyond threshold"
      else
        let t1 = e.e_env i in
        let res = array_group_concat_unique_strong e e_thr fuel' t1 a2 in
        assert (res == ResultSuccess ==> Spec.array_group3_concat_unique_strong
          (array_group_sem e.e_sem_env a1)
          (array_group_sem e.e_sem_env a2)
        );
        res
    else ResultSuccess
  | _, (n2, TAAtom (TADef i)) :: a2' ->
    array_group_sem_cons e.e_sem_env n2 (TAAtom (TADef i)) a2';
    if SEArrayGroup? (e.e_sem_env.se_env i)
    then
      let t1 = e.e_env i in
      array_group_sem_append e.e_sem_env t1 a2';
      Spec.array_group3_concat_equiv
        (elem_array_group_sem e.e_sem_env (TAAtom (TADef i)))
        (array_group_sem e.e_sem_env t1)
        (array_group_sem e.e_sem_env a2')
        (array_group_sem e.e_sem_env a2');
      let res = array_group_concat_unique_strong e e_thr fuel' a1 (t1 `List.Tot.append` a2') in
      if ResultSuccess? res
      then begin
        assert (Spec.array_group3_concat_unique_strong
          (array_group_sem e.e_sem_env a1)
          (array_group_sem e.e_sem_env a2)
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
        (atom_array_group_sem e.e_sem_env t1)
        (array_group_sem e.e_sem_env a2);
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
        (atom_array_group_sem e.e_sem_env t1)
        (array_group_sem e.e_sem_env a2);
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
        (atom_array_group_sem e.e_sem_env t1)
        (array_group_sem e.e_sem_env a2);
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
  (requires spec_array_group_splittable e.e_sem_env a2 /\
    array_group_bounded e.e_sem_env.se_bound a1
  )
  (ensures fun b ->
    array_group_bounded e.e_sem_env.se_bound (a1 `List.Tot.append` a2) /\
    (b == ResultSuccess ==> spec_array_group_splittable e.e_sem_env (a1 `List.Tot.append` a2))
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
    if SEArrayGroup? (e.e_sem_env.se_env i)
    then
      if not (e_thr i)
      then ResultFailure "array_group_splittable: unfold left, beyond threshold"
      else
        let t1 = e.e_env i in
        let res = array_group_splittable e e_thr fuel' t1 a2 in
        if not (ResultSuccess? res)
        then res
        else begin
          spec_array_group_splittable_fold e.e_sem_env t1 a2;
          ResultSuccess
        end
    else ResultSuccess
  | [_, TAAtom (TAElem _)], _ -> ResultSuccess
  | _, (n2, TAAtom (TADef i)) :: a2' ->
    if SEArrayGroup? (e.e_sem_env.se_env i)
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
            spec_array_group_splittable_fold_gen e.e_sem_env a1 t1 a2' n2 (TAAtom (TADef i));
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
        (atom_array_group_sem e.e_sem_env t1)
        (array_group_sem e.e_sem_env a2);
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
        (atom_array_group_sem e.e_sem_env t1)
        (array_group_sem e.e_sem_env a2);
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
        (atom_array_group_sem e.e_sem_env t1)
        (array_group_sem e.e_sem_env a2);
      ResultSuccess
    end
//  | _ -> false

#pop-options

let rec spec_choice_typ_well_formed
  (env: sem_env)
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
  (env1 env2: sem_env)
  (l: list elem_typ)
: Lemma
  (requires
    sem_env_included env1 env2 /\
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
  (requires typ_bounded e.e_sem_env.se_bound (TChoice l))
  (ensures fun b ->
    b == ResultSuccess ==>  spec_choice_typ_well_formed e.e_sem_env l
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
  (env: sem_env)
  (#s: sem_env_elem)
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
  | SEMapGroup _ -> True // TODO

let ast_env_elem_well_formed'
  (e: ast_env)
  (e_thr: spec_array_group_splittable_threshold e)
  (fuel: nat)
  (#s: sem_env_elem)
  (x: ast_env_elem e.e_sem_env s)
: Pure result
    (requires True)
    (ensures fun res ->
      res == ResultSuccess ==> spec_ast_env_elem_well_formed e.e_sem_env x
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
      (i `name_mem` e.e_sem_env.se_bound /\
        spec_ast_env_elem_well_formed e.e_sem_env (e.e_env i)
    ))

[@@ bounded_attr; sem_attr]
noeq
type wf_ast_env = {
  we_env: ast_env;
  we_env_wf: spec_ast_env_elem_well_formed_threshold we_env;
  we_env_wf_prop: squash (forall (i: name we_env.e_sem_env.se_bound) . we_env_wf i == true);
}

[@@"opaque_to_smt"]
let spec_array_group_splittable_threshold_of_ast_elem_well_formed_threshold
  (e: ast_env)
  (f: spec_ast_env_elem_well_formed_threshold e)
: Tot (spec_array_group_splittable_threshold e)
= (fun i ->
    if f i
    then SEArrayGroup? (e.e_sem_env.se_env i)
    else false
  )

let ast_env_elem_well_formed
  (e: ast_env)
  (e_thr: spec_ast_env_elem_well_formed_threshold e)
  (fuel: nat)
  (#s: sem_env_elem)
  (x: ast_env_elem e.e_sem_env s)
: Pure result
    (requires True)
    (ensures fun res ->
      res == ResultSuccess ==> spec_ast_env_elem_well_formed e.e_sem_env x
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
  (e: sem_env)
: Lemma
  (ensures (spec_array_group_splittable e []))
  [SMTPat (spec_array_group_splittable e [])]
= assert_norm (spec_array_group_splittable e []) // would need 1 fuel

let spec_ast_env_elem_well_formed_threshold_fuel
  (#e: ast_env)
  (e_thr: spec_ast_env_elem_well_formed_threshold e)
  (new_name: name e.e_sem_env.se_bound)
: Tot Type0
= (fuel: nat {
    ast_env_elem_well_formed e e_thr fuel (e.e_env new_name) == ResultSuccess
  })

let spec_ast_env_elem_well_formed_threshold_fuel_intro
  (fuel: nat)
  (e: ast_env)
  (e_thr: spec_ast_env_elem_well_formed_threshold e)
  (new_name: name e.e_sem_env.se_bound)
  (prf: squash (ast_env_elem_well_formed e e_thr fuel (e.e_env new_name) == ResultSuccess))
: Tot (spec_ast_env_elem_well_formed_threshold_fuel e_thr new_name)
= fuel

let spec_ast_env_elem_well_formed_threshold_extend
  (#e: ast_env)
  (e_thr: spec_ast_env_elem_well_formed_threshold e)
  (new_name: name e.e_sem_env.se_bound)
  (fuel: spec_ast_env_elem_well_formed_threshold_fuel e_thr new_name)
: Tot (spec_ast_env_elem_well_formed_threshold e)
= (fun i -> if i = new_name then true else e_thr i)

let spec_ast_env_elem_well_formed_included
  (e1 e2: sem_env)
  (#s: sem_env_elem)
  (x: ast_env_elem e1 s)
: Lemma
  (requires
    sem_env_included e1 e2 /\
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
       spec_ast_env_elem_well_formed_included e1.e_sem_env e2.e_sem_env (e1.e_env i);
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
  (new_name: string { (~ (new_name `name_mem` e.we_env.e_sem_env.se_bound)) } )
  (s: sem_env_elem)
  (x: ast_env_elem e.we_env.e_sem_env s)
  (fuel: spec_ast_env_elem_well_formed_threshold_fuel
    (spec_ast_env_elem_well_formed_threshold_extend_env
      e.we_env_wf
      (ast_env_extend_gen e.we_env new_name s x))
    new_name
  )
: Pure wf_ast_env
    (requires True)
    (ensures fun e' ->
      e'.we_env.e_sem_env.se_bound == e.we_env.e_sem_env.se_bound `extend_name_env` new_name /\
      wf_ast_env_included e e' /\
      e'.we_env.e_sem_env.se_env new_name == s /\
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
  (new_name_fresh: squash (~ (new_name `name_mem` e.we_env.e_sem_env.se_bound))) // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  (a: typ)
  (sq: squash (
    typ_bounded e.we_env.e_sem_env.se_bound a // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  ))
  (fuel: spec_ast_env_elem_well_formed_threshold_fuel
    (spec_ast_env_elem_well_formed_threshold_extend_env
      e.we_env_wf
      (ast_env_extend_typ e.we_env new_name new_name_fresh a sq))
    (name_intro new_name (ast_env_extend_typ e.we_env new_name new_name_fresh a sq).e_sem_env.se_bound new_name_fresh)
  )
: Tot (e': wf_ast_env {
      e'.we_env.e_sem_env.se_bound == e.we_env.e_sem_env.se_bound `extend_name_env` new_name /\
      wf_ast_env_included e e' /\
      e'.we_env.e_sem_env.se_env new_name == SEType (typ_sem e.we_env.e_sem_env a)   /\
      e'.we_env.e_env new_name == a
  })
= wf_ast_env_extend_gen e new_name (SEType (typ_sem e.we_env.e_sem_env a)) a fuel

[@@ bounded_attr; sem_attr]
let wf_ast_env_extend_array_group
  (e: wf_ast_env)
  (new_name: string) // ideally by SMT
  (new_name_fresh: squash (~ (new_name `name_mem` e.we_env.e_sem_env.se_bound))) // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  (a: array_group)
  (sq: squash (
    array_group_bounded e.we_env.e_sem_env.se_bound a // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  ))
  (fuel: spec_ast_env_elem_well_formed_threshold_fuel
    (spec_ast_env_elem_well_formed_threshold_extend_env
      e.we_env_wf
      (ast_env_extend_array_group e.we_env new_name new_name_fresh a sq))
    (name_intro new_name (ast_env_extend_array_group e.we_env new_name new_name_fresh a sq).e_sem_env.se_bound new_name_fresh)
  )
: Tot (e': wf_ast_env {
      e'.we_env.e_sem_env.se_bound == e.we_env.e_sem_env.se_bound `extend_name_env` new_name /\
      wf_ast_env_included e e' /\
      e'.we_env.e_sem_env.se_env new_name == SEArrayGroup (array_group_sem e.we_env.e_sem_env a) /\
      e'.we_env.e_env new_name == a
  })
= wf_ast_env_extend_gen e new_name (SEArrayGroup (array_group_sem e.we_env.e_sem_env a)) a fuel

[@@ bounded_attr; sem_attr]
let wf_ast_env_extend_map_group
  (e: wf_ast_env)
  (new_name: string) // ideally by SMT
  (new_name_fresh: squash (~ (new_name `name_mem` e.we_env.e_sem_env.se_bound))) // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  (a: map_group)
  (sq: squash (
    map_group_bounded e.we_env.e_sem_env.se_bound a // ideally by normalization with (delta_attr [`%bounded_attr; iota; zeta; primops]) + SMT
  ))
  (fuel: spec_ast_env_elem_well_formed_threshold_fuel
    (spec_ast_env_elem_well_formed_threshold_extend_env
      e.we_env_wf
      (ast_env_extend_map_group e.we_env new_name new_name_fresh a sq))
    (name_intro new_name (ast_env_extend_map_group e.we_env new_name new_name_fresh a sq).e_sem_env.se_bound new_name_fresh)
  )
: Tot (e': wf_ast_env {
      e'.we_env.e_sem_env.se_bound == e.we_env.e_sem_env.se_bound `extend_name_env` new_name /\
      wf_ast_env_included e e' /\
      e'.we_env.e_sem_env.se_env new_name == SEMapGroup (map_group_sem e.we_env.e_sem_env a) /\
      e'.we_env.e_env new_name == a
  })
= wf_ast_env_extend_gen e new_name (SEMapGroup (map_group_sem e.we_env.e_sem_env a)) a fuel

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

noeq
type target_type =
| TTDef of string
| TTUnit
| TTSimple
| TTUInt64
| TTString
| TTBool
| TTOption of target_type
| TTPair: target_type -> target_type -> target_type
| TTUnion: target_type -> target_type -> target_type
| TTArray of target_type
| TTNonemptyArray of target_type
| TTEscapeHatch of Spec.typ // TODO: remove

type target_spec_env (bound: name_env) =
  (name bound -> Type0)

let rec target_type_bounded
  (bound: name_env)
  (t: target_type)
: GTot bool
= match t with
  | TTDef s -> s `name_mem` bound
  | TTPair t1 t2
  | TTUnion t1 t2 ->
    target_type_bounded bound t1 &&
    target_type_bounded bound t2
  | TTNonemptyArray a
  | TTArray a
  | TTOption a ->
    target_type_bounded bound a
  | TTSimple
  | TTUInt64
  | TTUnit
  | TTBool
  | TTEscapeHatch _
  | TTString -> true

let cbor_with (t: Spec.typ) : Type0 = (c: CBOR.Spec.raw_data_item { t c })

module U8 = FStar.UInt8
let string64 = (s: Seq.seq U8.t { Seq.length s < pow2 64 })
module U64 = FStar.UInt64

let rec target_type_sem
  (bound: name_env)
  (env: target_spec_env bound)
  (t: target_type)
: Pure Type0
  (requires target_type_bounded bound t)
  (ensures fun _ -> True)
= match t with
  | TTDef s -> env s
  | TTPair t1 t2 -> target_type_sem bound env t1 & target_type_sem bound env t2
  | TTUnion t1 t2 -> target_type_sem bound env t1 `either` target_type_sem bound env t2
  | TTArray a -> list (target_type_sem bound env a)
  | TTNonemptyArray a -> Spec.nelist (target_type_sem bound env a)
  | TTOption a -> option (target_type_sem bound env a)
  | TTSimple -> CBOR.Spec.simple_value
  | TTUInt64 -> U64.t
  | TTUnit -> unit
  | TTBool -> bool
  | TTString -> string64
  | TTEscapeHatch ty -> cbor_with ty

let ttpair (t1 t2: target_type) : target_type = match t1, t2 with
| TTUnit, _ -> t2
| _, TTUnit -> t1
| _ -> TTPair t1 t2

let destruct_ttpair
  (bound: name_env)
  (env: target_spec_env bound)
  (t1 t2: (t: target_type { target_type_bounded bound t }))
  (x: target_type_sem bound env (t1 `ttpair` t2))
: Tot (target_type_sem bound env t1 & target_type_sem bound env t2)
= match t1, t2 with
  | TTUnit, _ -> ((), x)
  | _, TTUnit -> (x, ())
  | _ -> x

let ttpair_fst
  (bound: name_env)
  (env: target_spec_env bound)
  (t1 t2: (t: target_type { target_type_bounded bound t }))
  (x: target_type_sem bound env (t1 `ttpair` t2))
: Tot (target_type_sem bound env t1)
= match t1, t2 with
  | TTUnit, _ -> ()
  | _, TTUnit -> x
  | _ -> fst #(target_type_sem bound env t1) #(target_type_sem bound env t2) x

let construct_ttpair
  (bound: name_env)
  (env: target_spec_env bound)
  (t1 t2: (t: target_type { target_type_bounded bound t }))
  (x: target_type_sem bound env t1 & target_type_sem bound env t2)
: Tot (target_type_sem bound env (t1 `ttpair` t2))
= match t1, t2 with
  | TTUnit, _ -> snd x
  | _, TTUnit -> fst x
  | _ -> x

let rec target_type_of_elem_typ
  (x: elem_typ)
: Tot target_type
= match x with
  | TDef s -> TTDef s
  | TLiteral _ -> TTUnit
  | TBool -> TTBool
  | TByteString
  | TTextString -> TTString
  | TElemArray s -> target_type_of_elem_array_group s

and target_type_of_atom_array_group
  (x: atom_array_group)
: Tot target_type
= match x with
  | TADef i -> TTDef i
  | TAElem t -> target_type_of_elem_typ t

and target_type_of_elem_array_group
  (x: elem_array_group)
: Tot target_type
= match x with
  | TAAtom t -> target_type_of_atom_array_group t
  | TAZeroOrMore t -> TTArray (target_type_of_atom_array_group t)
  | TAZeroOrOne t -> TTOption (target_type_of_atom_array_group t)
  | TAOneOrMore t -> TTNonemptyArray (target_type_of_atom_array_group t)

let rec target_type_of_array_group
  (a: array_group)
: Tot target_type
= match a with
  | [] -> TTUnit
  | (_ (* name *), t) :: q ->
    target_type_of_elem_array_group t `ttpair`
    target_type_of_array_group q

let target_type_of_table_map_group_item_entry
  (x: table_map_group_item)
: Tot target_type
= let (k, v) = x in
  (target_type_of_elem_typ k `ttpair` target_type_of_elem_typ v)

let target_type_of_table_map_group_item
  (x: table_map_group_item)
: Tot target_type
= TTArray (target_type_of_table_map_group_item_entry x)

let rec target_type_of_table_map_group
  (l: table_map_group)
: Tot target_type
= match l with
  | [] -> TTUnit
  | a :: q -> target_type_of_table_map_group_item a `ttpair`
    target_type_of_table_map_group q

let target_type_of_atom_struct_map_group
  (x: atom_struct_map_group)
: Tot target_type
= match x with
  | TSDef name -> TTDef name
  | TSEntry _ _ (* key *) value -> target_type_of_elem_typ value

let target_type_of_maybe_atom_struct_map_group
  (x: maybe_atom_struct_map_group)
: Tot target_type
= let (kd, x') = x in
  let t' = target_type_of_atom_struct_map_group x' in
  match kd with
  | TSRequired -> t'
  | TSOptional -> TTOption t'

let rec target_type_of_elem_struct_map_group
  (x: elem_struct_map_group)
: Tot target_type
  (decreases (List.Tot.length (TStructConcat?._0 x)))
= match TStructConcat?._0 x with
  | [] -> TTUnit
  | a :: q -> target_type_of_maybe_atom_struct_map_group a `ttpair`
    target_type_of_elem_struct_map_group (TStructConcat q)

let rec target_type_of_struct_map_group
  (x: struct_map_group)
: Tot target_type
  (decreases (List.Tot.length (TStructChoice?._0 x)))
= match TStructChoice?._0 x with
  | [] -> TTUnit (* dummy *)
  | [a] -> target_type_of_elem_struct_map_group a
  | a :: q -> target_type_of_elem_struct_map_group a `TTUnion`
    target_type_of_struct_map_group (TStructChoice q)

let target_type_of_elem_map_group
  (x: elem_map_group)
: Tot target_type
= match x with
  | TMTable (TStructChoice [TStructConcat []]) t -> // table only
    target_type_of_table_map_group t
  | TMTable s _ -> // struct only, but ignore the table
    target_type_of_struct_map_group s

let rec target_type_of_choice_map_group
  (x: choice_map_group)
: Tot target_type
= match x with
  | [] -> TTUnit (* dummy *)
  | [a] -> TTDef a
  | a :: q -> TTDef a `TTUnion` target_type_of_choice_map_group q

let target_type_of_map_group
  (x: map_group)
: Tot target_type
= match x with
  | TMapElem e -> target_type_of_elem_map_group e
  | TMapChoice l -> target_type_of_choice_map_group l

let rec target_type_of_choice_typ
  (l: list elem_typ)
: Tot target_type
= match l with
  | [] -> TTUnit (* dummy *)
  | [a] -> target_type_of_elem_typ a
  | a :: q -> target_type_of_elem_typ a `TTUnion`
    target_type_of_choice_typ q

let target_type_of_typ
  (t: typ)
: Tot target_type
= match t with
  | TElem t -> target_type_of_elem_typ t
  | TChoice l -> target_type_of_choice_typ l
  | TTag _ t -> target_type_of_elem_typ t
  | TEscapeHatch _ -> TTUnit (* ignore non-realizable types *)
  | TArray a -> target_type_of_array_group a
  | TMap m -> target_type_of_map_group m

let rec target_type_of_elem_typ_bounded
  (b: name_env)
  (x: elem_typ)
: Lemma
  (requires elem_typ_bounded b x)
  (ensures target_type_bounded b (target_type_of_elem_typ x))
  [SMTPat (target_type_bounded b (target_type_of_elem_typ x))]
= match x with
  | TElemArray s -> target_type_of_elem_array_group_bounded b s
  | _ -> ()

and target_type_of_atom_array_group_bounded
  (b: name_env)
  (x: atom_array_group)
: Lemma
  (requires atom_array_group_bounded b x)
  (ensures target_type_bounded b (target_type_of_atom_array_group x))
  [SMTPat (target_type_bounded b (target_type_of_atom_array_group x))]
= match x with
  | TAElem t -> target_type_of_elem_typ_bounded b t
  | _ -> ()

and target_type_of_elem_array_group_bounded
  (b: name_env)
  (x: elem_array_group)
: Lemma
  (requires elem_array_group_bounded b x)
  (ensures target_type_bounded b (target_type_of_elem_array_group x))
  [SMTPat (target_type_bounded b (target_type_of_elem_array_group x))]
= match x with
  | TAAtom t
  | TAZeroOrMore t
  | TAZeroOrOne t
  | TAOneOrMore t
  -> target_type_of_atom_array_group_bounded b t

let rec target_type_of_array_group_bounded
  (b: name_env)
  (x: array_group)
: Lemma
  (requires array_group_bounded b x)
  (ensures target_type_bounded b (target_type_of_array_group x))
  [SMTPat (target_type_bounded b (target_type_of_array_group x))]
= match x with
  | [] -> ()
  | (_, t) :: q ->
    target_type_of_elem_array_group_bounded b t;
    target_type_of_array_group_bounded b q

let target_type_of_table_map_group_item_bounded
  (b: name_env)
  (x: table_map_group_item)
: Lemma
  (requires table_map_group_item_bounded b x)
  (ensures target_type_bounded b (target_type_of_table_map_group_item x))
= ()

let rec target_type_of_table_map_group_bounded
  (b: name_env)
  (x: table_map_group)
: Lemma
  (requires table_map_group_bounded b x)
  (ensures target_type_bounded b (target_type_of_table_map_group x))
  [SMTPat (target_type_bounded b (target_type_of_table_map_group x))]
= match x with
  | [] -> ()
  | a :: q -> target_type_of_table_map_group_bounded b q

let target_type_of_atom_struct_map_group_bounded
  (b: name_env)
  (x: atom_struct_map_group)
: Lemma
  (requires atom_struct_map_group_bounded b x)
  (ensures target_type_bounded b (target_type_of_atom_struct_map_group x))
= ()

let target_type_of_maybe_atom_struct_map_group_bounded
  (b: name_env)
  (x: maybe_atom_struct_map_group)
: Lemma
  (requires maybe_atom_struct_map_group_bounded b x)
  (ensures target_type_bounded b (target_type_of_maybe_atom_struct_map_group x))
= ()

let rec target_type_of_elem_struct_map_group_bounded
  (b: name_env)
  (x: elem_struct_map_group)
: Lemma
  (requires elem_struct_map_group_bounded b x)
  (ensures target_type_bounded b (target_type_of_elem_struct_map_group x))
  (decreases (TStructConcat?._0 x))
  [SMTPat (target_type_bounded b (target_type_of_elem_struct_map_group x))]
= match TStructConcat?._0 x with
  | [] -> ()
  | a :: q -> target_type_of_elem_struct_map_group_bounded b (TStructConcat q)

let rec target_type_of_struct_map_group_bounded
  (b: name_env)
  (x: struct_map_group)
: Lemma
  (requires struct_map_group_bounded b x)
  (ensures target_type_bounded b (target_type_of_struct_map_group x))
  (decreases (TStructChoice?._0 x))
  [SMTPat (target_type_bounded b (target_type_of_struct_map_group x))]
= match TStructChoice?._0 x with
  | [] -> ()
  | a :: q -> target_type_of_struct_map_group_bounded b (TStructChoice q)

let rec target_type_of_choice_map_group_bounded
  (b: name_env)
  (x: choice_map_group)
: Lemma
  (requires choice_map_group_bounded b x)
  (ensures target_type_bounded b (target_type_of_choice_map_group x))
  [SMTPat (target_type_bounded b (target_type_of_choice_map_group x))]
= match x with
  | [] -> ()
  | a :: q -> target_type_of_choice_map_group_bounded b q

let target_type_of_map_group_bounded
  (b: name_env)
  (x: map_group)
: Lemma
  (requires map_group_bounded b x)
  (ensures target_type_bounded b (target_type_of_map_group x))
  [SMTPat (target_type_bounded b (target_type_of_map_group x))]
= ()

let rec target_type_of_choice_typ_bounded
  (b: name_env)
  (x: list elem_typ)
: Lemma
  (requires typ_bounded b (TChoice x))
  (ensures target_type_bounded b (target_type_of_choice_typ x))
  [SMTPat (target_type_bounded b (target_type_of_choice_typ x))]
= match x with
  | [] -> ()
  | a :: q -> target_type_of_choice_typ_bounded b q

let target_type_of_typ_bounded
  (b: name_env)
  (x: typ)
: Lemma
  (requires typ_bounded b x)
  (ensures target_type_bounded b (target_type_of_typ x))
  [SMTPat (target_type_bounded b (target_type_of_typ x))]
= ()

(* Serializability condition needed because array and map sizes are bounded *)

noeq
type target_spec_size_env (b: name_env) = {
  tss_env: target_spec_env b;
  tss_array_size: (n: name b) -> (x: tss_env n) -> Tot nat;
  tss_map_size: (n: name b) -> (x: tss_env n) -> Tot nat;
}

let array_size_of_atom_array_group
  (b: name_env)
  (env: target_spec_size_env b)
  (t: atom_array_group { atom_array_group_bounded b t })
  (x: target_type_sem b env.tss_env (target_type_of_atom_array_group t))
: Tot nat
= match t with
  | TADef s -> env.tss_array_size s x
  | TAElem _ -> 1

let rec array_size_of_atom_array_group_list
  (b: name_env)
  (env: target_spec_size_env b)
  (t: atom_array_group { atom_array_group_bounded b t })
  (x: list (target_type_sem b env.tss_env (target_type_of_atom_array_group t)))
: Tot nat
= match x with
  | [] -> 0
  | a :: q -> array_size_of_atom_array_group b env t a +
    array_size_of_atom_array_group_list b env t q

let array_size_of_elem_array_group
  (b: name_env)
  (env: target_spec_size_env b)
  (t: elem_array_group { elem_array_group_bounded b t })
  (x: target_type_sem b env.tss_env (target_type_of_elem_array_group t))
: Tot nat
= match t with
  | TAAtom t -> array_size_of_atom_array_group b env t x
  | TAZeroOrMore t
  | TAOneOrMore t -> array_size_of_atom_array_group_list b env t x
  | TAZeroOrOne t ->
    let x' : option (target_type_sem b env.tss_env (target_type_of_atom_array_group t)) = x in
    begin match x' with
    | None -> 0
    | Some y -> array_size_of_atom_array_group b env t y
    end

let rec array_size_of_array_group
  (b: name_env)
  (env: target_spec_size_env b)
  (t: array_group { array_group_bounded b t })
  (x: target_type_sem b env.tss_env (target_type_of_array_group t))
: Tot nat
= match t with
  | [] -> 0
  | (_, a) :: q ->
    let (hd, tl) = destruct_ttpair b env.tss_env (target_type_of_elem_array_group a) (target_type_of_array_group q) x in
    array_size_of_elem_array_group b env a hd +
    array_size_of_array_group b env q tl

(* for struct map groups, the size condition is static, based on the total number of struct rules, but for table map groups, we need to bound the sum of the sizes of all tables in a given map group. *)
let rec map_size_of_table_map_group
  (b: name_env)
  (env: target_spec_size_env b)
  (t: table_map_group { table_map_group_bounded b t })
  (x: target_type_sem b env.tss_env (target_type_of_table_map_group t))
: Tot nat
= match t with
  | [] -> 0
  | a :: q ->
    let (hd, tl) = destruct_ttpair b env.tss_env (target_type_of_table_map_group_item a) (target_type_of_table_map_group q) x in
    let (k, v) = a in
    let hd' : list (target_type_sem b env.tss_env (target_type_of_elem_typ k `ttpair` target_type_of_elem_typ v)) = hd in
    List.Tot.length hd' + map_size_of_table_map_group b env q tl

let rec map_size_of_choice_map_group
  (b: name_env)
  (env: target_spec_size_env b)
  (t: choice_map_group { choice_map_group_bounded b t })
  (x: target_type_sem b env.tss_env (target_type_of_choice_map_group t))
: Tot nat
= match t with
  | [] -> 0
  | [a] -> env.tss_map_size a x
  | a :: q ->
    let x' : either (env.tss_env a) (target_type_sem b env.tss_env (target_type_of_choice_map_group q)) = x in
    match x' with
    | Inl v -> env.tss_map_size a v
    | Inr v -> map_size_of_choice_map_group b env q v

let map_size_of_elem_map_group
  (b: name_env)
  (env: target_spec_size_env b)
  (t: elem_map_group { elem_map_group_bounded b t })
: Tot (target_type_sem b env.tss_env (target_type_of_elem_map_group t) -> nat)
= match t with
  | TMTable (TStructChoice [TStructConcat []]) t ->
    map_size_of_table_map_group b env t
  | TMTable _ _ -> fun _ -> 0 // table is ignored, size condition is static on the struct

let map_size_of_map_group
  (b: name_env)
  (env: target_spec_size_env b)
  (t: map_group { map_group_bounded b t })
: Tot (target_type_sem b env.tss_env (target_type_of_map_group t) -> nat)
= match t with
  | TMapElem e -> map_size_of_elem_map_group b env e
  | TMapChoice c -> map_size_of_choice_map_group b env c

(* Summary of serializability conditions *)

noeq
type wf_target_spec_env (b: name_env) = {
  wft_env: target_spec_size_env b;
  wft_serializable: (n: name b) -> (x: wft_env.tss_env n) -> Tot prop;
}

let rec elem_typ_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b)
  (t: elem_typ { elem_typ_bounded b t })
: Tot (target_type_sem b env.wft_env.tss_env (target_type_of_elem_typ t) -> prop)
  (decreases t)
= fun x ->
  match t with
  | TDef n -> env.wft_serializable n x
  | TElemArray s ->
    array_size_of_elem_array_group b env.wft_env s x < pow2 64 /\
    elem_array_group_target_spec_value_serializable b env s x
  | _ -> true

and atom_array_group_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b)
  (t: atom_array_group { atom_array_group_bounded b t })
: Tot (target_type_sem b env.wft_env.tss_env (target_type_of_atom_array_group t) -> prop)
  (decreases t)
= fun x ->
  match t with
  | TADef s -> env.wft_serializable s x
  | TAElem t' -> elem_typ_target_spec_value_serializable b env t' x

and elem_array_group_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b)
  (t: elem_array_group { elem_array_group_bounded b t })
: Tot (target_type_sem b env.wft_env.tss_env (target_type_of_elem_array_group t) -> prop)
  (decreases t)
= fun x ->
  match t with
  | TAAtom t -> atom_array_group_target_spec_value_serializable b env t x
  | TAZeroOrMore t -> forall elt . List.Tot.memP elt x ==> (atom_array_group_target_spec_value_serializable b env t) elt
  | TAOneOrMore t -> forall elt . List.Tot.memP elt x ==> (atom_array_group_target_spec_value_serializable b env t) elt
  | TAZeroOrOne t ->
    let x' : option (target_type_sem b env.wft_env.tss_env (target_type_of_atom_array_group t)) = x in
    begin match x' with
    | None -> True
    | Some y -> atom_array_group_target_spec_value_serializable b env t y
    end

let rec array_group_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b)
  (t: array_group { array_group_bounded b t })
: Tot (target_type_sem b env.wft_env.tss_env (target_type_of_array_group t) -> prop)
  (decreases t)
= fun x ->
  match t with
  | [] -> true
  | (_, a) :: q ->
    let (hd, tl) = destruct_ttpair b env.wft_env.tss_env (target_type_of_elem_array_group a) (target_type_of_array_group q) x in
    elem_array_group_target_spec_value_serializable b env a hd /\
    array_group_target_spec_value_serializable b env q tl

let table_map_group_item_target_spec_value_entry_serializable
  (b: name_env)
  (env: wf_target_spec_env b)
  (t: table_map_group_item { table_map_group_item_bounded b t })
  (x: target_type_sem b env.wft_env.tss_env (target_type_of_table_map_group_item_entry t))
: Tot prop
= let (k, v) = t in
  let (hd, tl) = destruct_ttpair b env.wft_env.tss_env (target_type_of_elem_typ k) (target_type_of_elem_typ v) x in
  elem_typ_target_spec_value_serializable b env k hd /\
  elem_typ_target_spec_value_serializable b env v tl

let table_map_group_item_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b)
  (t: table_map_group_item { table_map_group_item_bounded b t })
  (x: target_type_sem b env.wft_env.tss_env (target_type_of_table_map_group_item t))
: Tot prop
= (forall elt . List.Tot.memP elt x ==> (table_map_group_item_target_spec_value_entry_serializable b env t) elt) /\
  List.Tot.no_repeats_p (List.Tot.map (ttpair_fst b env.wft_env.tss_env (target_type_of_elem_typ (fst t)) (target_type_of_elem_typ (snd t))) x) // THIS is the reason why the serializability predicate is in prop instead of bool
  // TODO: if we ever allow serializing tables along with structs within the same map, we should also add struct-table disjointness conditions here

let rec table_map_group_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b) 
  (l: table_map_group { table_map_group_bounded b l })
: Tot (target_type_sem b env.wft_env.tss_env (target_type_of_table_map_group l) -> prop)
= fun x ->
  match l with
  | [] -> True
  | a :: q ->
    let (hd, tl) = destruct_ttpair b env.wft_env.tss_env (target_type_of_table_map_group_item a) (target_type_of_table_map_group q) x in
    table_map_group_item_target_spec_value_serializable b env a hd /\
    table_map_group_target_spec_value_serializable b env q tl

let atom_struct_map_group_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b) 
  (t: atom_struct_map_group { atom_struct_map_group_bounded b t })
: Tot (target_type_sem b env.wft_env.tss_env (target_type_of_atom_struct_map_group t) -> prop)
= match t with
  | TSDef name -> env.wft_serializable name
  | TSEntry _ _ (* key *) value ->
    elem_typ_target_spec_value_serializable b env value

let maybe_atom_struct_map_group_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b) 
  (t: maybe_atom_struct_map_group { maybe_atom_struct_map_group_bounded b t })
: Tot (target_type_sem b env.wft_env.tss_env (target_type_of_maybe_atom_struct_map_group t) -> prop)
= fun x ->
  let (kd, t') = t in
  match kd with
  | TSRequired -> atom_struct_map_group_target_spec_value_serializable b env t' x
  | TSOptional ->
    let x' : option (target_type_sem b env.wft_env.tss_env (target_type_of_atom_struct_map_group t')) = x in
    match x' with
    | None -> True
    | Some v -> atom_struct_map_group_target_spec_value_serializable b env t' v

let rec elem_struct_map_group_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b) 
  (t: elem_struct_map_group { elem_struct_map_group_bounded b t })
: Tot (target_type_sem b env.wft_env.tss_env (target_type_of_elem_struct_map_group t) -> prop)
  (decreases (List.Tot.length (TStructConcat?._0 t)))
= fun x ->
  match TStructConcat?._0 t with
  | [] -> True
  | a :: q ->
    let (hd, tl) = destruct_ttpair b env.wft_env.tss_env (target_type_of_maybe_atom_struct_map_group a) (target_type_of_elem_struct_map_group (TStructConcat q)) x in
    maybe_atom_struct_map_group_target_spec_value_serializable b env a hd /\
    elem_struct_map_group_target_spec_value_serializable b env (TStructConcat q) tl

let rec struct_map_group_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b) 
  (t: struct_map_group { struct_map_group_bounded b t })
: Tot (target_type_sem b env.wft_env.tss_env (target_type_of_struct_map_group t) -> prop)
  (decreases (List.Tot.length (TStructChoice?._0 t)))
= fun x ->
  match TStructChoice?._0 t with
  | [] -> False
  | [a] -> elem_struct_map_group_target_spec_value_serializable b env a x
  | a :: q ->
    let x' : either (target_type_sem b env.wft_env.tss_env (target_type_of_elem_struct_map_group a)) (target_type_sem b env.wft_env.tss_env (target_type_of_struct_map_group (TStructChoice q))) = x in
    match x' with
    | Inl v -> elem_struct_map_group_target_spec_value_serializable b env a v
    | Inr v -> struct_map_group_target_spec_value_serializable b env (TStructChoice q) v
    
let elem_map_group_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b) 
  (t: elem_map_group { elem_map_group_bounded b t })
: Tot (target_type_sem b env.wft_env.tss_env (target_type_of_elem_map_group t) -> prop)
= match t with
  | TMTable (TStructChoice [TStructConcat []]) t -> // table only
    table_map_group_target_spec_value_serializable b env t
  | TMTable s _ -> // struct only, but ignore the table
    struct_map_group_target_spec_value_serializable b env s

let rec choice_map_group_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b) 
  (t: choice_map_group { choice_map_group_bounded b t })
: Tot (target_type_sem b env.wft_env.tss_env (target_type_of_choice_map_group t) -> prop)
= fun x ->
  match t with
  | [] -> False
  | [a] -> env.wft_serializable a x
  | a :: q ->
    let x' : either (env.wft_env.tss_env a) (target_type_sem b env.wft_env.tss_env (target_type_of_choice_map_group q)) = x in
    match x' with
    | Inl v -> env.wft_serializable a v
    | Inr v -> choice_map_group_target_spec_value_serializable b env q v

let map_group_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b) 
  (t: map_group { map_group_bounded b t })
  (x: target_type_sem b env.wft_env.tss_env (target_type_of_map_group t))
: Tot prop
= map_size_of_map_group b env.wft_env t x < pow2 64 /\
  begin match t with
  | TMapElem e -> elem_map_group_target_spec_value_serializable b env e x
  | TMapChoice l -> choice_map_group_target_spec_value_serializable b env l x
  end

let rec choice_typ_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b) 
  (l: list elem_typ { sem_typ_choice_bounded b l })
: Tot (target_type_sem b env.wft_env.tss_env (target_type_of_choice_typ l) -> prop)
= fun x -> match l with
  | [] -> False
  | [a] -> elem_typ_target_spec_value_serializable b env a x
  | a :: q ->
    let x' : either (target_type_sem b env.wft_env.tss_env (target_type_of_elem_typ a)) (target_type_sem b env.wft_env.tss_env (target_type_of_choice_typ q)) = x in
    match x' with
    | Inl v -> elem_typ_target_spec_value_serializable b env a v
    | Inr v -> choice_typ_target_spec_value_serializable b env q v

let typ_target_spec_value_serializable
  (b: name_env)
  (env: wf_target_spec_env b) 
  (t: typ { typ_bounded b t })
: Tot (target_type_sem b env.wft_env.tss_env (target_type_of_typ t) -> prop)
= match t with
  | TElem t -> elem_typ_target_spec_value_serializable b env t
  | TChoice l -> choice_typ_target_spec_value_serializable b env l
  | TTag _ t -> elem_typ_target_spec_value_serializable b env t
  | TEscapeHatch _ -> (fun _ -> False) (* ignore non-realizable types *)
  | TArray a -> array_group_target_spec_value_serializable b env a
  | TMap m -> map_group_target_spec_value_serializable b env m

let mk_refinement (#t: Type) (p: t -> prop) = (x: t { p x })

let serializable_target_spec_typ
  (b: name_env)
  (env: wf_target_spec_env b) 
  (t: typ { typ_bounded b t })
: Tot Type
= mk_refinement (typ_target_spec_value_serializable b env t)

let serializable_target_spec_array_group
  (b: name_env)
  (env: wf_target_spec_env b) 
  (t: array_group { array_group_bounded b t })
: Tot Type
= mk_refinement (array_group_target_spec_value_serializable b env t)

let serializable_target_spec_map_group
  (b: name_env)
  (env: wf_target_spec_env b) 
  (t: map_group { map_group_bounded b t })
: Tot Type
= mk_refinement (map_group_target_spec_value_serializable b env t)

let serializable_target_spec
  (s_ast: wf_ast_env)
  (s_sz: wf_target_spec_env (s_ast.we_env.e_sem_env.se_bound))
  (n: name s_ast.we_env.e_sem_env.se_bound)
: Tot Type
= match s_ast.we_env.e_sem_env.se_env n with
  | SEType _ -> serializable_target_spec_typ _ s_sz (s_ast.we_env.e_env n)
  | SEArrayGroup _ -> serializable_target_spec_array_group _ s_sz (s_ast.we_env.e_env n)
  | SEMapGroup _ -> serializable_target_spec_map_group _ s_sz (s_ast.we_env.e_env n)

let mk_trivial_target_spec_env (b: name_env) (wft_env: target_spec_size_env b) : wf_target_spec_env b = {
  wft_env = wft_env;
  wft_serializable = (fun _ _ -> True);
}

noeq
type spec_env = {
  s_ast: wf_ast_env;
  s_sz: target_spec_size_env (s_ast.we_env.e_sem_env.se_bound);
  s_bij: (n: name s_ast.we_env.e_sem_env.se_bound) -> Spec.bijection
    (serializable_target_spec s_ast (mk_trivial_target_spec_env _ s_sz) n)
    (s_sz.tss_env n);
  s_array_size_preserved: squash (forall (n: name s_ast.we_env.e_sem_env.se_bound { SEArrayGroup? (s_ast.we_env.e_sem_env.se_env n) })
    (x: serializable_target_spec s_ast (mk_trivial_target_spec_env _ s_sz) n) .
    array_size_of_array_group _ s_sz (s_ast.we_env.e_env n) x ==
    s_sz.tss_array_size n ((s_bij n).bij_from_to x)
  );
  s_map_size_preserved: squash (forall (n: name s_ast.we_env.e_sem_env.se_bound { SEMapGroup? (s_ast.we_env.e_sem_env.se_env n) })
    (x: serializable_target_spec s_ast (mk_trivial_target_spec_env _ s_sz) n) .
    map_size_of_map_group _ s_sz (s_ast.we_env.e_env n) x ==
    s_sz.tss_map_size n ((s_bij n).bij_from_to x)
  );
}
