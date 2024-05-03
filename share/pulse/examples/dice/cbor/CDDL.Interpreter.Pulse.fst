module CDDL.Interpreter.Pulse
include CDDL.Interpreter.AST

module Spec = CDDL.Spec
module CP = CDDL.Pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Stick
open Pulse.Lib.SeqMatch

module U8 = FStar.UInt8
module A = Pulse.Lib.Array
module U64 = FStar.UInt64

let impl_elem_type_sem
  (t: target_elem_type)
: Tot Type0
= match t with
  | TTSimple -> CBOR.Spec.simple_value
  | TTUInt64 -> U64.t
  | TTUnit -> unit
  | TTBool -> bool
  | TTString -> A.array U8.t
  | TTAny -> CBOR.Pulse.cbor
  | TTAlwaysFalse -> squash False

let impl_table (key value: Type) = A.array (key & value)

let rec impl_type_sem
  (#bound: name_env)
  (env: target_spec_env bound)
  (t: target_type)
: Pure Type0
  (requires target_type_bounded bound t)
  (ensures fun _ -> True)
= match t with
  | TTDef s -> env s
  | TTPair t1 t2 -> impl_type_sem env t1 & impl_type_sem env t2
  | TTUnion t1 t2 -> impl_type_sem env t1 `either` impl_type_sem env t2
  | TTArray a -> A.array (impl_type_sem env a)
  | TTTable t1 t2 -> impl_table (impl_type_sem env t1) (impl_type_sem env t2)
  | TTOption a -> option (impl_type_sem env a)
  | TTElem e -> impl_elem_type_sem e

let impl_type_sem_incr
  (#bound: name_env)
  (env: target_spec_env bound)
  (#bound': name_env)
  (env': target_spec_env bound')
  (t: target_type)
: Lemma
  (requires target_type_bounded bound t /\
    target_spec_env_included env env'
  )
  (ensures
    target_type_bounded bound' t /\
    impl_type_sem env' t == impl_type_sem env t
  )
  [SMTPatOr [
    [SMTPat (target_spec_env_included env env'); SMTPat (impl_type_sem env t)];
    [SMTPat (target_spec_env_included env env'); SMTPat (impl_type_sem env' t)];
  ]]
= admit ()

noeq
type impl_env
    (#bound: name_env)
    (high: target_spec_env bound)
=   {
        i_low: target_spec_env bound;
        i_r: (n: name bound) -> i_low n -> high n -> vprop;
    }

let impl_env_included
    (#bound: name_env)
    (#high: target_spec_env bound)
    (env: impl_env high)
    (#bound': name_env)
    (#high': target_spec_env bound')
    (env': impl_env high')
: Tot prop
= target_spec_env_included high high' /\
  target_spec_env_included env.i_low env'.i_low /\
  (forall (n: name bound) . env.i_r n == env'.i_r n)

let impl_rel_pure
    (t: Type)
    (x y: t)
: vprop
= pure (x == y)

let impl_rel_scalar_array
  (t: Type)
  (r: A.array t)
  (x: Seq.seq t)
: Tot vprop
= A.pts_to r x

let impl_rel_array_of_list
  (#low #high: Type)
  (r: low -> high -> vprop)
  (x: A.array low)
  (y: list high)
: vprop
= exists* s . A.pts_to x s ** seq_list_match s y r

```pulse
ghost
fn rec seq_list_match_pure_elim
  (#t: Type0)
  (s: Seq.seq t)
  (l: list t)
requires
  seq_list_match s l (impl_rel_pure _)
ensures
  pure (s `Seq.equal` Seq.seq_of_list l)
decreases l
{
  seq_list_match_length  (impl_rel_pure t) s l;
  if (Nil? l) {
    seq_list_match_nil_elim s l (impl_rel_pure _)
  } else {
    let _ = seq_list_match_cons_elim s l (impl_rel_pure _);
    unfold (impl_rel_pure _ (Seq.head s) (List.Tot.hd l));
    seq_list_match_pure_elim (Seq.tail s) (List.Tot.tl l)
  }
}
```

```pulse
ghost
fn rec seq_list_match_pure_intro
  (#t: Type0)
  (s: Seq.seq t)
  (l: list t)
requires
  pure (s `Seq.equal` Seq.seq_of_list l)  
ensures
  seq_list_match s l (impl_rel_pure _)
decreases l
{
  if (Nil? l) {
    seq_list_match_nil_intro s l (impl_rel_pure _)
  } else {
    fold (impl_rel_pure _ (Seq.head s) (List.Tot.hd l));
    seq_list_match_pure_intro (Seq.tail s) (List.Tot.tl l);
    seq_list_match_cons_intro (Seq.head s) (List.Tot.hd l) (Seq.tail s) (List.Tot.tl l) (impl_rel_pure _);
    rewrite (seq_list_match 
      (Seq.head s `Seq.cons` Seq.tail s) (List.Tot.hd l :: List.Tot.tl l) (impl_rel_pure _)
    ) as (seq_list_match s l (impl_rel_pure _))
  }
}
```

let impl_rel_elem
    (t: target_elem_type)
: impl_elem_type_sem t -> target_elem_type_sem t -> vprop
= match t with
  | TTSimple
  | TTUInt64
  | TTUnit
  | TTBool
  | TTAlwaysFalse -> impl_rel_pure _
  | TTString -> impl_rel_scalar_array U8.t
  | TTAny -> CP.raw_data_item_match 1.0R

let impl_rel_pair
  (#low1 #high1: Type)
  (r1: low1 -> high1 -> vprop)
  (#low2 #high2: Type)
  (r2: low2 -> high2 -> vprop)
  (xlow: (low1 & low2)) (xhigh: (high1 & high2))
: vprop
= r1 (fst xlow) (fst xhigh) ** r2 (snd xlow) (snd xhigh)

let impl_rel_either
  (#low1 #high1: Type)
  (r1: low1 -> high1 -> vprop)
  (#low2 #high2: Type)
  (r2: low2 -> high2 -> vprop)
  (xlow: (low1 `either` low2)) (xhigh: (high1 `either` high2))
: vprop
= match xlow, xhigh with
| Inl xl, Inl xh -> r1 xl xh
| Inr xl, Inr xh -> r2 xl xh
| _ -> pure False

let impl_rel_option
  (#low #high: Type)
  (r: low -> high -> vprop)
  (x: option low)
  (y: option high)
: vprop
= match x, y with
  | Some x', Some y' -> r x' y'
  | None, None -> emp
  | _ -> pure False

let rec impl_rel
    (#bound: name_env)
    (#high: target_spec_env bound)
    (env: impl_env high)
    (t: target_type {target_type_bounded bound t})
: impl_type_sem env.i_low t -> target_type_sem high t -> vprop
= match t with
  | TTDef s -> env.i_r s
  | TTElem e -> impl_rel_elem e
  | TTPair t1 t2 -> impl_rel_pair (impl_rel env t1) (impl_rel env t2)
  | TTUnion t1 t2 -> impl_rel_either (impl_rel env t1) (impl_rel env t2)
  | TTArray a -> impl_rel_array_of_list (impl_rel env a)
  | TTTable t1 t2 -> impl_rel_array_of_list (impl_rel_pair (impl_rel env t1) (impl_rel env t2))
  | TTOption a -> impl_rel_option (impl_rel env a)

let impl_rel_incr
    (#bound: name_env)
    (#high: target_spec_env bound)
    (env: impl_env high)
    (#bound': name_env)
    (#high': target_spec_env bound')
    (env': impl_env high')
    (t: target_type {target_type_bounded bound t})
: Lemma
  (requires impl_env_included env env')
  (ensures impl_rel env' t == impl_rel env t)
  [SMTPatOr [
    [SMTPat (impl_rel env t); SMTPat (impl_env_included env env')];
    [SMTPat (impl_rel env' t); SMTPat (impl_env_included env env')];
  ]]
= admit ()

let impl_rel_bij_l
  (#left #right: Type)
  (r: left -> right -> vprop)
  (#left': Type)
  (bij: Spec.bijection left left')
  (x: left')
  (y: right)
: vprop
= r (bij.bij_to_from x) y

let impl_rel_bij_r
  (#left #right: Type)
  (r: left -> right -> vprop)
  (#right': Type)
  (bij: Spec.bijection right right')
  (x: left)
  (y: right')
: vprop
= r x (bij.bij_to_from y)

inline_for_extraction [@@noextract_to "krml"]
noeq
type total_env = {
  te_ast: target_ast_env;
  te_spec: spec_env (te_ast.ta_ast.e_sem_env) (te_ast.ta_tgt);
  te_impl_typ: impl_env te_ast.ta_tgt.wft_env.tss_env;
(*
  te_impl_bij: (n: name te_ast.ta_ast.e_sem_env.se_bound) -> Spec.bijection
    (target_type_sem te_impl_typ.i_low (target_type_of_wf_ast_elem (te_ast.ta_ast.e_env n) (Some?.v (te_ast.ta_ast.e_wf n))))
    (te_impl_typ.i_low n);
*)
  te_impl_validate: (n: typ_name te_ast.ta_ast.e_sem_env.se_bound) ->
    CP.impl_typ #None (te_ast.ta_ast.e_sem_env.se_env n);
  te_impl_parse: (n: typ_name te_ast.ta_ast.e_sem_env.se_bound) ->
    CP.impl_parse
      (te_spec.tp_spec_typ n).parser
      (te_impl_typ.i_r n)
     ;
  te_impl_serialize: (n: typ_name te_ast.ta_ast.e_sem_env.se_bound) ->
    CP.impl_serialize
      (te_spec.tp_spec_typ n).serializer
      (te_impl_typ.i_r n)
     ;
}
