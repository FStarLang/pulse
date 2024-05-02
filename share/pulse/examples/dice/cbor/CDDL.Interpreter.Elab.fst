module CDDL.Interpreter.Elab
include CDDL.Interpreter.AST
module Spec = CDDL.Spec
module U64 = FStar.UInt64
module MapSpec = CDDL.Spec.MapGroupGen

(* Rewriting *)

[@@ sem_attr]
let rec map_group_is_productive
  (g: group NMapGroup)
: Tot bool
= match g with
  | GOneOrMore g' -> map_group_is_productive g'
  | GAlwaysFalse
  | GMapElem _ _ _ _ -> true
  | GNop
  | GZeroOrOne _
  | GZeroOrMore _ -> false
  | GChoice g1 g2 -> map_group_is_productive g1 && map_group_is_productive g2
  | GConcat g1 g2 -> map_group_is_productive g1 || map_group_is_productive g2

let rec map_group_is_productive_correct
  (env: sem_env)
  (g: group NMapGroup)
: Lemma
  (requires (
    group_bounded NMapGroup env.se_bound g /\
    map_group_is_productive g == true
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
    if map_group_is_productive g1
    then map_group_is_productive_correct env g1
    else map_group_is_productive_correct env g2
  | _ -> ()

[@@ sem_attr]
let rec rewrite_typ
  (fuel: nat)
  (t: typ)
: Tot typ
= if fuel = 0
  then t
  else let fuel' : nat = fuel - 1 in
  match t with
  | TChoice (TChoice t1 t2) t3 -> rewrite_typ fuel' (TChoice t1 (TChoice t2 t3))
  | TChoice t (TElem EAlwaysFalse)
  | TChoice (TElem EAlwaysFalse) t
    -> rewrite_typ fuel' t
  | TChoice t1 t2 ->
    let t' = TChoice (rewrite_typ fuel' t1) (rewrite_typ fuel' t2) in
    if t' = t
    then t'
    else rewrite_typ fuel' t'
  | TArray g -> TArray (rewrite_group fuel' NArrayGroup g)
  | TMap g -> TMap (rewrite_group fuel' NMapGroup g)
  | _ -> t

and rewrite_group
  (fuel: nat)
  (kind: name_env_elem)
  (g: group kind)
: Tot (group kind)
= if fuel = 0
  then g
  else let fuel' : nat = fuel - 1 in
  match g with
  | GConcat GAlwaysFalse _ -> GAlwaysFalse
  | GConcat GNop g -> rewrite_group fuel' kind g
  | GConcat g GNop -> rewrite_group fuel' kind g
  | GConcat (GConcat t1 t2) t3 -> rewrite_group fuel' kind (GConcat t1 (GConcat t2 t3))
  | GConcat t1 t2 ->
    let g' = GConcat (rewrite_group fuel' kind t1) (rewrite_group fuel' kind t2) in
    if g' = g
    then g'
    else rewrite_group fuel' kind g'
  | GChoice GAlwaysFalse g -> rewrite_group fuel' kind g
  | GChoice g GAlwaysFalse -> rewrite_group fuel' kind g
  | GChoice (GChoice t1 t2) t3 -> rewrite_group fuel' kind (GChoice t1 (GChoice t2 t3))
  | GChoice t1 t2 ->
    let g' = GChoice (rewrite_group fuel' kind t1) (rewrite_group fuel' kind t2) in
    if g' = g
    then g'
    else rewrite_group fuel' kind g'
  | GZeroOrMore (GMapElem sq cut (TElem (ELiteral key)) value) ->
    rewrite_group fuel' kind (GZeroOrOne (GMapElem sq cut (TElem (ELiteral key)) value))
  | GZeroOrMore (GChoice (GMapElem sq cut key value) g') ->
    if map_group_is_productive g'
    then rewrite_group fuel' kind (GConcat (GZeroOrMore (GMapElem sq cut key value)) (GZeroOrMore g'))
    else g
  | GZeroOrMore g1 -> 
    let g' = GZeroOrMore (rewrite_group fuel' kind g1) in
    if g' = g
    then g'
    else rewrite_group fuel' kind g'
  | GZeroOrOne g -> GZeroOrOne (rewrite_group fuel' kind g)
  | GOneOrMore g -> GOneOrMore (rewrite_group fuel' kind g)
  | GArrayElem sq ty -> GArrayElem sq (rewrite_typ fuel' ty)
  | GMapElem sq cut key value -> GMapElem sq cut (rewrite_typ fuel' key) (rewrite_typ fuel' value)
  | GDef sq n -> GDef sq n
  | GAlwaysFalse -> GAlwaysFalse
  | GNop -> GNop

#push-options "--z3rlimit 32"

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
    let t' = rewrite_typ fuel t in
    typ_bounded env.se_bound t' /\
    Spec.typ_equiv (typ_sem env t) (typ_sem env t')
  ))
  (decreases fuel)
  [SMTPat (typ_sem env (rewrite_typ fuel t))]
= if fuel = 0
  then ()
  else let fuel' : nat = fuel - 1 in
  match t with
  | TChoice (TChoice t1 t2) t3 ->
    rewrite_typ_correct env fuel' (TChoice t1 (TChoice t2 t3))
  | TChoice t (TElem EAlwaysFalse)
  | TChoice (TElem EAlwaysFalse) t
    -> rewrite_typ_correct env fuel' t
  | TChoice t1 t2 ->
    rewrite_typ_correct env fuel' t1;
    rewrite_typ_correct env fuel' t2;
    rewrite_typ_correct env fuel' (TChoice (rewrite_typ fuel' t1) (rewrite_typ fuel' t2))
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
    let t' = rewrite_group fuel kind t in
    group_bounded kind env.se_bound t' /\
    begin match kind with
    | NArrayGroup -> Spec.array_group3_equiv (array_group_sem env t) (array_group_sem env t')
    | NMapGroup -> map_group_sem env t == map_group_sem env t'
    | _ -> True
    end
  ))
  (decreases fuel)
  [SMTPatOr [
    [SMTPat (map_group_sem env (rewrite_group fuel kind t))];
    [SMTPat (array_group_sem env (rewrite_group fuel kind t))];
  ]]
= if fuel = 0
  then ()
  else let fuel' : nat = fuel - 1 in
  match t with
  | GConcat GAlwaysFalse _ -> ()
  | GConcat GNop g -> rewrite_group_correct env fuel' g
  | GConcat g GNop -> rewrite_group_correct env fuel' g
  | GConcat (GConcat t1 t2) t3 ->
    rewrite_group_correct env fuel' (GConcat t1 (GConcat t2 t3))
  | GConcat t1 t2 ->
    let t1' = rewrite_group fuel' kind t1 in
    let t2' = rewrite_group fuel' kind t2 in
    rewrite_group_correct env fuel' t1;
    rewrite_group_correct env fuel' t2;
    rewrite_group_correct env fuel' (GConcat t1' t2');
    begin match kind with
    | NArrayGroup -> Spec.array_group3_concat_equiv (array_group_sem env t1) (array_group_sem env t1') (array_group_sem env t2) (array_group_sem env t2')
    | _ -> ()
    end
  | GChoice GAlwaysFalse g -> rewrite_group_correct env fuel' g
  | GChoice g GAlwaysFalse -> rewrite_group_correct env fuel' g
  | GChoice (GChoice t1 t2) t3 ->
    rewrite_group_correct env fuel' (GChoice t1 (GChoice t2 t3))
  | GChoice t1 t2 ->
    let t1' = rewrite_group fuel' kind t1 in
    let t2' = rewrite_group fuel' kind t2 in
    rewrite_group_correct env fuel' t1;
    rewrite_group_correct env fuel' t2;
    rewrite_group_correct env fuel' (GChoice t1' t2')
  | GZeroOrMore (GMapElem sq cut (TElem (ELiteral key)) value) ->
    MapSpec.map_group_zero_or_more_map_group_match_item_for cut (eval_literal key) (typ_sem env value);
    rewrite_group_correct env fuel' (GZeroOrOne (GMapElem sq cut (TElem (ELiteral key)) value))
  | GZeroOrMore (GChoice (GMapElem sq cut key value) g') ->
    if map_group_is_productive g'
    then begin
      map_group_is_productive_correct env g';
      MapSpec.map_group_zero_or_more_choice (MapSpec.map_group_match_item cut (typ_sem env key) (typ_sem env value)) (map_group_sem env g');
      rewrite_group_correct env fuel' (GConcat (GZeroOrMore (GMapElem sq cut key value)) (GZeroOrMore g'))
    end
  | GZeroOrOne g1 ->
    rewrite_group_correct env fuel' g1
  | GZeroOrMore g1 ->
    rewrite_group_correct env fuel' g1;
    let g2 = rewrite_group fuel' kind g1 in
    rewrite_group_correct env fuel' (GZeroOrMore g2);
    begin match kind with
    | NArrayGroup -> Spec.array_group3_zero_or_more_equiv (array_group_sem env g1) (array_group_sem env g2)
    | _ -> ()
    end
  | GOneOrMore g1 ->
    rewrite_group_correct env fuel' g1;
    let g2 = rewrite_group fuel' kind g1 in
    rewrite_group_correct env fuel' (GOneOrMore g2);
    begin match kind with
    | NArrayGroup -> Spec.array_group3_zero_or_more_equiv (array_group_sem env g1) (array_group_sem env g2)
    | _ -> ()
    end
  | GArrayElem sq ty ->
    rewrite_typ_correct env fuel' ty;
    Spec.array_group3_item_equiv (typ_sem env ty) (typ_sem env (rewrite_typ fuel' ty))
  | GMapElem sq cut key value ->
    rewrite_typ_correct env fuel' key;
    rewrite_typ_correct env fuel' value;
    MapSpec.map_group_match_item_ext cut (typ_sem env key) (typ_sem env value) (typ_sem env (rewrite_typ fuel' key)) (typ_sem env (rewrite_typ fuel' value))
  | GAlwaysFalse
  | GNop
  | GDef _ _ -> ()

#pop-options

(* Disjointness *)

noeq
type result (t: Type) =
| RSuccess of t
| RFailure of string
| ROutOfFuel

let destruct_group
  (#n: name_env_elem)
  (g: group n)
: Tot (group n & group n)
= match g with
  | GConcat g1 g2 -> (g1, g2)
  | _ -> (g, GNop)

let maybe_close_array_group_concat
  (close: bool)
  (a1 a2: Spec.array_group3 None)
: Lemma
  (Spec.array_group3_equiv
    (Spec.maybe_close_array_group (Spec.array_group3_concat a1 a2) close)
    (Spec.array_group3_concat a1 (Spec.maybe_close_array_group a2 close))
  )
= ()

let array_group_sem_destruct_group
  (e: sem_env)
  (g: group NArrayGroup { group_bounded _ e.se_bound g })
: Lemma
  (let (g1, g2) = destruct_group g in
    group_bounded _ e.se_bound g1 /\
    group_bounded _ e.se_bound g2 /\
    array_group_sem e g `Spec.array_group3_equiv` (array_group_sem e g1 `Spec.array_group3_concat` array_group_sem e g2)
  )
= ()

let maybe_close_array_group_sem_destruct_group
  (close: bool)
  (e: sem_env)
  (g: group NArrayGroup { group_bounded _ e.se_bound g })
: Lemma
  (let (g1, g2) = destruct_group g in
    group_bounded _ e.se_bound g1 /\
    group_bounded _ e.se_bound g2 /\
    Spec.maybe_close_array_group (array_group_sem e g) close `Spec.array_group3_equiv`
      (array_group_sem e g1 `Spec.array_group3_concat` Spec.maybe_close_array_group (array_group_sem e g2) close)
  )
  [SMTPat (Spec.maybe_close_array_group (array_group_sem e g) close)]
= ()

#restart-solver
let array_group_concat_elem_same_disjoint
  (close: bool)
  (t1 t2: Spec.typ)
  (a1 a2: Spec.array_group3 None)
: Lemma
  (requires
    Spec.typ_equiv t1 t2
  )
  (ensures (Spec.array_group3_disjoint (Spec.maybe_close_array_group a1 close) (Spec.maybe_close_array_group a2 close) ==>
    Spec.array_group3_disjoint
      (Spec.maybe_close_array_group (Spec.array_group3_concat (Spec.array_group3_item t1) a1) close)
      (Spec.maybe_close_array_group (Spec.array_group3_concat (Spec.array_group3_item t2) a2) close)
  ))
= maybe_close_array_group_concat close (Spec.array_group3_item t1) a1;
  maybe_close_array_group_concat close (Spec.array_group3_item t1) a2

#push-options "--z3rlimit 128 --query_stats --split_queries always --fuel 4 --ifuel 8"

#restart-solver
[@@"opaque_to_smt"]
let rec typ_disjoint
  (e: ast_env)
  (fuel: nat)
  (t1: typ { typ_bounded e.e_sem_env.se_bound t1 })
  (t2: typ { typ_bounded e.e_sem_env.se_bound t2 })
: Pure (result unit) // I cannot use `squash` because of unification, yet I want to shortcut disjointness symmetry
    (requires True)
    (ensures fun r -> RSuccess? r ==> Spec.typ_disjoint (typ_sem e.e_sem_env t1) (typ_sem e.e_sem_env t2))
    (decreases fuel)
= if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match t1, t2 with
  | t2, TDef i
  | TDef i, t2 ->
    let s1 = e.e_sem_env.se_env i in
    let t1' = e.e_env i in
    typ_disjoint e fuel' t1' t2
  | TElem EAlwaysFalse, _
  | _, TElem EAlwaysFalse -> RSuccess ()
  | TElem EAny, _
  | _, TElem EAny -> RFailure "typ_disjoint: EAny"
  | TChoice t1l t1r, t2
  | t2, TChoice t1l t1r ->
    let rl = typ_disjoint e fuel' t1l t2 in
    if not (RSuccess? rl)
    then rl
    else typ_disjoint e fuel' t1r t2
  | TTagged tag1 t1', TTagged tag2 t2' ->
    if tag1 = tag2
    then typ_disjoint e fuel' t1' t2'
    else RSuccess ()
  | TTagged _ _, _
  | _, TTagged _ _ -> RSuccess ()
  | TElem EBool, TElem (ELiteral (LSimple v))
  | TElem (ELiteral (LSimple v)), TElem EBool ->
    if v = Spec.simple_value_true
    then RFailure "typ_disjoint: Bool vs. simple_value_true"
    else if v = Spec.simple_value_false
    then RFailure "typ_disjoint: Bool vs. simple_value_false"
    else RSuccess ()
  | TElem (ELiteral (LString ty _)), TElem EByteString
  | TElem EByteString, TElem (ELiteral (LString ty _)) ->
    if ty = CBOR.Spec.cbor_major_type_byte_string
    then RFailure "typ_disjoint: byte string"
    else RSuccess ()
  | TElem (ELiteral (LString ty _)), TElem ETextString
  | TElem ETextString, TElem (ELiteral (LString ty _)) ->
    if ty = CBOR.Spec.cbor_major_type_text_string
    then RFailure "typ_disjoint: text string"
    else RSuccess ()
  | TElem e1, TElem e2 ->
    if e1 = e2
    then RFailure "typ_disjoint: equal elem"
    else RSuccess ()
  | TElem _, _
  | _, TElem _ -> RSuccess ()
  | TMap _, TMap _ -> RFailure "typ_disjoint: map: not supported"
  | TMap _, _
  | _, TMap _ -> RSuccess ()
  | TArray a1, TArray a2 ->
    Spec.array3_close_array_group (array_group_sem e.e_sem_env a1);
    Spec.array3_close_array_group (array_group_sem e.e_sem_env a2);
    array_group_disjoint e fuel' true a1 a2
  | TArray _, _
  | _, TArray _ -> RSuccess ()

and array_group_disjoint
  (e: ast_env)
  (fuel: nat)
  (close: bool)
  (a1: group NArrayGroup { group_bounded _ e.e_sem_env.se_bound a1 })
  (a2: group NArrayGroup { group_bounded _ e.e_sem_env.se_bound a2 })
: Pure (result unit)
    (requires True)
    (ensures fun r ->
      RSuccess? r ==> Spec.array_group3_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2) close)
    )
    (decreases fuel)
= let a10 = a1 in
  let a20 = a2 in
  if fuel = 0
  then ROutOfFuel
  else let fuel' : nat = fuel - 1 in
  match (a1, destruct_group a1), (a2, destruct_group a2) with
  | (GAlwaysFalse, _), _
  | _, (GAlwaysFalse, _) -> RSuccess ()
  | (GNop, _), (GNop, _) -> RFailure "array_group_disjoint: nop"
  | (GChoice a1l a1r, _), (a2, _)
  | (a2, _), (GChoice a1l a1r, _) ->
    let res1 = array_group_disjoint e fuel' close a1l a2 in
    if not (RSuccess? res1)
    then res1
    else array_group_disjoint e fuel' close a1r a2
  | (_, (GDef _ n, a1r)), (a2, _)
  | (a2, _), (_, (GDef _ n, a1r)) ->
    let a1' = GConcat (e.e_env n) a1r in
    rewrite_group_correct e.e_sem_env fuel' a1';
    array_group_disjoint e fuel' close (rewrite_group fuel' _ a1') a2
  | (a1, (GZeroOrMore g, a1r)), (a2, _)
  | (a2, _), (a1, (GZeroOrMore g, a1r)) ->
    assert (
     Spec.array_group3_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a10) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a20) close) <==>
       Spec.array_group3_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2) close)
     );
     let res1 = array_group_disjoint e fuel' close a1r a2 in
     if not (RSuccess? res1)
     then res1
     else if RSuccess? (array_group_disjoint e fuel' false g a2) // loop-free shortcut, but will miss things like "disjoint? (a* ) (ab)"
     then RSuccess ()
     else begin
       Spec.array_group3_concat_assoc (array_group_sem e.e_sem_env g) (array_group_sem e.e_sem_env (GZeroOrMore g)) (array_group_sem e.e_sem_env a1r);
       let a1' = GConcat g a1 in
       rewrite_group_correct e.e_sem_env fuel' a1';
       array_group_disjoint e fuel' close (rewrite_group fuel' _ a1') a2 // potential source of loops
     end
   | (a1, (GOneOrMore g, a1r)), (a2, _)
   | (a2, _), (a1, (GOneOrMore g, a1r)) ->
     assert (
       Spec.array_group3_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a10) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a20) close) <==>
       Spec.array_group3_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2) close)
     );
     let a1' = GConcat (GConcat g (GZeroOrMore g)) a1r in
     rewrite_group_correct e.e_sem_env fuel' a1';
     array_group_disjoint e fuel' close (rewrite_group fuel' _ a1') a2 // potential source of loops
   | (a1, (GZeroOrOne g, a1r)), (a2, _)
   | (a2, _), (a1, (GZeroOrOne g, a1r)) ->
     assert (
       Spec.array_group3_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a10) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a20) close) <==>
       Spec.array_group3_disjoint (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a1) close) (Spec.maybe_close_array_group (array_group_sem e.e_sem_env a2) close)
     );
     let res = array_group_disjoint e fuel' close a1r a2 in
     if not (RSuccess? res)
     then res
     else begin
       let a1' = GConcat g a1r in
       rewrite_group_correct e.e_sem_env fuel' a1';
       array_group_disjoint e fuel' close (rewrite_group fuel' _ a1') a2
     end
   | (GNop, _), (_, (GArrayElem _ _, _))
   | (_, (GArrayElem _ _, _)), (GNop, _) ->
     if close then RSuccess () else RFailure "array_group_disjoint: empty but not close"
   | (_, (GArrayElem _ a1l, a1r)), (_, (GArrayElem _ a2l, a2r)) ->
     let res1 = typ_disjoint e fuel' a1l a2l in
     if RSuccess? res1
     then res1
     else if a1l = a2l // TODO: replace with equivalence?
     then begin
       array_group_concat_elem_same_disjoint
         close
         (typ_sem e.e_sem_env a1l)
         (typ_sem e.e_sem_env a2l)
         (array_group_sem e.e_sem_env a1r)
         (array_group_sem e.e_sem_env a2r);
       array_group_disjoint e fuel' close a1r a2r
     end
     else res1
   | (_, (GConcat a11 a12, a13)), (a2, _)
   | (a2, _), (_, (GConcat a11 a12, a13)) ->
     array_group_disjoint e fuel' close (GConcat a11 (GConcat a12 a13)) a2
   | _ -> RFailure "array_group_disjoint: array: unsupported pattern"

#pop-options

#restart-solver
let rec map_group_footprint
  (g: group NMapGroup)
: Tot (result typ)
= match g with
  | GMapElem _ cut (TElem (ELiteral key)) value
  -> RSuccess (TElem (ELiteral key))
  | GZeroOrMore (GMapElem _ false key _) // TODO: extend to GOneOrMore
  -> RSuccess key
  | GZeroOrOne g -> map_group_footprint g
  | GChoice g1 g2
  | GConcat g1 g2 ->
    begin match map_group_footprint g1 with
    | RSuccess ty1 ->
      begin match map_group_footprint g2 with
      | RSuccess ty2 -> RSuccess (ty1 `TChoice` ty2)
      | res -> res
      end
    | res -> res
    end
  | GNop
  | GAlwaysFalse -> RSuccess (TElem EAlwaysFalse)
  | GMapElem _ _ _ _
  | GZeroOrMore _
  | GOneOrMore _ -> RFailure "map_group_footprint: unsupported cases. Please `rewrite` your map group before calling"

#push-options "--z3rlimit 32"

#restart-solver
let rec map_group_footprint_correct
  (env: sem_env)
  (g: group NMapGroup)
: Lemma
  (requires (
    group_bounded _ env.se_bound g
  ))
  (ensures (
    match spec_map_group_footprint env g, map_group_footprint g with
    | Some ty, RSuccess t ->
      typ_bounded env.se_bound t /\
      ty `Spec.typ_equiv` typ_sem env t
    | _, RSuccess _ -> False
    | Some _, _ -> False
    | _ -> True
  ))
  (decreases g)
  [SMTPat (spec_map_group_footprint env g)]
= match g with
  | GZeroOrOne g ->
    map_group_footprint_correct env g
  | GChoice g1 g2
  | GConcat g1 g2 ->
    map_group_footprint_correct env g1;
    map_group_footprint_correct env g2
  | _ -> ()

#restart-solver
let rec restrict_map_group
  (fuel: nat) // for typ_disjoint
  (env: ast_env)
  (left: typ)
  (g: group NMapGroup)
: Pure (result (group NMapGroup))
    (requires (
      typ_bounded env.e_sem_env.se_bound left /\
      group_bounded _ env.e_sem_env.se_bound g
    ))
    (ensures (fun g' ->
      match g' with
      | RSuccess g' ->
        group_bounded _ env.e_sem_env.se_bound g' /\
        MapSpec.restrict_map_group
          (map_group_sem env.e_sem_env g)
          (map_group_sem env.e_sem_env g') /\
        begin match spec_map_group_footprint env.e_sem_env g, spec_map_group_footprint env.e_sem_env g' with
        | Some fp, Some fp' -> Spec.typ_included fp' fp /\
          Spec.typ_disjoint (typ_sem env.e_sem_env left) fp'
        | _ -> False
        end
      | _ -> True
    ))
  (decreases g)
= match g with
  | GChoice g1 g2 ->
    begin match restrict_map_group fuel env left g1 with
    | RSuccess g1' ->
      begin match restrict_map_group fuel env left g2 with
      | RSuccess g2' -> RSuccess (GChoice g1' g2')
      | res -> res
      end
    | res -> res
    end
  | GConcat g1 g2 ->
    begin match restrict_map_group fuel env left g1 with
    | RSuccess g1' ->
      let RSuccess fp1 = map_group_footprint g1 in
      begin match restrict_map_group fuel env (left `TChoice` fp1) g2 with
      | RSuccess g2' ->
        let f2' = Ghost.hide (Some?.v (spec_map_group_footprint env.e_sem_env g2')) in
        MapSpec.restrict_map_group_concat
          (map_group_sem env.e_sem_env g1)
          (typ_sem env.e_sem_env fp1)
          (map_group_sem env.e_sem_env g1')
          (map_group_sem env.e_sem_env g2)
          (map_group_sem env.e_sem_env g2')
          f2';
        let g' = GConcat g1' g2' in
        assert (MapSpec.restrict_map_group
          (map_group_sem env.e_sem_env g)
          (map_group_sem env.e_sem_env g')
        );
        assert (Some? (spec_map_group_footprint env.e_sem_env g));
        assert (Some? (spec_map_group_footprint env.e_sem_env g'));
        assert (
          let Some fp = spec_map_group_footprint env.e_sem_env g in
          let Some fp' = spec_map_group_footprint env.e_sem_env g' in
          Spec.typ_included fp' fp /\
          Spec.typ_disjoint (typ_sem env.e_sem_env left) fp'
        );
        RSuccess g' // (rewrite_group fuel _ g')
      | res -> res
      end
    | res -> res
    end
  | GZeroOrOne g1 ->
    begin match restrict_map_group fuel env left g1 with
    | RSuccess g1' -> RSuccess (GZeroOrOne g1')
    | res -> res
    end
  | GMapElem sq cut (TElem (ELiteral key)) value ->
    begin match typ_disjoint env fuel (TElem (ELiteral key)) left with
    | RSuccess _ ->
      MapSpec.map_group_is_det_match_item_for
        cut
        (eval_literal key)
        (typ_sem env.e_sem_env value);
      MapSpec.restrict_map_group_refl (map_group_sem env.e_sem_env g);
      RSuccess g
    | RFailure msg -> RFailure msg
    | ROutOfFuel -> ROutOfFuel
    end
  | GZeroOrMore (GMapElem _ false key value) ->
    begin match typ_disjoint env fuel key left with
    | RSuccess _ ->
      MapSpec.restrict_map_group_refl (map_group_sem env.e_sem_env g);
      RSuccess g
    | _ ->
      RSuccess GNop
    end
  | _ -> RFailure "restrict_map_group: unsupported cases"

#pop-options
