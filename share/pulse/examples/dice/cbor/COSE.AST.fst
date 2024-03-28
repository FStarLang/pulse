module COSE.AST
open CDDL.Interpreter
module Spec = COSE.Spec

#set-options "--fuel 0"

[@@ bounded_attr; sem_attr]
let e0 = empty_env
let thr0 : spec_array_group_splittable_threshold e0 = spec_array_group_splittable_threshold_empty _

[@@ bounded_attr; sem_attr]
let e1 = env_extend_map_group e0 "header_map0" 
  (_ by (solve_env_extend_array_group ()))
  Spec.header_map0
  (_ by (solve_env_extend_array_group ()))

[@@ bounded_attr; sem_attr]
let e2 = env_extend_typ e1 "header_map"
  (_ by (solve_env_extend_array_group ()))
  (TElem (TMap "header_map0"))
  (_ by (solve_env_extend_array_group ()))

[@@ bounded_attr; sem_attr]
let e3 = env_extend_typ e2 "empty_or_serialized_map"
  (_ by (solve_env_extend_array_group ()))
  (TEscapeHatch Spec.empty_or_serialized_map)
  (_ by (solve_env_extend_array_group ()))

[@@ bounded_attr; sem_attr]
let e4 =
  env_extend_array_group e3 "headers"
    (_ by (solve_env_extend_array_group ()))
    [
      "protected", TAAtom (TAElem (TDef "empty_or_serialized_map"));
      "unprotected", TAAtom (TAElem (TDef "header_map"));
    ]
    (_ by (solve_env_extend_array_group ()))

let thr4 : spec_array_group_splittable_threshold e4 =
  spec_array_group_splittable_threshold_extend
    (spec_array_group_splittable_threshold_extend_env thr0 e4)
    "headers"
    (_ by (solve_spec_array_group_splittable ()))

let _ : squash (
  se_array_group e4.e_semenv "headers" `CDDL.Spec.array_group3_equiv` Spec.headers
) = 
  let a = normalize_term (e4.e_env "headers") in
  assert (array_group_sem e4.e_semenv a `CDDL.Spec.array_group3_equiv` Spec.headers)
    by (solve_sem_equiv ())

[@@ bounded_attr; sem_attr]
let e5 =
  env_extend_typ e4 "bstr"
    (_ by (solve_env_extend_array_group ()))
    (TEscapeHatch CDDL.Spec.bstr)
    (_ by (solve_env_extend_array_group ()))

[@@ bounded_attr; sem_attr]
let e6 =
  env_extend_array_group e5 "cose_signature_array"
    (_ by (solve_env_extend_array_group ()))
    [
      "headers", TAAtom (TADef "headers");
      "signature", TAAtom (TAElem (TDef "bstr"));
    ]
    (_ by (solve_env_extend_array_group ()))

let thr6 : spec_array_group_splittable_threshold e6 =
  spec_array_group_splittable_threshold_extend
    (spec_array_group_splittable_threshold_extend_env thr4 e6)
    "cose_signature_array"
    (_ by (solve_spec_array_group_splittable ()))

[@@ bounded_attr; sem_attr]
let e7 =
  env_extend_typ e6 "cose_signature"
    (_ by (solve_env_extend_array_group ()))
    (TElem (TArray "cose_signature_array"))
    (_ by (solve_env_extend_array_group ()))

let _ : squash (
  se_typ e7.e_semenv "cose_signature" `CDDL.Spec.typ_equiv` Spec.cose_signature
) = 
  let a = normalize_term (e7.e_env "cose_signature") in
  assert (typ_sem e7.e_semenv a `CDDL.Spec.typ_equiv` Spec.cose_signature)
    by (solve_sem_equiv ())

[@@ bounded_attr; sem_attr]
let e8 =
  env_extend_typ e7 "cose_signature_payload" 
    (_ by (solve_env_extend_array_group ()))
    (TChoice [
      TByteString;
      TNil;
    ])
    (_ by (solve_env_extend_array_group ()))

[@@ bounded_attr; sem_attr]
let e9 =
  env_extend_array_group e8 "cose_signatures"
    (_ by (solve_env_extend_array_group ()))
    ["signatures", TAOneOrMore (TAElem (TDef "cose_signature"))]
    (_ by (solve_env_extend_array_group ()))

let thr9 : spec_array_group_splittable_threshold e9 =
  spec_array_group_splittable_threshold_extend
    (spec_array_group_splittable_threshold_extend_env thr6 e9)
    "cose_signatures"
    (_ by (solve_spec_array_group_splittable ()))

[@@ bounded_attr; sem_attr]
let e10 =
  env_extend_array_group e9 "cose_sign_array"
    (_ by (solve_env_extend_array_group ()))
    [
      "headers", TAAtom (TADef "headers");
      "payload", TAAtom (TAElem (TDef "cose_signature_payload"));
      "signatures", TAAtom (TAElem (TArray "cose_signatures"));
    ]
    (_ by (solve_env_extend_array_group ()))

let thr10 : spec_array_group_splittable_threshold e10 =
  spec_array_group_splittable_threshold_extend
    (spec_array_group_splittable_threshold_extend_env thr9 e10)
    "cose_sign_array"
    (_ by (solve_spec_array_group_splittable ()))

[@@ bounded_attr; sem_attr]
let e11 =
  env_extend_typ e10 "cose_sign"
    (_ by (solve_env_extend_array_group ()))
    (TElem (TArray "cose_sign_array"))
    (_ by (solve_env_extend_array_group ()))

#push-options "--z3rlimit 16" // cannot reason about typ_equiv

let _ : squash (
  se_typ e11.e_semenv "cose_sign" `CDDL.Spec.typ_equiv` Spec.cose_sign
) = 
  let a = normalize_term (e11.e_env "cose_sign") in
  assert (typ_sem e11.e_semenv a `CDDL.Spec.typ_equiv` Spec.cose_sign)
    by (solve_sem_equiv ())

#pop-options

[@@ bounded_attr; sem_attr]
let e12 =
  env_extend_typ e11 "cose_sign_tagged"
    (_ by (solve_env_extend_array_group ()))
    (TTag Spec.tag_cose_sign (TDef "cose_sign"))
    (_ by (solve_env_extend_array_group ()))
