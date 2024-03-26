module COSE.AST
open CDDL.Interpreter
module Spec = COSE.Spec

#set-options "--fuel 0"

let e0 = empty_env
let thr0 : spec_array_group_splittable_threshold e0 = spec_array_group_splittable_threshold_empty _

let e1 = env_extend_map_group e0 "header_map0" Spec.header_map0 ()

let e2 = env_extend_typ e1 "header_map" (TElem (TMap "header_map0")) ()

let e3 = env_extend_typ e2 "empty_or_serialized_map" (TEscapeHatch Spec.empty_or_serialized_map) ()

let e4 =
  env_extend_array_group e3 "headers" [
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

let e5 =
  env_extend_typ e4 "bstr" (TEscapeHatch CDDL.Spec.bstr) ()

let e6 =
  env_extend_array_group e5 "cose_signature0" [
    "headers", TAAtom (TADef "headers");
    "signature", TAAtom (TAElem (TDef "bstr"));
  ]
  (_ by (solve_env_extend_array_group ()))

let thr6 : spec_array_group_splittable_threshold e6 =
  spec_array_group_splittable_threshold_extend
    (spec_array_group_splittable_threshold_extend_env thr4 e6)
    "cose_signature0"
    (_ by (solve_spec_array_group_splittable ()))
