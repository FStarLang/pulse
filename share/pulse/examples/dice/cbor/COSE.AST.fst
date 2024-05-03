module COSE.AST
open CDDL.Interpreter
module Spec = COSE.Spec

#push-options "--fuel 0"

[@@  sem_attr]
let e0 = empty_wf_ast_env

[@@  sem_attr]
let generic_headers: group NMapGroup =
  GZeroOrOne (GMapElem () false (TElem (ELiteral (LInt CBOR.Spec.Constants.cbor_major_type_uint64 Spec.h_alg))) tint)

[@@  sem_attr]
let header_map = TMap generic_headers

let e1 = wf_ast_env_extend_typ
  e0
  "header_map"
  (_ by (solve_by_norm ()))
  header_map
  (_ by (solve_mk_wf_typ_fuel_for ()))

irreducible let print (#t: Type) (x: t) : prop = False

// let _ : squash (print (e1.e_wf "header_map"))  = (_ by (solve_by_norm (); FStar.Tactics.fail "abc"))
