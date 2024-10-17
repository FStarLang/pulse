(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Main
open FStar.Tactics.V2
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker
open Pulse.Elaborate
open Pulse.Soundness
module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing
module Cfg = Pulse.Config
module RU = Pulse.RuntimeUtils
module P = Pulse.Syntax.Printer
module Rec = Pulse.Recursion
open Pulse.Json 

let env_bindings_to_json (g:env) : T.Tac Pulse.Json.json =
  JsonList (
    T.map 
      (fun (x, n, t) ->
        JsonAssoc ([
          "name", JsonStr (T.unseal (x <: ppname).name);
          "index", JsonInt (n <: var);
          "type", JsonStr (Stubs.Pprint.render (Syntax.Printer.term_to_doc t))
        ]))
      (Pulse.Typing.Env.bindings_with_ppname g)
  )

let qualifier_to_json (q: option qualifier) : T.Tac Pulse.Json.json =
  JsonStr(Pulse.Syntax.Printer.qual_to_string q)

let binder_to_json (b: binder) : T.Tac Pulse.Json.json =
  JsonAssoc ([
    "type", JsonStr "";
    "name", JsonStr (T.unseal (b.binder_ppname <: ppname).name);
    "attributes", JsonList (
      T.map (fun t -> JsonStr (Pulse.Syntax.Printer.term_to_string t)) (T.unseal b.binder_attrs)
    )
  ])

#push-options "--z3rlimit_factor 4"
let rec jsonize_st_typing #g #t #c (d:st_typing g t c) : T.Tac Pulse.Json.json =
  let open Pulse.Json in
  match d with
    | T_Abs g x q b u body c total_typing body_typing ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_Abs");
        // "environment", env_bindings_to_json g;
        // "x", JsonInt (x <: var);
        // "q", qualifier_to_json q;
        "b", binder_to_json b;
        // "universe", JsonStr (Pulse.Syntax.Printer.univ_to_string u);
        // "body", JsonStr(Pulse.Syntax.Printer.st_term_to_string body);
        // "body_range", JsonStr (T.range_to_string body.range);
        // "comp", JsonStr(Pulse.Syntax.Printer.comp_to_string c); 
        "body", jsonize_st_typing body_typing;
      ])
    | T_STApp g head ty q res arg tot_typing_head tot_typing_arg ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_STApp");
        // "environment", env_bindings_to_json g;
        // "head", JsonStr(Pulse.Syntax.Printer.term_to_string head);
        // "ty", JsonStr(Pulse.Syntax.Printer.term_to_string ty);
        // "q", qualifier_to_json q;
        // "res", JsonStr(Pulse.Syntax.Printer.comp_to_string res);
        // "arg", JsonStr(Pulse.Syntax.Printer.term_to_string arg);
        // "tot_typing_head", jsonize_st_typing tot_typing_head;
        // "tot_typing_arg", jsonize_st_typing tot_typing_arg;
        "stmt", JsonStr (Pulse.Syntax.Printer.st_term_to_string (t));
        "comp", JsonStr (Pulse.Syntax.Printer.comp_to_string (c));
      ])
    | T_STGhostApp g head ty q res arg x ghost_typing_head non_informative ghost_typing_arg ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_STGhostApp");
        "stmt", JsonStr (Pulse.Syntax.Printer.st_term_to_string (t));
        "comp", JsonStr (Pulse.Syntax.Printer.comp_to_string (c));
        // "environment", env_bindings_to_json g;
        // "head", JsonStr(Pulse.Syntax.Printer.term_to_string head);
        // "ty", JsonStr(Pulse.Syntax.Printer.term_to_string ty);
        // "q", qualifier_to_json q;
        // "res", JsonStr(Pulse.Syntax.Printer.comp_to_string res);
        // "arg", JsonStr(Pulse.Syntax.Printer.term_to_string arg);
        // "x", JsonInt (x <: var);
        // "ghost_typing_head", jsonize_st_typing ghost_typing_head;
        // "non_informative", jsonize_st_typing non_informative;
        // "ghost_typing_arg", jsonize_st_typing ghost_typing_arg;
      ])
    | T_Return g c use_eq u t e post x tot_typing_e tot_typing_post tot_typing_x ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_Return");
        // "environment", env_bindings_to_json g;
        // "ctag", JsonStr(Pulse.Syntax.Printer.ctag_to_string c);
        // "use_eq", JsonBool use_eq;
        // "universe", JsonStr (Pulse.Syntax.Printer.univ_to_string u);
        // "type", JsonStr(Pulse.Syntax.Printer.term_to_string t);
        "e", JsonStr(Pulse.Syntax.Printer.term_to_string e);
        "post", JsonStr(Pulse.Syntax.Printer.term_to_string post);
        // "x", JsonInt (x <: var);
        // "tot_typing_e", jsonize_st_typing tot_typing_e;
        // "tot_typing_post", jsonize_st_typing tot_typing_post;
        // "tot_typing_x", jsonize_st_typing tot_typing_x;
      ])
    | T_Lift g e c1 c2 d1 comp  ->
      // JsonAssoc ([
      //   "stmt_type", JsonStr ("T_Lift");
      //   // "environment", env_bindings_to_json g;
      //   // "e", JsonStr(Pulse.Syntax.Printer.st_term_to_string e);
      //   // "e_range", JsonStr (T.range_to_string e.range);
      //   // "c1", JsonStr(Pulse.Syntax.Printer.comp_to_string c1);
      //   // "c2", JsonStr(Pulse.Syntax.Printer.comp_to_string c2);
      //   "d1", jsonize_st_typing d1;
      //   // "d2", jsonize_st_typing comp;
      // ])
      jsonize_st_typing d1
    | T_Bind g e1 e2 c1 c2 b x c d1 total_typing d2 bind_comp ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_Bind");
        // "environment", env_bindings_to_json g;
        // "e1", JsonStr(Pulse.Syntax.Printer.st_term_to_string e1);
        // "e1_range", JsonStr (T.range_to_string e1.range);
        // "e2", JsonStr(Pulse.Syntax.Printer.st_term_to_string e2);
        // "e2_range", JsonStr (T.range_to_string e2.range);
        // "c1", JsonStr(Pulse.Syntax.Printer.comp_to_string c1);
        // "c2", JsonStr(Pulse.Syntax.Printer.comp_to_string c2);
        // "b", binder_to_json b;
        // "x", JsonInt (x <: var);
        // "c", JsonStr(Pulse.Syntax.Printer.comp_to_string c);
        "d1", jsonize_st_typing d1;
        // "total_typing", jsonize_st_typing total_typing;
        "d2", jsonize_st_typing d2;
        // "bind_comp", jsonize_st_typing bind_comp;
      ])
    | T_BindFn g e1 e2 c1 c2 b x d1 ghost_erased_universe total_typing d2 bind_comp ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_BindFn");
        // "environment", env_bindings_to_json g;
        // "e1", JsonStr(Pulse.Syntax.Printer.st_term_to_string e1);
        // "e1_range", JsonStr (T.range_to_string e1.range);
        // "e2", JsonStr(Pulse.Syntax.Printer.st_term_to_string e2);
        // "e2_range", JsonStr (T.range_to_string e2.range);
        // "c1", JsonStr(Pulse.Syntax.Printer.comp_to_string c1);
        // "c2", JsonStr(Pulse.Syntax.Printer.comp_to_string c2);
        // "b", binder_to_json b;
        // "x", JsonInt (x <: var);
        "d1", jsonize_st_typing d1;
        // "universe", JsonStr (Pulse.Syntax.Printer.univ_to_string ghost_erased_universe);
        // "total_typing", TODO
        "d2", jsonize_st_typing d2;
        // "bind_comp", JsonStr (Pulse.Syntax.Printer.comp_to_string bind_comp);
      ])
    | T_If g b e1 e2 c hyp total_typing e1_st_typing e2_st_typing erased_comp ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_If");
        // "environment", env_bindings_to_json g;
        "b", JsonStr(Pulse.Syntax.Printer.term_to_string b);
        // "e1", JsonStr(Pulse.Syntax.Printer.st_term_to_string e1);
        // "e1_range", JsonStr (T.range_to_string e1.range);
        // "e2", JsonStr(Pulse.Syntax.Printer.st_term_to_string e2);
        // "e2_range", JsonStr (T.range_to_string e2.range);
        // "c", JsonStr(Pulse.Syntax.Printer.comp_to_string c);
        // "hyp", JsonStr(Pulse.Syntax.Printer.term_to_string hyp);
        // "total_typing", jsonize_st_typing total_typing;  
        "e1_st_typing", jsonize_st_typing e1_st_typing;
        "e2_st_typing", jsonize_st_typing e2_st_typing;
        // "erased_comp", jsonize_st_typing erased_comp;
      ])
    | T_Match g sc_u sc_ty sc total_typing1 total_typing2 c erased brs brs_typing pats_complt ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_Match");
        // "environment", env_bindings_to_json g;
        // "sc_u", JsonStr (Pulse.Syntax.Printer.univ_to_string sc_u);
        // "sc_ty", JsonStr (Pulse.Syntax.Printer.term_to_string sc_ty);
        // "sc", JsonStr (Pulse.Syntax.Printer.term_to_string sc);
        // "total_typing1", jsonize_st_typing total_typing1;
        // "total_typing2", jsonize_st_typing total_typing2;
        // "c", JsonStr (Pulse.Syntax.Printer.comp_to_string c);
        // "erased", jsonize_st_typing erased;
        // "branches", JsonList(
        //   T.map (fun (p, e) -> JsonAssoc([
        //     "pattern", JsonStr (Pulse.Syntax.Printer.pattern_to_string p);
        //     "expr", JsonStr (Pulse.Syntax.Printer.st_term_to_string e);
        //     "expr_range", JsonStr (T.range_to_string (e <: st_term).range);
        //   ])) brs
        // );
        // "brs_typing", jsonize_st_typing brs_typing; // TODO: This is a list of typing derivations for different branchs
        // "pats_complt", jsonize_st_typing pats_complt;
      ])
    | T_Frame g e comp frame total_typing body ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_Frame");
        // "environment", env_bindings_to_json g;
        // "e", JsonStr (Pulse.Syntax.Printer.st_term_to_string e);
        // "e_range", JsonStr (T.range_to_string e.range);
        // "c", JsonStr (Pulse.Syntax.Printer.comp_to_string c);
        "frame", JsonStr (Pulse.Syntax.Printer.term_to_string frame);
        // "total_typing", jsonize_st_typing total_typing;
        "body", jsonize_st_typing body;
        "c", JsonStr (Pulse.Syntax.Printer.comp_to_string c);
      ])
    | T_Equiv g e c c' d eq ->
      // JsonAssoc ([
      //   "stmt_type", JsonStr ("T_Equiv");
      //   // "environment", env_bindings_to_json g;
      //   // "e", JsonStr (Pulse.Syntax.Printer.st_term_to_string e);
      //   // "e_range", JsonStr (T.range_to_string e.range);
      //   // "c", JsonStr (Pulse.Syntax.Printer.comp_to_string c);
      //   // "c'", JsonStr (Pulse.Syntax.Printer.comp_to_string c');
      //   "d", jsonize_st_typing d;
      //   // "eq", jsonize_st_typing eq;
      // ])
      jsonize_st_typing d
    | T_Sub g e c c' d sub ->
      // JsonAssoc ([
      //   "stmt_type", JsonStr ("T_Sub");
      //   "environment", env_bindings_to_json g;
      //   "e", JsonStr (Pulse.Syntax.Printer.st_term_to_string e);
      //   "e_range", JsonStr (T.range_to_string e.range);
      //   "c", JsonStr (Pulse.Syntax.Printer.comp_to_string c);
      //   "c'", JsonStr (Pulse.Syntax.Printer.comp_to_string c');
      //   "d", jsonize_st_typing d;
      //   // "sub", jsonize_st_typing sub;
      // ])
      jsonize_st_typing d
    | T_IntroPure g p tot_typing prop_validity ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_IntroPure");
        // "environment", env_bindings_to_json g;
        "p", JsonStr (Pulse.Syntax.Printer.term_to_string p);
        // "tot_typing", jsonize_st_typing tot_typing;
        // "prop_validity", jsonize_st_typing prop_validity;
      ])
    | T_ElimExists g u t p x tot_typing1 tot_typing2 ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_ElimExists");
        // "environment", env_bindings_to_json g;
        // "u", JsonStr (Pulse.Syntax.Printer.univ_to_string u);
        "t", JsonStr (Pulse.Syntax.Printer.term_to_string t);
        "p", JsonStr (Pulse.Syntax.Printer.term_to_string p);
        // "x", JsonInt (x <: var);
        // "tot_typing1", jsonize_st_typing tot_typing1;
        // "tot_typing2", jsonize_st_typing tot_typing1;
      ])
    | T_IntroExists g u b p e tot_typing1 tot_typing2 ghost_typing ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_IntroExists");
        // "environment", env_bindings_to_json g;
        // "u", JsonStr (Pulse.Syntax.Printer.univ_to_string u);
        // "b", binder_to_json b;
        "p", JsonStr (Pulse.Syntax.Printer.term_to_string p);
        "e", JsonStr (Pulse.Syntax.Printer.term_to_string e);
        // "tot_typing1", jsonize_st_typing tot_typing1;
        // "tot_typing2", jsonize_st_typing tot_typing2;
        // "ghost_typing", jsonize_st_typing ghost_typing;
      ])
    | T_While g inv cond body tot_typing_inv st_typing_cond st_typing_body ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_While");
        // "environment", env_bindings_to_json g;
        "inv", JsonStr (Pulse.Syntax.Printer.term_to_string inv);
        // "cond", JsonStr (Pulse.Syntax.Printer.st_term_to_string cond);
        // "cond_range", JsonStr (T.range_to_string cond.range);
        // "body", JsonStr (Pulse.Syntax.Printer.st_term_to_string body);
        // "body_range", JsonStr (T.range_to_string body.range);
        // "tot_typing_inv", jsonize_st_typing tot_typing_inv;
        "st_typing_cond", jsonize_st_typing st_typing_cond;
        "st_typing_body", jsonize_st_typing st_typing_body;
      ])
    | T_Par g eL cL eR cR x comp_typing_cl comp_typing_cr st_typing_cl st_typing_cr ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_Par");
        // "environment", env_bindings_to_json g;
        // "eL", JsonStr (Pulse.Syntax.Printer.st_term_to_string eL);
        // "eL_range", JsonStr (T.range_to_string eL.range);
        // "cL", JsonStr (Pulse.Syntax.Printer.comp_to_string cL);
        // "eR", JsonStr (Pulse.Syntax.Printer.st_term_to_string eR);
        // "eR_range", JsonStr (T.range_to_string eR.range);
        // "cR", JsonStr (Pulse.Syntax.Printer.comp_to_string cR);
        // "x", JsonInt (x <: var);
        // "comp_typing_cl", jsonize_st_typing comp_typing_cl;
        // "comp_typing_cr", jsonize_st_typing comp_typing_cr;
        "st_typing_cl", jsonize_st_typing st_typing_cl;
        "st_typing_cr", jsonize_st_typing st_typing_cr;
      ])
    | T_WithLocal g binder_ppname init body init_t c x tot_typing univerese_of comp_typing_u st_typing ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_WithLocal");
        // "environment", env_bindings_to_json g;
        "binder_ppname", JsonStr (T.unseal binder_ppname.name);
        "init", JsonStr (Pulse.Syntax.Printer.term_to_string init);
        // "body", JsonStr (Pulse.Syntax.Printer.st_term_to_string body);
        // "body_range", JsonStr (T.range_to_string body.range);
        "init_t", JsonStr (Pulse.Syntax.Printer.term_to_string init_t);
        // "c", JsonStr (Pulse.Syntax.Printer.comp_to_string c);
        // "x", JsonInt (x <: var);
        // "tot_typing", jsonize_st_typing tot_typing;
        // "universe_of", JsonStr (Pulse.Syntax.Printer.univ_to_string univerese_of);
        // "comp_typing_u", jsonize_st_typing comp_typing_u;
        "st_typing", jsonize_st_typing st_typing;
      ])
    | T_WithLocalArray g binder_ppname initializer length body a c x tot_typing_initializer tot_typing_length universe_of comp_typing_u st_typing ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_WithLocalArray");
        // "environment", env_bindings_to_json g;
        "binder_ppname", JsonStr (T.unseal binder_ppname.name);
        "initializer", JsonStr (Pulse.Syntax.Printer.term_to_string initializer);
        "length", JsonStr (Pulse.Syntax.Printer.term_to_string length);
        // "body", JsonStr (Pulse.Syntax.Printer.st_term_to_string body);
        // "body_range", JsonStr (T.range_to_string body.range);
        "init_t", JsonStr (Pulse.Syntax.Printer.term_to_string a);
        // "c", JsonStr (Pulse.Syntax.Printer.comp_to_string c);
        // "x", JsonInt (x <: var);
        // "tot_typing_initializer", jsonize_st_typing tot_typing_initializer;
        // "tot_typing_length", jsonize_st_typing tot_typing_length;
        // "universe_of", JsonStr (Pulse.Syntax.Printer.univ_to_string universe_of);
        // "comp_typing_u", jsonize_st_typing comp_typing_u;
        "st_typing", jsonize_st_typing st_typing;
      ])
    | T_Rewrite g p q tot_typing_p slprop_equiv ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_Rewrite");
        // "environment", env_bindings_to_json g;
        "p", JsonStr (Pulse.Syntax.Printer.term_to_string p);
        "q", JsonStr (Pulse.Syntax.Printer.term_to_string q);
        // "tot_typing_p", jsonize_st_typing tot_typing_p;
        // "slprop_equiv", jsonize_st_typing slprop_equiv;
      ])
    | T_Admit g c comp_typing ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_Admit");
        // "environment", env_bindings_to_json g;
        "c", JsonStr (Pulse.Syntax.Printer.comp_to_string c);
        // "comp_typing", jsonize_st_typing comp_typing;
      ])
    | T_Unreachable g c comp_typing prop_validity ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_Unreachable");
        // "environment", env_bindings_to_json g;
        "c", JsonStr (Pulse.Syntax.Printer.comp_to_string c);
        // "comp_typing", jsonize_st_typing comp_typing;
        // "prop_validity", jsonize_st_typing prop_validity;
      ])
    | T_WithInv g i p body c tot_typing_i tot_typing_p body_typing inv_disjointness_token ->
      JsonAssoc ([
        "stmt_type", JsonStr ("T_WithInv");
        // "environment", env_bindings_to_json g;
        "inv", JsonStr (Pulse.Syntax.Printer.term_to_string i);
        "inv_type", JsonStr (Pulse.Syntax.Printer.term_to_string p);
        // "body", JsonStr (Pulse.Syntax.Printer.st_term_to_string body);
        // "body_range", JsonStr (T.range_to_string body.range);
        // "c", JsonStr (Pulse.Syntax.Printer.comp_to_string c);
        // "tot_typing_i", jsonize_st_typing tot_typing_i;
        // "tot_typing_p", jsonize_st_typing tot_typing_p;
        "body_typing", jsonize_st_typing body_typing;
        // "inv_disjointness_token", jsonize_st_typing inv_disjointness_token;
      ])
    | _ -> JsonStr "<UNK>"



let print_st_typing #g #t #c (d:st_typing g t c) : T.Tac unit =
  let open Pulse.Json in
  let json = jsonize_st_typing d in
  T.print (string_of_json json)


let debug_main g (s: unit -> T.Tac string) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.main"
  then T.print (s ())
  else ()

let rec mk_abs (g:env) (qbs:list (option qualifier & binder & bv)) (body:st_term) (comp:comp)
: TacH st_term (fun _ -> not (Nil? qbs))
               (fun _ r -> match r with FStar.Tactics.Result.Success v _ -> Tm_Abs? v.term | _ -> False)
=
  let with_range (s:st_term') (r:range) : st_term =
    { term = s; range = r; effect_tag = default_effect_hint; source=Sealed.seal false }
  in
  match qbs with
  | [(q, last, last_bv)] -> 
    let body = close_st_term body last_bv.bv_index in
    let comp = close_comp comp last_bv.bv_index in
    let asc = { annotated = Some comp; elaborated = None } in
    with_range (Pulse.Syntax.Builder.tm_abs last q asc body) body.range
  | (q, b, bv)::qbs ->
    let body = mk_abs g qbs body comp in
    let body = close_st_term body bv.bv_index in
    with_range (Pulse.Syntax.Builder.tm_abs b q empty_ascription body) body.range

let set_impl #g #t (se: RT.sigelt_for g t) (r: bool) (impl: R.term) : Dv (RT.sigelt_for g t) =
  let checked, se, blob = se in
  let se = RU.add_attribute se (Extract.CompilerLib.mk_extracted_as_attr impl) in
  checked, se, blob

#push-options "--z3rlimit_factor 10"
let check_fndefn
    (d : decl{FnDefn? d.d})
    (g : Soundness.Common.stt_env{bindings g == []})
    (expected_t : option term)
    (* Both of these unused: *)
    (pre : term) (pre_typing : tot_typing g pre tm_slprop)
  : T.Tac (RT.dsl_tac_result_t (fstar_env g) expected_t)
= 

  (* Maybe add a recursive knot before starting *)
  let FnDefn fn_d = d.d in
  let nm_orig = fst (inspect_ident fn_d.id) in // keep the original name
  let d =
    if fn_d.isrec
    then Recursion.add_knot g d.range d
    else d
  in

  let FnDefn { id; isrec; bs; comp; meas; body } = d.d in
  let nm_aux = fst (inspect_ident id) in

  if Nil? bs then
    fail g (Some d.range) "main: FnDefn does not have binders";
  let body = mk_abs g bs body comp in
  let rng = body.range in
  debug_main g (fun _ -> Printf.sprintf "\nbody after mk_abs:\n%s\n" (P.st_term_to_string body));

  let (| body, c, t_typing |) = Pulse.Checker.Abs.check_abs g body Pulse.Checker.check in

  Pulse.Checker.Prover.debug_prover g
    (fun _ -> Printf.sprintf "\ncheck call returned in main with:\n%s\nat type %s\n"
              (P.st_term_to_string body)
              (P.comp_to_string c));
  debug_main g
    (fun _ -> Printf.sprintf "\nchecker call returned in main with:\n%s\nderivation=%s\n"
              (P.st_term_to_string body)
              (Pulse.Typing.Printer.print_st_typing t_typing));
  
  let _ = print_st_typing t_typing in 
  let refl_t = elab_comp c in
  let refl_e = Pulse.RuntimeUtils.embed_st_term_for_extraction #st_term body (Some rng) in
  let blob = "pulse", refl_e in
  soundness_lemma g body c t_typing;

  let elab_derivation = T.ext_getv "pulse:elab_derivation" <> "" in
  let cur_module = T.cur_module () in

  let maybe_add_impl t (se: RT.sigelt_for (fstar_env g) t) : Tac (RT.sigelt_for (fstar_env g) t) =
    let open Pulse.Extract.Main in begin
    if C_STGhost? comp then
      se
    else if fn_d.isrec then
      let impl = extract_dv_recursive g body (R.pack_fv (cur_module @ [nm_orig])) in
      set_impl se true impl
    else
      set_impl se false (extract_pulse_dv g body)
    end in

  let mk_main_decl
    (refl_t:typ)
    (_:squash (RT.tot_typing (elab_env g) (elab_st_typing t_typing) refl_t)) =
    let nm = fst (inspect_ident id) in
    if elab_derivation
    then RT.mk_checked_let (fstar_env g) cur_module nm (elab_st_typing t_typing) refl_t
    else Reflection.Util.mk_opaque_let (fstar_env g) cur_module nm (elab_st_typing t_typing) refl_t
  in

  if fn_d.isrec
  then begin
    //
    // For the recursive case, the recursive decl is the one that has the
    //   input expected type
    // However, for it, we don't set the checked flag and let F* typecheck it
    //
    // So, nothing to be done for expected type here
    //
    let main_decl = mk_main_decl refl_t () in
    let main_decl : RT.sigelt_for (elab_env g) None = main_decl in
    let (chk, se, _) = main_decl in
    let nm = R.pack_ln (R.Tv_Const (R.C_String nm_orig)) in
    let attribute = `("pulse.recursive", `#(nm)) in
    let se = RU.add_attribute se (`(noextract_to "krml")) in
    let se = RU.add_noextract_qual se in
    let se : T.sigelt = RU.add_attribute se attribute in
    let main_decl = chk, se, Some blob in
    let recursive_decl : RT.sigelt_for (elab_env g) expected_t =
      Rec.tie_knot g rng nm_orig nm_aux refl_t blob in
    [main_decl], maybe_add_impl _ recursive_decl, []
  end
  else begin
    //
    // For the non-recursive case,
    //   we need to check that the computed type is a subtype of the expected type
    //
    let (| refl_t, _ |) :
      refl_t:term { Some? expected_t ==> Some refl_t == expected_t } &
      squash (RT.tot_typing (elab_env g) (elab_st_typing t_typing) refl_t) =

      match expected_t with
      | None -> (| refl_t, FStar.Squash.get_proof _ |)

      | Some t ->
        let tok = Pulse.Checker.Pure.check_subtyping g refl_t t in
        let refl_t_typing
          : squash (RT.tot_typing (elab_env g) (elab_st_typing t_typing) refl_t) = () in
        let sq : squash (RT.tot_typing (elab_env g) (elab_st_typing t_typing) t) =
          FStar.Squash.bind_squash refl_t_typing (fun refl_t_typing ->
            FStar.Squash.return_squash (
              RT.T_Sub _ _ _ _
                refl_t_typing
                (RT.Relc_typ _ _ _ _ RT.R_Sub
                   (RT.Rel_subtyping_token _ _ _ (FStar.Squash.return_squash tok))))) in

        (| t, sq |)
    in

    let main_decl = mk_main_decl refl_t () in
    let chk, se, _ = main_decl in
    let main_decl = chk, se, Some blob in
    [], maybe_add_impl _ main_decl, []
  end

let check_fndecl
    (d : decl{FnDecl? d.d})
    (g : Soundness.Common.stt_env{bindings g == []})
  : T.Tac (RT.dsl_tac_result_t (fstar_env g) None)
=
  let FnDecl { id; bs; comp } = d.d in
  if Nil? bs then
    fail g (Some d.range) "main: FnDecl does not have binders";

  let nm = fst (inspect_ident id) in
  let stc = st_comp_of_comp comp in

  (* We make a dummy FnDefn setting the body to a Tm_Admit, and
  call the checker to elaborate its actual type. *)
  let body : st_term = {
    term = Tm_Admit {
      ctag   = ctag_of_comp_st comp;
      u      = stc.u;
      typ    = stc.res;
      post   = None; // Some stc.post?
    };
    range = d.range;
    effect_tag = seal None;
    source = seal false;
  }
  in
  let body = mk_abs g bs body comp in
  let rng = body.range in
  let (| _, c, t_typing |) =
    (* We don't want to print the diagnostic for the admit in the body. *)
    RU.with_extv "pulse:no_admit_diag" "1" (fun () ->
      Pulse.Checker.Abs.check_abs g body Pulse.Checker.check
    )
  in
  let typ = elab_comp c in
  let se : sigelt =
    pack_sigelt <|
    Sg_Val {
      nm = cur_module () @ [nm];
      univs = [];
      typ = typ
    }
  in
  ([], (false, se, None), [])

let main' (d:decl) (pre:term) (g:RT.fstar_top_env) (expected_t:option term)
  : T.Tac (RT.dsl_tac_result_t g expected_t)
  = match Pulse.Soundness.Common.check_top_level_environment g with
    | None -> T.fail "pulse main: top-level environment does not include stt at the expected types"
    | Some g ->
      if RU.debug_at_level (fstar_env g) "Pulse" then 
        T.print (Printf.sprintf "About to check pulse decl:\n%s\n" (P.decl_to_string d));
      let (| pre, ty, pre_typing |) = Pulse.Checker.Pure.compute_tot_term_type g pre in
      if not (eq_tm ty tm_slprop) then
        fail g (Some (Pulse.RuntimeUtils.range_of_term pre)) "pulse main: cannot typecheck pre at type slprop"; //fix range
      let pre_typing : tot_typing g pre tm_slprop = pre_typing in
      match d.d with
      | FnDefn {} -> check_fndefn d g expected_t pre pre_typing
      | FnDecl {} ->
        if None? expected_t then
          check_fndecl d g
        else
          fail g (Some d.range) "pulse main: expected type provided for a FnDecl?"

let join_smt_goals () : Tac unit =
  let open FStar.Tactics.V2 in
  let open FStar.List.Tot in

  if RU.debug_at_level (top_env ()) "pulse.join" then
    dump "PULSE: Goals before join";

  (* Join *)
  let smt_goals = smt_goals () in
  set_goals (goals () @ smt_goals);
  set_smt_goals [];
  let n = List.Tot.length (goals ()) in
  ignore (repeat join);

  (* Heuristic rlimit setting :). Increase by 2 for every joined goal.
  Default rlimit is 5, so this is "saving" 3 rlimit units per joined
  goal. *)
  if not (Nil? (goals ())) then (
    let open FStar.Mul in
    let rlimit = get_rlimit() + (n-1)*2 in
    set_rlimit rlimit
  );

  if RU.debug_at_level (top_env ()) "pulse.join" then
    dump "PULSE: Goals after join";

  ()

let parse_guard_policy (s:string) : Tac guard_policy =
  match s with
  | "Goal" -> Goal
  | "SMT" -> SMT
  | "SMTSync" -> SMTSync
  | "Force" -> Force
  | "ForceSMT" -> ForceSMT
  // | "Drop" -> Drop (* terribly unsound, so not even allowing it here *)
  | _ -> Tactics.fail ("Unknown guard policy: " ^ s)

let main t pre : RT.dsl_tac_t = fun (g, expected_t) ->
  (* We use the ForceSMT policy by default, to discharge guards
  immediately when they show, allowing SMT. This
  proofstate and discharge them all at the end, potentially joining
  them (see below).
  This can be overriden to others by `--ext pulse:guard_policy=<guard>`
  where <guard> is one of of the above (see parse_guard_policy). *)
  set_guard_policy ForceSMT;
  if ext_getv "pulse:guard_policy" <> "" then
    set_guard_policy (parse_guard_policy (ext_getv "pulse:guard_policy"));

  let res = main' t pre g expected_t in

  if ext_getv "pulse:join" = "1"
     (* || ext_getv "pulse:join" <> "" *)
     // ^ Uncomment to make it true by default.
  then
    join_smt_goals();
  res

let check_pulse_core 
        (as_decl: unit -> Tac (either Pulse.Syntax.decl (option (string & R.range))))
  : RT.dsl_tac_t
  = fun (env, expected_t) ->
      if ext_getv "pulse:dump_on_failure" <> "1" then
        set_dump_on_failure false;
      match as_decl () with
      | Inl decl ->
        main decl tm_emp (env, expected_t)

      | Inr None ->
        T.fail "Pulse parser failed"

      | Inr (Some (msg, range)) ->
        let i =
          Issue.mk_issue "Error"
                   (Printf.sprintf "%s: %s" (T.range_to_string range) msg)
                   (Some range)
                   None
                   []
        in
        T.log_issues [i];
        T.fail "Pulse parser failed"



[@@plugin]
let check_pulse (namespaces:list string)
                (module_abbrevs:list (string & string))
                (content:string)
                (file_name:string)
                (line col:int)
                (nm:string)
  : RT.dsl_tac_t
  = fun (env, expected_t) ->
      check_pulse_core
        (fun () -> PulseSyntaxExtension.ASTBuilder.parse_pulse env namespaces module_abbrevs content file_name line col)
        (env, expected_t)

[@@plugin]
let check_pulse_after_desugar
      (decl:'a)
: RT.dsl_tac_t
= fun (env, expected_t) ->
    check_pulse_core
        (fun () -> 
          let decl : Pulse.Syntax.decl = RU.unembed_pulse_decl decl in
          Inl decl)
        (env, expected_t)
