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

module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing
open FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker
open Pulse.Elaborate
open Pulse.Soundness
module Cfg = Pulse.Config
module RU = Pulse.RuntimeUtils
module P = Pulse.Syntax.Printer
module Rec = Pulse.Recursion

let debug_main g (s: unit -> T.Tac string) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.main"
  then T.print (s ())
  else ()

let rec mk_abs (g:env) (qbs:list (option qualifier & binder & bv)) (body:st_term) (comp:comp)
: TacH st_term (fun _ -> not (Nil? qbs))
               (fun _ r -> match r with FStar.Tactics.Result.Success v _ -> Tm_Abs? v.term | _ -> False)
=
  let with_range (s:st_term') (r:range) : st_term =
    { term = s; range = r; effect_tag = default_effect_hint }
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

let rec is_incremental_st_term (st0 st1:st_term)
  : option st_term =
  match st0.term, st1.term with
  | Tm_Bind {binder=binder0; head=head0; body=body0},
    Tm_Bind {binder=binder1; head=head1; body=body1} ->
    if eq_binder binder0 binder1 &&
       eq_st_term head0 head1
    then is_incremental_st_term body0 body1
    else None

  | Tm_TotBind {binder=binder0; head=head0; body=body0},
    Tm_TotBind {binder=binder1; head=head1; body=body1} ->
    if eq_binder binder0 binder1 &&
       eq_tm head0 head1
    then is_incremental_st_term body0 body1
    else None

  | Tm_Admit _, _ -> Some st1


  | _, _ -> None

noeq
type cache_elt = {
  cache_decl : decl';
  cache_typing : (g:env & t:st_term & c:comp & st_typing g t c);
}

open Pulse.Checker.Base

let is_internal_name (s:string) : bool =
  admit ();
  // TODO: this is also in Pulse.Extract.Main, add to a single place
  s = "_fret" ||
  s = "_bind_c" ||
  s = "_while_c" ||
  s = "_tbind_c" ||
  s = "_if_br" ||
  s = "_br" ||
  FStar.String.index s 0 = '_'

let is_internal_binder (b:binder) : T.Tac bool =
  let s = T.unseal b.binder_ppname.name in
  is_internal_name s

// let rec get_abs_body_typing (#g:env) (#t:st_term) (#c:comp)
//   (d:st_typing g t c)
//   : T.Tac (g':env { g `env_extends` g} &
//            t':st_term &
//            c':comp &
//            st_typing g' t' c' &
//            (t'':st_term -> st_typing g' t'' c' -> T.Tac (t_abs:st_term & st_typing g t_abs c))) =
//   match d with
//   | T_Abs _ x q b u body c d_bt d_body ->
//     let g' = push_binding g x b.binder_ppname b.binder_ty in
//     let body = open_st_term_nv body (b.binder_ppname, x) in
//     let (| g', t', c', d', f |) = get_abs_body_typing #g' #body #c d_body in
//     assume (g' `env_extends` g);
//     (| g', t', c', d', (fun t'' d'' ->
//                         let (| t'', d'' |) = f t'' d'' in
//                         let t_closed = close_st_term t'' x in
//                         assume (open_st_term_nv t_closed (b.binder_ppname, x) == t'');
//                         (| _, T_Abs _ x q b u t_closed c d_bt d'' |)) |)

//   | _ -> (| g, t, c, d, (fun t'' d'' -> (| t'', d'' |) <: T.Tac _) |)

let (let?) (#a:Type) (#b:Type) (x:option a) (y:a -> T.Tac (option b))
  : T.Tac (option b) =

  match x with
  | None -> None
  | Some x -> y x

let return (#a:Type) (x:a) : option a = Some x

let c_match (c1 c2:comp_st) =
  effect_annot_of_comp c1 == effect_annot_of_comp c2 /\
  comp_pre c1 == comp_pre c2 /\
  comp_u c1 == comp_u c2 /\
  comp_post c1 == comp_post c2 /\
  comp_res c1 == comp_res c2

let obs_match (c1:comp_st) (c2:comp_st { c_match c1 c2 }) =
  match c1, c2 with
  | C_ST _, C_ST _ -> true
  | C_STAtomic _ obs1 _, C_STAtomic _ obs2 _ -> obs1 = obs2
  | C_STGhost _, C_STGhost _ -> true

let c_and_obs_match (c1 c2:comp_st) : Lemma (requires c_match c1 c2 /\ obs_match c1 c2) (ensures c1 == c2) =
  ()

let both_binds (t0 t1:st_term) =
  (Tm_Bind? t0.term /\ Tm_Bind? t1.term) \/
  (Tm_TotBind? t0.term /\ Tm_TotBind? t1.term)

#push-options "--z3rlimit_factor 10 --fuel 2 --ifuel 2 --print_implicits --print_full_names"
let rec incremental_tc_bind0 (#g:env) (#t:st_term) (#c:comp_st)
  (d:st_typing g t c)
  (t0:st_term)
  (t1:st_term { both_binds t0 t1 })
  : T.Tac (option (t':st_term & st_typing g t' c)) =

  match d with
  | T_Bind g e1 e2 c1 c2 b x c e1_typing c1_res_typing e2_typing d_bind_comp ->
    T.print (FStar.Printf.sprintf "Incremental tc bind0 with b: %s\n" (P.binder_to_string b));
    if Tm_Bind? e1.term
    then let _ = T.print (FStar.Printf.sprintf "Incremental tc bind0 e1.term is a bind: %s\n" (P.st_term_to_string e1)) in
         let ropt = incremental_tc_bind1 #g #e1 #c1 e1_typing t0 t1 in
         match ropt with
         | Some (| e1, e1_typing |) ->
           Some (| _, T_Bind _ e1 e2 c1 c2 b x c e1_typing c1_res_typing e2_typing d_bind_comp |)
         | None -> None
    else if T_Frame? d || T_Sub? d || T_Equiv? d
    then incremental_tc_trivial d (fun e_typing -> incremental_tc_bind0 e_typing t0 t1)
    else T.fail (FStar.Printf.sprintf "Unexpected derivation(2) with %s" (tag_of_st_typing d))
  
  | _ ->
    if T_Frame? d || T_Sub? d || T_Equiv? d
    then incremental_tc_trivial d (fun e_typing -> incremental_tc_bind0 e_typing t0 t1)
    else T.fail (FStar.Printf.sprintf "Unexpected derivation(1) with %s" (tag_of_st_typing d))

and incremental_tc_bind1 (#g:env) (#t:st_term) (#c:comp_st)
  (d:st_typing g t c)
  (t0:st_term)
  (t1:st_term { both_binds t0 t1 })
  : T.Tac (option (t':st_term & st_typing g t' c)) =

  match d with
  | T_Bind g e1 e2 c1 c2 b x c e1_typing c1_res_typing e2_typing d_bind_comp ->
    T.print (FStar.Printf.sprintf "incremental tc bind1, b : %s\n" (P.binder_to_string b));
    if is_internal_binder b
    then let _ = T.print (FStar.Printf.sprintf "incremental tc bind1, internal binder\n") in
         let g = push_binding g x b.binder_ppname (comp_res c1) in
         let e2 = open_st_term_nv e2 (b.binder_ppname, x) in
         let ropt = incremental_tc_bind1 #g #e2 #c2 e2_typing t0 t1 in
         match ropt with
         | Some (| e2, e2_typing |) ->
           let e2_closed = close_st_term e2 x in
           assume (open_st_term_nv e2_closed (b.binder_ppname, x) == e2);
           Some (| _, T_Bind _ e1 e2_closed c1 c2 b x c e1_typing c1_res_typing e2_typing d_bind_comp |)
         | None -> None
    else incremental_tc_bind2 d t0 t1
  
  | _ ->
    if T_Frame? d || T_Sub? d || T_Equiv? d
    then incremental_tc_trivial d (fun e_typing -> incremental_tc_bind1 e_typing t0 t1)
    else T.fail (FStar.Printf.sprintf "Unexpected derivation(2) with %s" (tag_of_st_typing d))

and incremental_tc_bind2 (#g:env) (#t:st_term) (#c:comp_st)
  (d:st_typing g t c)
  (t0:st_term)
  (t1:st_term { both_binds t0 t1 })
  : T.Tac (option (t':st_term & st_typing g t' c)) =
  
  match d with
  | T_Bind g e1 e2 c1 c2 b x c e1_typing c1_res_typing e2_typing d_bind_comp ->
    let ropt =
      match t0.term, t1.term with
      | Tm_Bind {binder=binder0; body=body0},
        Tm_Bind {binder=binder1; body=body1} ->
        T.print (FStar.Printf.sprintf "incremental tc bind2 b: %s, b0: %s, b1: %s\n"
          (P.binder_to_string b)
          (P.binder_to_string binder0)
          (P.binder_to_string binder1));
        if eq_binder binder0 binder1
        then Some (body0, body1)
        else None
      | Tm_TotBind {binder=binder0; body=body0},
        Tm_TotBind {binder=binder1; body=body1} ->
        if eq_binder binder0 binder1
        then Some (body0, body1)
        else None in
    begin
      match ropt with
      | None -> None
      | Some (body0, body1) ->
        let t0 = open_st_term_nv body0 (b.binder_ppname, x) in
        let t1 = open_st_term_nv body1 (b.binder_ppname, x) in
        let g = push_binding g x b.binder_ppname (comp_res c1) in
        let e2 = open_st_term_nv e2 (b.binder_ppname, x) in
        let ropt = incremental_tc #g #e2 #c2 e2_typing t0 t1 in
        match ropt with
        | Some (| e2, e2_typing |) ->
          let e2_closed = close_st_term e2 x in
          assume (open_st_term_nv e2_closed (b.binder_ppname, x) == e2);
          Some (| _, T_Bind _ e1 e2_closed c1 c2 b x c e1_typing c1_res_typing e2_typing d_bind_comp |)
        | None -> None
    end
  | _ ->
    if T_Frame? d || T_Sub? d || T_Equiv? d
    then incremental_tc_trivial d (fun e_typing -> incremental_tc_bind2 e_typing t0 t1)
    else T.fail (FStar.Printf.sprintf "Unexpected derivation(3) with %s" (tag_of_st_typing d))

and incremental_tc_admit (#g:env) (#t:st_term) (#c:comp_st)
  (d:st_typing g t c)
  (t0:st_term)
  (t1:st_term { Tm_Admit? t0.term })
  : T.Tac (option (t':st_term &
                   st_typing g t' c)) =
  
  T.print (FStar.Printf.sprintf "Reached a point with e2: %s\n" (P.st_term_to_string t1));
  let ct = Pulse.Typing.Metatheory.Base.st_typing_correctness d in
  let post_hint : post_hint_for_env g = post_hint_from_comp_typing ct in
  let res =
    check g (comp_pre c) (magic ()) (Some post_hint) ppname_default t1 in
  let (| t', c', t'_typing |) =
    apply_checker_result_k res ppname_default in
  T.print (FStar.Printf.sprintf "Typechecked with e: %s\n" (P.st_term_to_string t'));
  assume (stateful_comp c');
  assume (c_match c c');
  if obs_match c c' then begin
    c_and_obs_match c c';
    assert (c == c');
    Some (| t', t'_typing |)
  end
  else T.fail "Obs did not match!\n"

and incremental_tc (#g:env) (#t:st_term) (#c:comp_st)
  (d:st_typing g t c)
  (t0:st_term)
  (t1:st_term)
  : T.Tac (option (t':st_term &
                   st_typing g t' c)) =

  T.print (FStar.Printf.sprintf "incremental tc, t: %s\n, t0: %s\n, t1:%s\n"
    (P.st_term_to_string t)
    (P.st_term_to_string t0)
    (P.st_term_to_string t1));
  match t0.term, t1.term with
  | Tm_Bind _, Tm_Bind _ ->
    incremental_tc_bind0 #g #t #c d t0 t1

  | Tm_TotBind _, Tm_TotBind _ ->
    incremental_tc_bind0 #g #t #c d t0 t1
  
  | Tm_Admit _, _ ->
    incremental_tc_admit #g #t #c d t0 t1

  | Tm_Abs {body=body0}, Tm_Abs {body=body1} ->
    (match d with
     | T_Abs _ x q b u body c d_bt d_body ->
       let g' = push_binding g x b.binder_ppname b.binder_ty in
       let body0 = open_st_term_nv body0 (b.binder_ppname, x) in
       let body1 = open_st_term_nv body1 (b.binder_ppname, x) in
       let ropt = incremental_tc d_body body0 body1 in
       (match ropt with
        | None -> None
        | Some (| body, body_typing |) ->
          let body_closed = close_st_term body x in
          assume (open_st_term_nv body_closed (b.binder_ppname, x) == body);
          Some (| _, T_Abs _ x q b u body_closed c d_bt body_typing |))
     | _ -> T.fail "Expected T_Abs")

  
  | _, _ ->
    T.print (FStar.Printf.sprintf "Unhandled case with t0 and t1: %s and %s\n"
               (P.tag_of_st_term t0)
               (P.tag_of_st_term t1));
    T.fail "main fail"

and incremental_tc_trivial (#g:env) (#t:st_term) (#c:comp_st)
  (d:st_typing g t c { T_Sub? d \/ T_Frame? d \/ T_Equiv? d })
  (f:(#g:env -> #t:st_term -> #c:comp_st -> st_typing g t c -> T.Tac (option (t':st_term & st_typing g t' c))))
  : T.Tac (option (t':st_term &
                   st_typing g t' c)) =
  
  match d with
  | T_Sub g e c c' e_typing st_sub_typing ->
    assume (stateful_comp c);
    begin
      let ropt = f e_typing in
      match ropt with
        | Some (| e, e_typing |) ->
          Some (| _, T_Sub g e c c' e_typing st_sub_typing |)
        | None -> None
    end

  | T_Equiv g e c c' e_typing d_equiv ->
    begin
      let ropt = f e_typing in
      match ropt with
      | Some (| e, e_typing |) ->
        Some (| _, T_Equiv g e c c' e_typing d_equiv |)
      | None -> None
    end

  | T_Frame g e c frame frame_typing e_typing ->
    begin
      let ropt = f e_typing in
      match ropt with
      | Some (| e, e_typing |) ->
        Some (| _, T_Frame g e c frame frame_typing e_typing |)
      | None -> None
    end
  

#push-options "--z3rlimit_factor 8"
let try_incremental_checking (g:env) (d:decl)
  : T.Tac (option (t:st_term & c:comp & st_typing g t c)) =

  let copt = Pulse.RuntimeUtils.get_extension_state (fstar_env g) in
  match copt with
  | None ->
    T.print ("Could not find anything in the cache, not incremental\n");
    None
  | Some { cache_decl; cache_typing } ->
    T.print ("Found something in the cache, trying incremental\n");
    let FnDecl { id=id0; isrec=isrec0; bs=bs0; comp=comp0; meas=meas0; body=body0 } = cache_decl in
    let FnDecl { id=id1; isrec=isrec1; bs=bs1; comp=comp1; meas=meas1; body=body1 } = d.d in

    match is_incremental_st_term body0 body1 with
    | None -> None
    | Some e ->
      T.print (FStar.Printf.sprintf "Incremental with e as %s\n" (P.st_term_to_string e));
      let (| g_c, t_c, c_c, d |) = cache_typing in
      // TODO: need to make sure that g' is same as g
      assume (g == g_c);
      assume (stateful_comp c_c);
      assume (~ (Nil? bs0));
      assume (~ (Nil? bs1));
      let ropt = incremental_tc #g_c #t_c #c_c d (mk_abs g bs0 body0 comp0) (mk_abs g bs1 body1 comp1) in
      match ropt with
      | None -> None
      | Some (| _, d |) -> Some (| _, _, d |)

#push-options "--z3rlimit_factor 4 --fuel 1 --ifuel 1"
let check_fndecl
    (d : decl{FnDecl? d.d})
    (g : Soundness.Common.stt_env{bindings g == []})
    (pre : term) (pre_typing : tot_typing g pre tm_vprop)
  : T.Tac (RT.dsl_tac_result_t (fstar_env g))
= 

  (* Maybe add a recursive knot before starting *)
  let FnDecl fn_d = d.d in
  let nm_orig = fst (inspect_ident fn_d.id) in // keep the original name
  let d =
    if fn_d.isrec
    then Recursion.add_knot g d.range d
    else d
  in

  let FnDecl { id; isrec; bs; comp; meas; body } = d.d in
  let nm_aux = fst (inspect_ident id) in

  if Nil? bs then fail g (Some d.range) "main: FnDecl does not have binders";
  let rng = body.range in

  let (| tm_abs, c, t_typing |), incr =
    match try_incremental_checking g d with
    | Some r -> r, true
    | None ->
      let tm_abs = mk_abs g bs body comp in
      debug_main g (fun _ -> Printf.sprintf "\nbody after mk_abs:\n%s\n" (P.st_term_to_string tm_abs));    
      (Pulse.Checker.Abs.check_abs g tm_abs Pulse.Checker.check), false in

  Pulse.RuntimeUtils.set_extension_state (fstar_env g) {
    cache_decl = d.d;
    cache_typing = (| g, tm_abs, c, t_typing |)
  };

  Pulse.Checker.Prover.debug_prover g
    (fun _ -> Printf.sprintf "\ncheck call returned in main with:\n%s\nat type %s\n"
              (P.st_term_to_string tm_abs)
              (P.comp_to_string c));
  debug_main g
    (fun _ -> Printf.sprintf "\nchecker call returned in main with:\n%s\nderivation=%s\n"
              (P.st_term_to_string tm_abs)
              (Pulse.Typing.Printer.print_st_typing t_typing));

  T.print (FStar.Printf.sprintf "Elaborated (%s): %s\n"
    (if incr then "incremental" else "not-incremental")
    (P.st_term_to_string tm_abs));

  let refl_t = elab_comp c in
  let refl_e = Pulse.RuntimeUtils.embed_st_term_for_extraction #st_term tm_abs (Some rng) in
  let blob = "pulse", refl_e in
  soundness_lemma g tm_abs c t_typing;
  let main_decl =
    let nm = fst (inspect_ident id) in
    if T.ext_getv "pulse:elab_derivation" <> ""
    then RT.mk_checked_let (fstar_env g) nm (elab_st_typing t_typing) refl_t
    else Pulse.Reflection.Util.mk_opaque_let (fstar_env g) nm (elab_st_typing t_typing) refl_t
  in
  (* Set the blob *)
  let main_decl =
    let (chk, se, _) = main_decl in
    let se = 
      if fn_d.isrec
      then (
        let nm = R.pack_ln (R.Tv_Const (R.C_String nm_orig)) in
        let attribute = `("pulse.recursive", `#(nm)) in
        let se = RU.add_attribute se (`(noextract_to "krml")) in
        let se = RU.add_noextract_qual se in
        let se : T.sigelt = RU.add_attribute se attribute in
        se
      )
      else se
    in
    (chk, se, Some blob)
  in
  let recursive_decls =
    if fn_d.isrec
    then Rec.tie_knot g rng nm_orig nm_aux d refl_t blob
    else []
  in
  main_decl :: recursive_decls

let main' (nm:string) (d:decl) (pre:term) (g:RT.fstar_top_env)
  : T.Tac (RT.dsl_tac_result_t g)
  = match Pulse.Soundness.Common.check_top_level_environment g with
    | None -> T.fail "pulse main: top-level environment does not include stt at the expected types"
    | Some g ->
      if RU.debug_at_level (fstar_env g) "Pulse" then 
        T.print (Printf.sprintf "About to check pulse decl:\n%s\n" (P.decl_to_string d));
      let (| pre, ty, pre_typing |) = Pulse.Checker.Pure.compute_tot_term_type g pre in
      if not (eq_tm ty tm_vprop) then
        fail g (Some pre.range) "pulse main: cannot typecheck pre at type vprop"; //fix range
      let pre_typing : tot_typing g pre tm_vprop = pre_typing in
      match d.d with
      | FnDecl _ ->
        check_fndecl d g pre pre_typing

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

let main nm t pre : RT.dsl_tac_t = fun g ->
  (* We use the SMT policy by default, to collect goals in the
  proofstate and discharge them all at the end, potentially joining
  them (see below). But it can be overriden to SMTSync by `--ext
  pulse:guard_policy=SMTSync`. *)
  if ext_getv "pulse:guard_policy" = "SMTSync" then
    set_guard_policy SMTSync
  else
    set_guard_policy SMT;

  let res = main' nm t pre g in

  if ext_getv "pulse:join" = "1"
     (* || ext_getv "pulse:join" <> "" *)
     // ^ Uncomment to make it true by default.
  then
    join_smt_goals();
  res

[@@plugin]
let check_pulse (namespaces:list string)
                (module_abbrevs:list (string & string))
                (content:string)
                (file_name:string)
                (line col:int)
                (nm:string)
  : RT.dsl_tac_t
  = fun env ->
      match PulseSyntaxExtension.ASTBuilder.parse_pulse env namespaces module_abbrevs content file_name line col with
      | Inl decl ->
        main nm decl tm_emp env

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
