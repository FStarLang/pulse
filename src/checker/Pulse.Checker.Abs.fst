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

module Pulse.Checker.Abs
#set-options "--z3refresh" //stabilize some flaky proofs
module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Base

module RT = FStar.Reflection.Typing
module P = Pulse.Syntax.Printer
module FV = Pulse.Typing.FV
module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module RU = Pulse.RuntimeUtils
module Env = Pulse.Typing.Env
module PTU = Pulse.Typing.Util
module U = Pulse.Syntax.Pure

open Pulse.Show

let debug_abs g (s: unit -> T.Tac string) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.abs"
  then T.print (s ())

let tc_term_phase1_with_type (g: env) (t:term) (must_tot:bool) (expected_typ: term) : T.Tac term =
  let t = R.pack_ln (R.Tv_AscribedT t expected_typ None false) in
  let t, _ = tc_term_phase1 g t must_tot in
  match R.inspect_ln t with
  | R.Tv_AscribedT t _ _ _ -> t
  | _ -> t

let qualifier_compat g r (q:option qualifier) (q':T.aqualv) : T.Tac unit =
  match q, q' with
  | None, T.Q_Explicit -> ()
  | Some Implicit, T.Q_Implicit 
  | Some Implicit, T.Q_Meta _ -> ()
  | Some TcArg, T.Q_Meta _ -> ()
  | Some (Meta _), T.Q_Meta _ -> ()
  | _ -> Env.fail g (Some r) "Unexpected binder qualifier"

// let check_qual g (q:T.aqualv) : T.Tac T.aqualv =
//   match q with
//   | T.Q_Meta t ->
//     let t = T.tc (elab_env g) t in
//     (* FIXME *)
//     T.Q_Meta t
//   | q -> q
let check_qual g (q:qualifier) : T.Tac qualifier =
  match q with
  | Meta t ->
    let ty = (`(unit -> T.Tac u#0 unit)) in
    // let t = T.pack (T.Tv_AscribedT t ty None false) in
    let t =
      (* This makes sure to elaborate the meta qualifier so it
      matches exactly with what F* would generate. If not, we get
      weird errors using an `fn` in the implementation and a `val .. : stt`
      in the interface, or vice-versa, since they don't fully match. *)
      match T.instantiate_implicits (elab_env g) t (Some ty) false with
      | Some (_, t, _), _ -> t
      | None, iss ->
        T.log_issues iss;
        T.fail ("check_qual: failed to elaborate term " ^ show t)
    in
    Meta t
  | q -> q

let sub_effect_comp g r (asc:comp_ascription) (c_computed:comp) : T.Tac (option (c2:comp & lift_comp g c_computed c2)) =
  let nop = None in
  match asc with
  | None -> nop
  | Some c ->
    match c_computed, c with
    | C_Tot t1, C_Tot t2 -> nop
    | C_ST _, C_ST _ -> nop
    | C_STGhost _ _, C_STGhost _ _ -> nop
    | C_STAtomic i Neutral c1, C_STGhost _ _ ->
      let lift = Lift_Neutral_Ghost g c_computed in
      Some (| C_STGhost i c1, lift |)
    | C_STAtomic i o1 c1, C_STAtomic j o2 c2 ->
      if sub_observability o1 o2
      then let lift = Lift_Observability g c_computed o2 in
           Some (| C_STAtomic i o2 c1, lift |)
      else nop

    (* FIXME: more lifts here *) 
    | _ -> nop

let check_effect_annotation g r (asc:comp_ascription) (c_computed:comp) : T.Tac (c2:comp & st_sub g c_computed c2) =
  let nop = (| c_computed, STS_Refl _ _ |) in
  match asc with
  | None -> nop
  | Some c ->
    match c, c_computed with
    | C_Tot _, C_Tot _
    | C_ST _, C_ST _  -> nop
    | C_STGhost i c1, C_STGhost j c2
    | C_STAtomic i Neutral c1, C_STAtomic j Neutral c2
    | C_STAtomic i Observable c1, C_STAtomic j Observable c2 ->
      // This should be true since we used the annotated computation type
      // to check the body of the function, but this fact is not exposed
      // by the checker and post hints yet.
      assume (c1 == c2);

      if eq_tm i j then (
        assert (c == c_computed);
        nop
      ) else
      
      let b = mk_binder "res" Range.range_0 c2.res in
      let phi = tm_inames_subset j i in
      let typing = tm_inames_subset_typing g j i in
      // Or:
      // let typing = core_check_tot_term g phi tm_prop in
      let tok = T.with_policy T.ForceSMT (fun () -> try_check_prop_validity g phi typing) in
      if None? tok then (
        let open Pulse.PP in
        fail_doc g (Some (RU.range_of_term i)) [
          prefix 4 1 (text "Annotated effect expects only invariants in") (pp i) ^/^
          prefix 4 1 (text "to be opened; but computed effect claims that invariants") (pp j) ^/^
          text "are opened"
        ]
      );

      let Some tok = tok in

      let d_sub : st_sub g c_computed c =
        match c_computed with
        | C_STAtomic _ obs _ -> STS_AtomicInvs g c2 j i obs obs tok
        | C_STGhost _ _ -> STS_GhostInvs g c2 j i tok
      in
      (| c, d_sub |)

    | _, _ ->
      let open Pulse.PP in
      fail_doc g (Some r) [
        prefix 4 1 (text "Expected effect")
                      (arbitrary_string (P.tag_of_comp c)) ^/^
        prefix 4 1 (text "but this function body has effect")
                      (arbitrary_string (P.tag_of_comp c_computed))
      ]


#push-options "--z3rlimit_factor 2 --fuel 0 --ifuel 1"
let maybe_rewrite_body_typing
      (#g:_) (#e:st_term) (#c:comp)
      (d:st_typing g e c)
      (asc:comp_ascription)
  : T.Tac (c':comp & st_typing g e c')
  = match asc with
    | None ->  (| c, d |)
    | Some (C_Tot t) -> (
      match c with
      | C_Tot t' -> (
        let t, _ = Pulse.Checker.Pure.instantiate_term_implicits g t None false in
        let (| u, t_typing |) = Pulse.Checker.Pure.check_universe g t in
        match Pulse.Checker.Base.norm_st_typing_inverse
                 #_ #_ #t' d t t_typing [hnf;delta]
        with
        | None -> 
          Env.fail g (Some e.range) "Inferred type is incompatible with annotation"
        | Some d -> 
          debug_abs g 
            (fun _ -> Printf.sprintf "maybe_rewrite_body_typing:{\nfrom %s\nto %s}\n" 
              (P.comp_to_string c)
              (P.comp_to_string (C_Tot t)));
          (| C_Tot t, d |)
      )
      | _ -> 
      Env.fail g (Some e.range) "Inferred type is incompatible with annotation"
    )
    | Some c -> 
      let st = st_comp_of_comp c in
      Env.fail g (Some (RU.range_of_term st.pre)) "Unexpected annotation on a function body"
#pop-options

let open_ascription (c:comp_ascription) (nv:nvar) : comp_ascription =
  let t = term_of_nvar nv in
  subst_ascription c [RT.DT 0 t]
let close_ascription (c:comp_ascription) (nv:nvar) : comp_ascription =
  subst_ascription c [RT.ND (snd nv) 0]

let preprocess_post g ret_ty_opt post =
  let x = fresh g in
  let ret_ty =
      match ret_ty_opt with
      | None -> wr RT.unit_ty FStar.Range.range_0
      | Some t -> t
  in
  let ret_ty = tc_term_phase1_with_type g ret_ty true (tm_type u_unknown) in
  let post = tc_term_phase1_with_type (push_binding g x ppname_default ret_ty) (open_term_nv post (v_as_nv x)) true tm_slprop in
  let post' = close_term post x in
  post'

let set_inames inames (c:comp) : comp =
  match c with
  | C_STAtomic _ obs st -> C_STAtomic inames obs st
  | C_STGhost  _ st     -> C_STGhost inames st
  | _ -> c

#push-options "--admit_smt_queries true"
let rec check_abs_core
  (g:env)
  (t:st_term{Tm_Abs? t.term})
  (check:check_t)
  #fin_res_t (finalize: unit -> T.Tac fin_res_t)
  : T.Tac (fin_res_t & t:st_term & c:comp & st_typing g t c) =
  //warn g (Some t.range) (Printf.sprintf "check_abs_core, t = %s" (P.st_term_to_string t));
  let range = t.range in
  debug_abs g (fun _ -> Printf.sprintf "check_abs_core\n\t%s\n"
              (P.st_term_to_string t));
  let Tm_Abs { b = {binder_ty=t;binder_ppname=ppname;binder_attrs}; q=qual; ascription=asc; body } = t.term in //pre=pre_hint; body; ret_ty; post=post_hint_body } =
    (*  (fun (x:t) -> {pre_hint} body : t { post_hint } *)
    let t = tc_term_phase1_with_type g t true (tm_type u_unknown) in
    let x = fresh g in
    let px = ppname, x in
    let var = tm_var {nm_ppname=ppname;nm_index=x} in
    let g' = push_binding g x ppname t in
    let body_opened = open_st_term_nv body px in
    let asc = open_ascription asc px in
    match body_opened.term with
    | Tm_Abs _ ->
      (* Check the opened body *)
      let (| (fr, (| u, t_typing |)), body, c_body, body_typing |) = check_abs_core g' body_opened check fun _ ->
        let fr = finalize () in
        let _ = tc_term_phase1_with_type g t true (tm_type u_unknown) in // wtf?? otherwise unresolved universe uvars with ticked args
        let chk_univ_res = check_universe g t in
        (fr, chk_univ_res) in

      (* First lift into annotated effect *)
      let (| c_body, body_typing |) : ( c_body:comp & st_typing g' body c_body ) =
        match sub_effect_comp g' body.range asc c_body with
        | None -> (| c_body, body_typing |)
        | Some (| c_body, lift |) ->
          let body_typing = T_Lift _ _ _ _ body_typing lift in
          (| c_body, body_typing |)
      in

      (* Check if it matches annotation (if any, likely not), and adjust derivation
      if needed. Currently this only subtypes the invariants. *)
      let (| c_body, d_sub |) = check_effect_annotation g' body.range asc c_body in
      let body_typing = T_Sub _ _ _ _ body_typing d_sub in
      (* Similar to above, fixes the type of the computation if we need to match
      its annotation. TODO: merge these two by adding a tot subtyping (or equiv)
      case to the st_sub judg. *)
      let (| c_body, body_typing |) = maybe_rewrite_body_typing body_typing asc in

      FV.st_typing_freevars body_typing;
      let body_closed = close_st_term body x in
      assume (open_st_term body_closed x == body);

      // instantiate implicits in the attributes
      let binder_attrs =
        binder_attrs
        |> T.unseal
        |> T.map (fun attr -> attr |> (fun t -> instantiate_term_implicits g t None false) |> fst)
        |> FStar.Sealed.seal in

      let b = {binder_ty=t;binder_ppname=ppname;binder_attrs} in
      let qual = T.map_opt (check_qual g) qual in
      let tt = T_Abs g x qual b u body_closed c_body t_typing body_typing in
      let tres = tm_arrow {binder_ty=t;binder_ppname=ppname;binder_attrs} qual (close_comp c_body x) in
      (| fr, _, C_Tot tres, tt |)
    | _ ->
      let elab_c, pre_opened, inames_opened, ret_ty, post_hint_body =
        match asc with
        | None ->
          Env.fail g (Some body.range)
              "Missing annotation on a function body"

        | Some (C_Tot r) -> (
          Env.fail g (Some body.range)
                     (Printf.sprintf 
                       "Incorrect annotation on a function, expected a computation type, got: %s"
                        (P.comp_to_string (C_Tot r)))
        )

        | Some c -> 
          let inames_opened =
            if C_STGhost? c || C_STAtomic? c then
             let inames = open_term_nv (comp_inames c) px in
             let inames = tc_term_phase1_with_type g' inames true tm_inames in
             let inames = T.norm_well_typed_term (elab_env g)
               [primops; iota; zeta; delta_attr ["Pulse.Lib.Core.unfold_check_opens"]]
               inames
             in
             inames
           else
             tm_emp_inames
          in
          set_inames inames_opened c,
          open_term_nv (comp_pre c) px,
          inames_opened,
          Some (open_term_nv (comp_res c) px),
          Some (open_term' (comp_post c) var 1)
      in

      let pre_opened = tc_term_phase1_with_type g' pre_opened true tm_slprop in
      let post_hint_body = T.map_opt (preprocess_post g' ret_ty) post_hint_body in
      let fr = finalize () in
      let t = tc_term_phase1_with_type g t true (tm_type u_unknown) in // wtf?? otherwise unresolved universe uvars with ticked args
      let (| u, t_typing |) = check_universe g t in

      let qual = T.map_opt (check_qual g) qual in

      let (| pre_opened, pre_typing |) =
        (* In some cases F* can mess up the range in error reporting and make it
         point outside of this term. Bound it here. See e.g. Bug59, if we remove
         this bound then the range points to the span between the 'x' and 'y' binders. *)
        RU.with_error_bound (T.range_of_term pre_opened) (fun () -> check_slprop g' pre_opened)
      in
      let pre = close_term pre_opened x in
      let post : post_hint_opt g' =
        match post_hint_body with
        | None ->
          NoHint
        | Some post ->
          let post_hint_typing
            : post_hint_t
            = Pulse.Checker.Base.intro_post_hint
                  (push_context "post_hint_typing" range g')
                  (effect_annot_of_comp elab_c)
                  ret_ty
                  post
          in
          PostHint post_hint_typing
      in

      let ppname_ret = mk_ppname_no_range "_fret" in
      let r  = check g' pre_opened pre_typing post ppname_ret body_opened  in
      let (| post, r |) : (ph:post_hint_opt g' & checker_result_t g' pre_opened ph) =
        match post with
        | PostHint _ -> (| post, r |)
        | _ ->
          (* we support inference of postconditions for functions,
             but this functionality is still unusable from the front end,
             which expects functions to be annotated *)
          let ph = Pulse.Checker.Base.infer_post r in
          let r = Pulse.Checker.Prover.prove_post_hint r (PostHint ph) (T.range_of_term t) in
          (| PostHint ph, r |)
      in
      let (| body, c_body, body_typing |) : st_typing_in_ctxt g' pre_opened post =
        apply_checker_result_k #_ #_ #(PostHint?.v post) r ppname_ret in

      let c_opened : comp_ascription = Some (open_comp_nv elab_c px) in

      (* First lift into annotated effect *)
      let (| c_body, body_typing |) : ( c_body:comp & st_typing g' body c_body ) =
        match sub_effect_comp g' body.range c_opened c_body with
        | None -> (| c_body, body_typing |)
        | Some (| c_body, lift |) ->
          let body_typing = T_Lift _ _ _ _ body_typing lift in
          (| c_body, body_typing |)
      in

      let (| c_body, d_sub |) = check_effect_annotation g' body.range c_opened c_body in
      let body_typing = T_Sub _ _ _ _ body_typing d_sub in

      // let (| c_body, body_typing |) = maybe_rewrite_body_typing body_typing asc in

      FV.st_typing_freevars body_typing;
      let body_closed = close_st_term body x in
      assume (open_st_term body_closed x == body);
      let b = {binder_ty=t;binder_ppname=ppname;binder_attrs} in
      let tt = T_Abs g x qual b u body_closed c_body t_typing body_typing in
      let tres = tm_arrow {binder_ty=t;binder_ppname=ppname;binder_attrs} qual (close_comp c_body x) in

      (| fr, _, C_Tot tres, tt |)
#pop-options

let check_abs (g:env) (t:st_term{Tm_Abs? t.term}) (check:check_t)
  : T.Tac (t:st_term & c:comp & st_typing g t c) =
  let (| _, t, c, t_typing |) =
    check_abs_core g t check fun _ ->
      debug_abs g fun _ -> "phase2 type checking of abs signature..." in
  (| t, c, t_typing |)
