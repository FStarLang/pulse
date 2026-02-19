(*
   Copyright 2026 Microsoft Research

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

module Pulse.Checker.Cleanup

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module RU = Pulse.RuntimeUtils

let extend_post_hint_for_cleanup (g:env) (p:post_hint_for_env g)
                                 (conjunct:term)
  : T.Tac (q:post_hint_for_env g {
      q.post == tm_star p.post conjunct /\
      q.ret_ty == p.ret_ty /\
      q.u == p.u /\
      q.effect_annot == p.effect_annot
    })
  = let x = fresh g in
    let pg = push_binding p.g x ppname_default p.ret_ty in
    let conjunct_typing : tot_typing pg (open_term conjunct x) tm_slprop = RU.magic () in
    let p_post_typing : tot_typing pg (open_term p.post x) tm_slprop = RU.magic () in
    let new_post = tm_star p.post conjunct in
    let new_post_typing : tot_typing pg (open_term new_post x) tm_slprop =
      Pulse.Typing.star_typing p_post_typing conjunct_typing in
    assume (fresh_wrt x p.g (freevars new_post));
    let new_post_abs_typing = post_typing_as_abstraction new_post_typing in
    assume (post_hint_for_env_p g { p with
      post = new_post;
      x;
      post_typing_src = new_post_typing;
      post_typing = new_post_abs_typing });
    { p with
      post = new_post;
      x;
      post_typing_src = new_post_typing;
      post_typing = new_post_abs_typing }

#push-options "--z3rlimit_factor 10 --fuel 0 --ifuel 0"
let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_Cleanup? t.term })
  (check:check_t)
: T.Tac (checker_result_t g pre post_hint)
= allow_invert post_hint;
  match post_hint with
  | NoHint | TypeHint _ ->
    fail g (Some t.range)
      "cleanup requires an annotated post-condition"

  | PostHint { effect_annot = EffectAnnotGhost _ }
  | PostHint { effect_annot = EffectAnnotAtomic _ }
  | PostHint { effect_annot = EffectAnnotAtomicOrGhost _ } ->
    fail g (Some t.range)
      "cleanup is only allowed in non-ghost and non-atomic code"

  | PostHint post ->
    let g = push_context "check_cleanup" t.range g in
    let Tm_Cleanup { cleanup_pre=cpre; handler; body } = t.term in
    // Check cleanup_pre is a valid slprop
    let (| cpre, cpre_typing |) = check_slprop g cpre in
    // Extend post_hint: body's postcondition must include cpre
    let body_post : post_hint_for_env g = extend_post_hint_for_cleanup g post cpre in
    // Extend env: push BindingPost so goto labels see cpre
    let g' = push_post g cpre in
    let pre_typing' : tot_typing g' pre tm_slprop = RU.magic () in
    assume post_hint_for_env_p g' body_post;
    let body_post' : post_hint_for_env g' = body_post in
    // Check body with extended env and post_hint
    let body_r = check g' pre pre_typing' (PostHint body_post') res_ppname body in
    let (| body', c_body, body_typing |) = apply_checker_result_k #g' #pre #body_post body_r res_ppname in
    // The body's postcondition should be (post ** cpre)
    // Now check the handler with cpre as (part of) precondition
    // After body, context is (post ** cpre); handler consumes cpre
    // Overall cleanup comp has the original post (without cpre)
    let c = C_ST { u=comp_u c_body; res=comp_res c_body; pre; post=post.post } in
    let d = T_Cleanup g cpre handler body' c_body c_body c body_typing (RU.magic ()) in
    let (| c'', typing'' |) = match_comp_res_with_post_hint d post_hint in
    prove_post_hint
      (try_frame_pre false #g pre_typing (|_, c'', typing''|) res_ppname)
      post_hint
      t.range
#pop-options
