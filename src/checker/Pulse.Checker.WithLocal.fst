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

module Pulse.Checker.WithLocal

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module RU = Pulse.RuntimeUtils

let extend_post_hint_for_local (g:env) (p:post_hint_for_env g)
                               (init_t:term) (x:var { ~ (Set.mem x (dom g)) })
  : T.Tac (q:post_hint_for_env (push_binding g x ppname_default (mk_ref init_t)){ 
      q.post == comp_withlocal_body_post p.post init_t (null_var x) /\
      q.ret_ty == p.ret_ty /\
      q.u == p.u /\
      q.effect_annot == p.effect_annot
      })
  = let conjunct = tm_exists_sl u0 (as_binder init_t) (mk_pts_to init_t (null_var x) (null_bvar 0)) in
    let g' = push_binding g x ppname_default (mk_ref init_t) in
    let c_typing = Pulse.Checker.Pure.core_check_term g' conjunct T.E_Total tm_slprop in
    let res = Pulse.Checker.Base.extend_post_hint g p x (mk_ref init_t) _ c_typing in
    res

let with_local_pre_typing (#g:env) (#pre:term) (pre_typing:tot_typing g pre tm_slprop)
                          (init_t:term) (x:var { ~ (Set.mem x (dom g)) }) (i:term)
  : tot_typing (push_binding g x ppname_default (mk_ref init_t))
               (comp_withlocal_body_pre pre init_t (null_var x) i)
               tm_slprop
  = admit()

#push-options "--z3rlimit_factor 10 --fuel 0 --ifuel 0"

let head_range (t:st_term {Tm_WithLocal? t.term}) : range =
  let Tm_WithLocal { initializer } = t.term in
  (RU.range_of_term initializer)
#restart-solver
let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_WithLocal? t.term })
  (check:check_t)
: T.Tac (checker_result_t g pre post_hint)
= allow_invert post_hint;
  match post_hint with
  | NoHint | TypeHint _ ->
    fail g (Some <| head_range t)
      "Allocating a mutable local variable expects an annotated post-condition"

  | PostHint { effect_annot = EffectAnnotGhost _ }
  | PostHint { effect_annot = EffectAnnotAtomic _ }
  | PostHint { effect_annot = EffectAnnotAtomicOrGhost _ } ->
    fail g (Some <| head_range t)
      "Allocating a mutable local variable is only allowed in non-ghost and non-atomic code"

  | PostHint post ->
    let g = push_context "check_withlocal" t.range g in
    let Tm_WithLocal {binder; initializer=init; body} = t.term in
    let (| init, init_u, init_t, init_t_typing, init_typing |) =
      (* Check against annotation if any *)
      let ty = binder.binder_ty in
      match inspect_term ty with
      | Tm_Unknown -> compute_tot_term_type_and_u g init
      | _ ->
        let (| u, ty_typing |) = check_universe g ty in
        let (| init, init_typing |) = check_term g init T.E_Total ty in
        let ty_typing : universe_of g ty u = ty_typing in
        let init_typing : typing g init T.E_Total ty = init_typing in
        (| init, u, ty, ty_typing, init_typing |)
          <: (t:term & u:universe & ty:term & universe_of g ty u & tot_typing g t ty)
          (* ^ Need this annotation *)
      in
    if not (eq_univ init_u u0)
    then (
      fail g (Some <| head_range t)
          (Printf.sprintf "check_withlocal: allocating a local variable: type %s is not universe zero (computed %s)"
              (P.term_to_string init)
              (P.univ_to_string init_u))
    )
    else
      let x = fresh g in
      let px = binder.binder_ppname, x in
      if x `Set.mem` freevars_st body
      then fail g (Some body.range) (Printf.sprintf "withlocal: %s is free in body" (T.unseal binder.binder_ppname.name))
      else
        let x_tm = term_of_nvar px in
        let g_extended = push_binding g x binder.binder_ppname (mk_ref init_t) in
        let body_pre = comp_withlocal_body_pre pre init_t x_tm init in
        let body_pre_typing = with_local_pre_typing pre_typing init_t x init in
        // elaborating this post here,
        //   so that later we can check the computed post to be equal to this one
        let post : post_hint_for_env g = post in
        if x `Set.mem` freevars post.post
        then fail g None "Impossible! check_withlocal: unexpected name clash in with_local,\
                          please file a bug-report"
        else
          let open Pulse.Typing.Combinators in
          let body_post : post_hint_for_env g_extended = extend_post_hint_for_local g post init_t x in
          let r = check g_extended body_pre body_pre_typing (PostHint body_post) binder.binder_ppname (open_st_term_nv body px) in
          let r: checker_result_t g_extended body_pre (PostHint body_post) = r in
          let (| opened_body, c_body, body_typing |) = apply_checker_result_k #g_extended #body_pre #body_post r binder.binder_ppname in
          let body = close_st_term opened_body x in
          assume (open_st_term (close_st_term opened_body x) x == opened_body);
          let c = C_ST {u=comp_u c_body;res=comp_res c_body;pre;post=post.post} in
          let c_typing =
            let post_typing_rec :post_hint_typing_t g post x = post_hint_typing g post x in
            intro_comp_typing g c pre_typing 
              post_typing_rec.effect_annot_typing
              post_typing_rec.ty_typing
              x post_typing_rec.post_typing
          in
          assert (None? (lookup g x));
          assert (~(Set.mem x (freevars_st body)));
          let d = T_WithLocal g binder.binder_ppname init body init_t c x
            init_typing
            init_t_typing
            c_typing
            body_typing in
          checker_result_for_st_typing (| _, _, d |) res_ppname
#pop-options