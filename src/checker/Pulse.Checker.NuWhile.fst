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

module Pulse.Checker.NuWhile

open Pulse
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover
open Pulse.Show
open Pulse.PP
open Pulse.Reflection.Util { mk_abs }

module T = FStar.Tactics.V2
module RU = Pulse.RuntimeUtils
module Metatheory = Pulse.Typing.Metatheory

let debug () : T.Tac bool =
  RU.debug_at_level (T.top_env ()) "nuwhile"

let unit_is_type0 (g:env) : tot_typing g (`unit) (tm_type T.Uv_Zero) = RU.magic ()

#set-options "--z3rlimit 20"

let rec drop (n:nat) (xs : list 'a) : T.Tac (list 'a) =
  match n, xs with
  | 0, _ -> xs
  | _, [] -> []
  | _, x::xs' -> drop (n-1) xs'

let rec take (n:nat) (xs : list 'a) : T.Tac (list 'a) =
  match n, xs with
  | 0, _ -> []
  | _, [] -> []
  | _, x::xs' ->
    let xs'' = take (n-1) xs' in
    x::xs''

let close1
  (x : var)
  (nm : ppname)
  (xt : typ)
  (ctxt : term)
  : T.Tac term
= 
  if not (x `Set.mem` freevars ctxt) then
    (* Easy case, it doesn't appear so just ignore it. (TODO: consider
    refinements...) *)
    ctxt
  else (
    // T.print (Printf.sprintf "closing %s for term %s" (show #int x) (show ctxt));
    let b : binder = {binder_ppname = nm; binder_ty = xt; binder_attrs = Sealed.seal []} in
    (* u0 is wrong *)
    let ctxt = Syntax.Naming.close_term ctxt x in
    let res = tm_exists_sl u0 b ctxt in
    // T.print (Printf.sprintf "closing %s for term %s done, res = %s" (show #int x) (show ctxt) (show res));
    res
  )

let close1_wt
  (#g:env)
  (x : var{~ (x `Set.mem` dom g)})
  (nm : ppname)
  (xt : typ)
  (ctxt : term)
  (ctxt_typing : tot_typing (push_binding g x nm xt) ctxt tm_slprop)
  : T.Tac (ctxt':term & tot_typing g ctxt' tm_slprop)
= admit()

let close_into
  (#g2:env)
  (ctxt : term)
  (ctxt_typing : tot_typing g2 ctxt tm_slprop)
  (g1 : env{g2 `env_extends` g1})
  : T.Tac (ctxt':term & tot_typing g1 ctxt' tm_slprop)
=
  let extra_vars = take (List.length (bindings g2) - List.length (bindings g1)) (bindings g2) in
  // assert (g2 == push_env g1 extra_vars);
  let ctxt' =
    T.fold_right (fun (v,t) ctxt' ->
      (* huge hack for the proof, this will need an aux lte rec instead of a fold. *)
      let ctxt'' = close1 v ppname_default t ctxt' in
      ctxt''
    ) extra_vars ctxt
  in
  let d : tot_typing g1 ctxt' tm_slprop = RU.magic () in
  (| ctxt', d |)


#set-options "--z3rlimit 40"

let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term{Tm_NuWhile? t.term})
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =
  admit();
  let g = push_context "nuwhile loop" t.range g in
  let Tm_NuWhile { condition; body; invariant; } = t.term in
  let (| invariant, invariant_typing |) = check_slprop g invariant in

  let invariant_typing_orig : tot_typing g invariant tm_slprop = invariant_typing in

  (* First thing we do is prove the invariant. Essentially
  this is very similar to having `assert invariant` at this point.
  After doing so, we split the context into invariant ** frame.
  We keep the frame--- it is passed through to the checks for
  cond and body. *)

  let no_uvs = mk_env (fstar_env g) in

  let (| g1, nts, _, frame, k_frame |) =
    Prover.prove false pre_typing no_uvs invariant_typing
  in

  Tactics.BreakVC.break_vc ();

  let invariant_typing : tot_typing g1 invariant tm_slprop =
    Typing.Metatheory.tot_typing_weakening_standard g invariant_typing g1
  in

  let frame_typing : tot_typing g1 frame tm_slprop =
    (* Prover should ensure this... *)
    RU.magic ()
  in
  let frame_typing_orig : tot_typing g frame tm_slprop =
    (* I think? *)
    RU.magic ()
  in

  if debug () then
    info_doc g (Some t.range) [
      text "Proved invariant";
      text "Frame:" ^/^ pp frame;
    ];

  (* We proved the invariant and got a frame. We now check
  the condition in the *full* context of inv ** frame. This
  is so we don't have to specify random fixed resources in
  the invariant. *)

  let cond_ppname = mk_ppname_no_range "cond" in
  let (| cond_x, __g2, _booltyping, (| ctxt_after_cond, ctxt_after_cond_typing |), k_cond |) =
    check
      (push_context "check_while_condition" condition.range g1)
      (tm_star invariant frame)
      (star_typing invariant_typing frame_typing)
      None
      cond_ppname
      condition
  in

  let flipped_g2 =
    let extra_vars = take (List.length (bindings __g2) - List.length (bindings g1)) (bindings __g2) in
    T.guard (Cons? extra_vars);
    (* note: snoc list *)
    let last :: init = extra_vars in
    assume (~(Set.mem (fst last) (dom g1)));
    let g = push_binding g1 (fst last) ppname_default (snd last) in
    let g = T.fold_right (fun b g ->
      let x, t = b in
      assume (~(Set.mem x (dom g)));
      push_binding g x ppname_default t
    ) init g
    in
    g
  in
  let g2 = flipped_g2 in
  let ctxt_after_cond_typing : tot_typing g2 ctxt_after_cond tm_slprop =
    RU.magic ()
  in
  assume (g2 `env_extends` g1);

  if debug () then
    info_doc g (Some t.range) [
      text "After condition:" ^/^ pp ctxt_after_cond;
      text "g2:" ^/^ pp g2;
    ];

  let cpost =
    let b : T.binder = {
      uniq = cond_x;
      ppname = cond_ppname.name;
      sort = (`bool);
      qual = T.Q_Explicit;
      attrs = [];
    } in
    assume (~(Set.mem cond_x (dom g)));
    let g1x = push_binding g cond_x ppname_default (`bool) in
    assume (env_extends g2 g1x);
    let (| ctxt_after_cond, _|) = close_into #g2 ctxt_after_cond ctxt_after_cond_typing g1x in
    if debug () then
      info_doc g (Some t.range) [
        text "GG ctxt_after_cond:" ^/^ pp ctxt_after_cond;
        text "GG cond_x = " ^/^ pp #int cond_x;
      ];
    T.mk_abs [b] ctxt_after_cond
  in
  if debug () then
    info_doc g (Some t.range) [
      text "Proved condition";
      text "Condition:" ^/^ pp condition;
      text "After condition:" ^/^ pp ctxt_after_cond;
      text "cpost:" ^/^ pp cpost;
    ];
  let cpost_typing : tot_typing g1 cpost (mk_abs (`bool) T.Q_Explicit tm_slprop) = RU.magic () in
    // Metatheory.tot_typing_weakening_standard g1 (star_typing invariant_typing frame_typing) g2

  (* Check the body, in the context after checking the condition,
     but also adding a pure fact that the condition is true. *)
    assert (g2 `env_extends` g1);
    let cond_x_tm = tm_var {nm_index=cond_x;nm_ppname=cond_ppname} in
    let ctxt_after_cond_true =
      tm_star ctxt_after_cond (tm_pure (mk_eq2 T.Uv_Zero (`bool) cond_x_tm (`true)))
    in
    let ctxt_after_cond_true_typing : tot_typing g2 ctxt_after_cond_true tm_slprop =
      star_typing #_ #ctxt_after_cond #(tm_pure (mk_eq2 T.Uv_Zero (`bool) cond_x_tm (`true)))
        ctxt_after_cond_typing (RU.magic ())
    in
    let post = tm_star invariant frame in
    let body_st_comp : st_comp =
      {
        pre = tm_emp; // irrelevant
        post = post;
        res = (`unit);
        u = T.Uv_Zero
      }
    in
    let body_comp : comp = C_ST body_st_comp in
    let x = fresh g2 in
    assume (~(x `Set.mem` freevars post)); // prove
    assume (open_term post x == post); // prove
    let g2x = push_binding g2 x ppname_default (`unit) in
    assert (g2 `env_extends` g1);
    assume (g2x `env_extends` g1); // trivial?
    let body_comp_typing : comp_typing_u g2 body_comp =
      CT_ST g2 body_st_comp <| STC g2 body_st_comp x
                     (unit_is_type0 _)
                     emp_typing
                     (Metatheory.tot_typing_weakening_standard
                       g1
                       (star_typing invariant_typing frame_typing)
                       g2x)
    in
  let body_hint : post_hint_for_env g2 = post_hint_from_comp_typing body_comp_typing in
  let after_body =
    check
      (push_context "check_while_body" body.range g2)
      ctxt_after_cond_true
      ctxt_after_cond_true_typing
      (Some body_hint)
      res_ppname
      body
  in
  let (| body', body'_comp, body'_typing |) =
    apply_checker_result_k after_body (mk_ppname_no_range "_nuwhile_b")
  in
  let (| body', body'_comp, body'_typing |) =
    let pak () : Typing.Combinators.st_typing_in_ctxt __g2 ctxt_after_cond_true (Some body_hint) =
      admit();
      (| body', body'_comp, body'_typing |)
    in
    admit();
    k_cond (Some body_hint) (pak ())
  in
  admit();

  info_doc g (Some t.range) [
    text "NUWHILE After body:" ^/^ pp body';
  ];

  let d : st_typing g1 _ _ =
    T_NuWhile
    g1
    (tm_star invariant frame)
    condition
    cpost body'
    (star_typing invariant_typing frame_typing)
    cpost_typing
  in
  assume (comp_pre (comp_nuwhile (tm_star invariant frame) cpost) == pre);
  assume (comp_post_matches_hint (comp_nuwhile (tm_star invariant frame) cpost) post_hint);
  let (| t, c, d |) = k_frame post_hint (| _, _, d |) in
  prove_post_hint
    (try_frame_pre false pre_typing (match_comp_res_with_post_hint d post_hint) res_ppname)
    post_hint t.range
