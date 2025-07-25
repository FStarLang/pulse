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

module Pulse.Checker.Base

module R = FStar.Reflection.V2
module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing
module Metatheory = Pulse.Typing.Metatheory
module CP = Pulse.Checker.Pure
module RU = Pulse.RuntimeUtils
module FV = Pulse.Typing.FV
open Pulse.Checker.Util
open Pulse.Show

open Pulse.Typing.Combinators
open Pulse.Typing.Metatheory

let debug (g:env) (f: unit -> T.Tac string) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.checker" then
    T.print (f())

let format_failed_goal (g:env) (ctxt:list term) (goal:list term) =
  let terms_to_strings (ts:list term)= T.map Pulse.Syntax.Printer.term_to_string ts in
  let numbered_list ss = 
       let _, s = T.fold_left (fun (i, acc) s -> (i+1, Printf.sprintf "%d. %s" i s :: acc)) (1, []) ss in
       String.concat "\n  " (List.rev s)
  in
  let format_terms (ts:list term) = numbered_list (terms_to_strings ts) in
  Printf.sprintf 
    "Failed to prove the following goals:\n  \
     %s\n\
     The remaining conjuncts in the separation logic context available for use are:\n  \
     %s\n\
     The typing context is:\n  \
     %s\n"
    (format_terms goal)
    (format_terms ctxt)
    (env_to_string g)


let mk_arrow ty t = RT.mk_arrow ty T.Q_Explicit t
let mk_abs ty t = RT.(mk_abs ty T.Q_Explicit t)

let intro_comp_typing (g:env) 
                      (c:comp_st)
                      (pre_typing:tot_typing g (comp_pre c) tm_slprop)
                      (i_typing:effect_annot_typing g (effect_annot_of_comp c))
                      (res_typing:universe_of g (comp_res c) (comp_u c))
                      (x:var { fresh_wrt x g (freevars (comp_post c)) })
                      (post_typing:tot_typing (push_binding g x ppname_default (comp_res c)) (open_term (comp_post c) x) tm_slprop)
  : T.Tac (comp_typing g c (universe_of_comp c))
  = let intro_st_comp_typing (st:st_comp { comp_u c == st.u /\
                                           comp_pre c == st.pre /\
                                           comp_res c == st.res /\
                                           comp_post c == st.post } )
      : T.Tac (st_comp_typing g st)
      = STC g st x res_typing pre_typing post_typing
    in
    match c with
    | C_ST st -> 
      let stc = intro_st_comp_typing st in
      CT_ST _ _ stc
    | C_STAtomic i obs st -> 
      let stc = intro_st_comp_typing st in
      CT_STAtomic _ i obs _ i_typing stc
    | C_STGhost i st -> 
      let stc = intro_st_comp_typing st in
      CT_STGhost _ i _ i_typing stc

irreducible
let post_typing_as_abstraction
  (#g:env) (#x:var) (#ty:term) (#t:term { fresh_wrt x g (freevars t) })
  (_:tot_typing (push_binding g x ppname_default ty) (open_term t x) tm_slprop)
  : FStar.Ghost.erased (RT.tot_typing (elab_env g) (mk_abs ty t) (mk_arrow ty tm_slprop))                                 
  = admit()

(* This should be in reflection typing *)
let fstar_equiv_preserves_typing
    (g:R.env) (t1 : R.term) (typ : R.term) (t2 : R.term)
    (eq : squash (T.equiv_token g t1 t2))
    (t1_typing : RT.tot_typing g t1 typ)
  : RT.tot_typing g t2 typ
  = admit()

let equiv_preserves_typing
    (g:env) (t1 : term) (typ : term) (t2 : term)
    (eq : squash (T.equiv_token (elab_env g) t1 t2))
    (t1_typing : typing g t1 T.E_Total typ)
  : typing g t2 T.E_Total typ
  = match t1_typing with
    | E pf -> E (fstar_equiv_preserves_typing _ t1 typ t2 eq pf)

let check_effect_annot (g:env) (e:effect_annot)
  : T.Tac (e':effect_annot { effect_annot_labels_match e e' } & effect_annot_typing g e') =
  let check_opens opens : T.Tac (e:term & typing g e T.E_Total tm_inames) =
    let (| opens, d |) = CP.check_term g opens T.E_Total tm_inames in
    let opens' =
      T.norm_well_typed_term
        (elab_env g)
        [primops; iota; zeta; delta_attr ["Pulse.Lib.Core.unfold_check_opens"]]
        opens
    in
    (| opens', equiv_preserves_typing _ _ _ _ () d |)
  in
  match e with
  | EffectAnnotSTT -> (| e, () |)
  | EffectAnnotGhost { opens } ->
    let (| opens, d |) = check_opens opens in
    (| EffectAnnotGhost { opens }, d |)
  | EffectAnnotAtomic { opens } ->
    let (| opens, d |) = check_opens opens in
    (| EffectAnnotAtomic { opens }, d |)
  | EffectAnnotAtomicOrGhost { opens } ->
    let (| opens, d |) = check_opens opens in
    (| EffectAnnotAtomicOrGhost { opens }, d |)

let intro_post_hint g effect_annot ret_ty_opt post =
  let x = fresh g in
  let ret_ty = 
      match ret_ty_opt with
      | None -> wr RT.unit_ty FStar.Range.range_0
      | Some t -> t
  in
  let ret_ty, _ = CP.instantiate_term_implicits g ret_ty None false in
  let (| u, ty_typing |) = CP.check_universe g ret_ty in
  let (| post, post_typing |) = CP.check_slprop (push_binding g x ppname_default ret_ty) (open_term_nv post (v_as_nv x)) in 
  let post' = close_term post x in
  Pulse.Typing.FV.freevars_close_term post x 0;
  let (| effect_annot, effect_annot_typing |) = check_effect_annot g effect_annot in
  assume (open_term post' x == post);
  { g;
    effect_annot;
    effect_annot_typing;
    ret_ty; u; ty_typing;
    post=post';
    x; post_typing_src=post_typing;
    post_typing=post_typing_as_abstraction #_ #_ #_ #post' post_typing }

let comp_typing_as_effect_annot_typing (#g:env) (#c:comp_st) (ct:comp_typing_u g c)
: effect_annot_typing g (effect_annot_of_comp c)
= let iname_typing = snd <| Metatheory.comp_typing_inversion ct in
  match c with
  | C_ST _ -> ()
  | C_STGhost _ _
  | C_STAtomic _ _ _ -> iname_typing
  

let post_hint_from_comp_typing #g #c ct = 
  let st_comp_typing = fst <| Metatheory.comp_typing_inversion ct in
  let effect_annot_typing = comp_typing_as_effect_annot_typing ct in
  let inv = Metatheory.st_comp_typing_inversion st_comp_typing in
  let p : post_hint_t = 
    { g;
      effect_annot=_;
      effect_annot_typing;
      ret_ty = comp_res c; u=comp_u c; 
      ty_typing=Mkdtuple4?._1 inv;
      post=comp_post c;
      x=Mkdtuple4?._3 inv;
      post_typing_src=Mkdtuple4?._4 inv;
      post_typing=post_typing_as_abstraction (Mkdtuple4?._4 inv) }
  in
  p

let comp_typing_from_post_hint
    (#g: env)
    (c: comp_st)
    (pre_typing: tot_typing g (comp_pre c) tm_slprop)
    (p:post_hint_for_env g { comp_post_matches_hint c (PostHint p) })
: T.Tac (comp_typing_u g c)
= let x = fresh g in
  if x `Set.mem` freevars p.post //exclude this
  then fail g None "Impossible: unexpected freevar in post, please file a bug-report"
  else let post_typing = post_hint_typing g p x in
       intro_comp_typing g c pre_typing
        post_typing.effect_annot_typing
        post_typing.ty_typing 
        x post_typing.post_typing


let extend_post_hint g p x tx conjunct conjunct_typing =
  let g' = push_binding g x ppname_default tx in
  let y = fresh g' in
  let g'' = push_binding g' y ppname_default p.ret_ty in
  let p_post_typing_src
    : tot_typing (push_binding p.g p.x ppname_default p.ret_ty)
                 (open_term p.post p.x) tm_slprop
    = p.post_typing_src
  in
  let p_post_typing_src''
    : tot_typing g'' (open_term p.post y) tm_slprop
    = RU.magic () //weaken, rename
  in
  let conjunct_typing'
    : tot_typing g' conjunct tm_slprop
    = conjunct_typing
  in
  let conjunct_typing''
    : tot_typing g'' (open_term conjunct y) tm_slprop
    = RU.magic () //weaken
  in
  let new_post = tm_star p.post conjunct in
  let new_post_typing
    : tot_typing g'' (open_term new_post y) tm_slprop
    = Pulse.Typing.star_typing p_post_typing_src'' conjunct_typing''
  in
  assume (fresh_wrt y g'' (freevars new_post));
  let new_post_abs_typing
    : Ghost.erased (RT.tot_typing (elab_env g'') (mk_abs p.ret_ty new_post) (mk_arrow p.ret_ty tm_slprop))
    = post_typing_as_abstraction new_post_typing
  in
  { p with
    g=g';
    post=new_post;
    x=y;
    post_typing_src=new_post_typing;
    post_typing=new_post_abs_typing }

let k_elab_unit (g:env) (ctxt:term)
  : continuation_elaborator g ctxt g ctxt
  = fun p r -> r

let k_elab_trans
  (#g0:env) (#g1:env { g1 `env_extends` g0 }) (#g2:env { g2 `env_extends` g1 }) (#ctxt0 #ctxt1 #ctxt2:term)
  (k0:continuation_elaborator g0 ctxt0 g1 ctxt1)
  (k1:continuation_elaborator g1 ctxt1 g2 ctxt2 { g1 `env_extends` g0})
   : continuation_elaborator g0 ctxt0 g2 ctxt2
   = fun post_hint res -> k0 post_hint (k1 post_hint res)

let comp_st_with_post (c:comp_st) (post:term)
  : c':comp_st { st_comp_of_comp c' == ({ st_comp_of_comp c with post} <: st_comp) } =
  match c with
  | C_ST st -> C_ST { st with post }
  | C_STGhost i st -> C_STGhost i { st with post }
  | C_STAtomic i obs st -> C_STAtomic i obs {st with post}

let ve_unit_r g (p:term) : slprop_equiv g (tm_star p tm_emp) p = 
  VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Unit _ _)

let st_equiv_post (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                  (post:term { freevars post `Set.subset` freevars (comp_post c)})
                  (veq: (x:var { fresh_wrt x g (freevars (comp_post c)) } ->
                         slprop_equiv (push_binding g x ppname_default (comp_res c)) 
                                     (open_term (comp_post c) x)
                                     (open_term post x)))
  : Dv (st_typing g t (comp_st_with_post c post))
  = if eq_tm post (comp_post c) then d
    else
      let c' = comp_st_with_post c post in
      let (| u_of, pre_typing, x, post_typing |) = Metatheory.(st_comp_typing_inversion (fst (comp_typing_inversion (st_typing_correctness d)))) in
      let veq = veq x in
      let st_equiv : st_equiv g c c' =
          ST_SLPropEquiv g c c' x pre_typing u_of post_typing (RT.Rel_refl _ _ _) (VE_Refl _ _) veq
      in
      t_equiv d st_equiv

let simplify_post (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                  (post:term { comp_post c == tm_star post tm_emp})
  : Dv (st_typing g t (comp_st_with_post c post))
  = st_equiv_post d post (fun x -> ve_unit_r (push_binding g x ppname_default (comp_res c)) (open_term post x))

let simplify_lemma (c:comp_st) (c':comp_st) (post_hint:post_hint_opt_t)
  : Lemma
    (requires
        comp_post_matches_hint c post_hint /\
        effect_annot_of_comp c == effect_annot_of_comp c' /\
        comp_res c' == comp_res c /\
        comp_u c' == comp_u c /\
        comp_post c' == tm_star (comp_post c) tm_emp)
    (ensures comp_post_matches_hint (comp_st_with_post c' (comp_post c)) post_hint /\
             comp_pre (comp_st_with_post c' (comp_post c)) == comp_pre c')
  = ()

let slprop_equiv_typing_bk (#g:env) (#ctxt:_) (ctxt_typing:tot_typing g ctxt tm_slprop)
                           (#p:_) (d:slprop_equiv g p ctxt)
  : tot_typing g p tm_slprop 
  = let _, bk = slprop_equiv_typing d in
    bk ctxt_typing

let comp_with_pre (c:comp_st) (pre:term) =
  match c with
  | C_ST st -> C_ST { st with pre }
  | C_STGhost i st -> C_STGhost i { st with pre }
  | C_STAtomic i obs st -> C_STAtomic i obs {st with pre}


let st_equiv_pre (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                 (pre:term)
                 (veq: slprop_equiv g (comp_pre c) pre)
  : Dv (st_typing g t (comp_with_pre c pre))
  = if eq_tm pre (comp_pre c) then d
    else
      let c' = comp_with_pre c pre in
      let (| u_of, pre_typing, x, post_typing |) =
        Metatheory.(st_comp_typing_inversion (fst (comp_typing_inversion (st_typing_correctness d)))) in
      let st_equiv : st_equiv g c c' =
          ST_SLPropEquiv g c c' x pre_typing u_of post_typing (RT.Rel_refl _ _ _) veq (VE_Refl _ _)
      in
      t_equiv d st_equiv


#push-options "--z3rlimit_factor 4 --ifuel 2 --fuel 0"
let k_elab_equiv_continuation (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt #ctxt1 #ctxt2:term)
  (k:continuation_elaborator g1 ctxt g2 ctxt1)
  (d:slprop_equiv g2 ctxt1 ctxt2)
  : continuation_elaborator g1 ctxt g2 ctxt2 =
  fun post_hint res ->
    let (| st, c, st_d |) = res in
    let st_d : st_typing g2 st c = st_d in
    assert (comp_pre c == ctxt2);
    let st_d' : st_typing g2 st (comp_with_pre c ctxt1) = st_equiv_pre st_d _ (VE_Sym _ _ _ d) in
    k post_hint (| st, _, st_d' |)
#pop-options

let slprop_equiv_typing_fwd (#g:env) (#ctxt:_) (ctxt_typing:tot_typing g ctxt tm_slprop)
                           (#p:_) (d:slprop_equiv g ctxt p)
  : tot_typing g p tm_slprop 
  = let fwd, _ = slprop_equiv_typing d in
    fwd ctxt_typing

#push-options "--z3rlimit_factor 4 --ifuel 1 --fuel 0"
let k_elab_equiv_prefix
  (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt1 #ctxt2 #ctxt:term)
  (k:continuation_elaborator g1 ctxt1 g2 ctxt)
  (d:slprop_equiv g1 ctxt1 ctxt2)
  : continuation_elaborator g1 ctxt2 g2 ctxt =
  fun post_hint res ->
  let framing_token : frame_for_req_in_ctxt g1 ctxt2 ctxt1 = 
  let d = VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Trans _ _ _ _ (VE_Unit _ _) d) in
    (| tm_emp, emp_typing, d |)
  in
  let res = k post_hint res in
  let (| st, c, st_d |) = res in
  assert (comp_pre c == ctxt1);
  (| _, _, st_equiv_pre st_d _ d |)
 #pop-options

let k_elab_equiv
  (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt1 #ctxt1' #ctxt2 #ctxt2':term)                 
  (k:continuation_elaborator g1 ctxt1 g2 ctxt2)
  (d1:slprop_equiv g1 ctxt1 ctxt1')
  (d2:slprop_equiv g2 ctxt2 ctxt2')
  : continuation_elaborator g1 ctxt1' g2 ctxt2' =
  
  let k : continuation_elaborator g1 ctxt1 g2 ctxt2' =
    k_elab_equiv_continuation k d2 in
  let k : continuation_elaborator g1 ctxt1' g2 ctxt2' =
    k_elab_equiv_prefix k d1 in
  k

#push-options "--fuel 3 --ifuel 2 --split_queries no --z3rlimit_factor 20"
open Pulse.PP
let continuation_elaborator_with_bind (#g:env) (ctxt:term)
  (#c1:comp{stateful_comp c1})
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (ctxt_pre1_typing:tot_typing g (tm_star ctxt (comp_pre c1)) tm_slprop)
  (x:nvar { None? (lookup g (snd x)) })
  : T.Tac (continuation_elaborator
             g
             (tm_star ctxt (comp_pre c1))
             (push_binding g (snd x) (fst x) (comp_res c1))
             (tm_star (open_term (comp_post c1) (snd x)) ctxt)) =

  let pre1 = comp_pre c1 in
  let res1 = comp_res c1 in
  let post1 = comp_post c1 in
  let ctxt_typing = star_typing_inversion_l ctxt_pre1_typing in
  // let p_prop = Metatheory.pure_typing_inversion pure_typing in
  let v_eq = VE_Comm g ctxt pre1 in
  let framing_token : frame_for_req_in_ctxt g (tm_star ctxt pre1) pre1 = 
    (| ctxt, ctxt_typing, VE_Comm g pre1 ctxt  |)
  in
  Pulse.Checker.Prover.Util.debug_prover g (fun _ ->
    Printf.sprintf "Applying frame %s to computation %s\n"
      (show ctxt)
      (show c1));
  let (| c1, e1_typing |) =
    apply_frame ctxt_pre1_typing e1_typing framing_token in
  let (| u_of_1, pre_typing, _, _ |) = 
    Metatheory.(st_comp_typing_inversion (fst <| comp_typing_inversion (st_typing_correctness e1_typing))) in
  let b = res1 in
  let ppname, x = x in
  let g' = push_binding g x ppname b in
  
  let post1_opened = open_term_nv post1 (v_as_nv x) in
  let k : continuation_elaborator g (tm_star ctxt pre1) g' (tm_star post1_opened ctxt) =
    fun post_hint res ->
    let (| e2, c2, e2_typing |) = res in
    assert (comp_post_matches_hint c2 post_hint);
    let e2_typing : st_typing g' e2 c2 = e2_typing in
    let e2_closed = close_st_term e2 x in
    assume (open_st_term e2_closed x == e2);
    assert (comp_pre c1 == (tm_star ctxt pre1));
    assert (comp_post c1 == tm_star post1 ctxt);
    assert (comp_pre c2 == tm_star post1_opened ctxt);
    assert (open_term (comp_post c1) x == tm_star post1_opened (open_term ctxt x));
    // ctxt is well-typed, hence ln
    assume (open_term ctxt x == ctxt);
    assert (open_term (comp_post c1) x == comp_pre c2);
    // we closed e2 with x
    assume (~ (x `Set.mem` freevars_st e2_closed));
    if x `Set.mem` freevars (comp_post c2)
    then fail g' None "Impossible: freevar clash when constructing continuation elaborator for bind, please file a bug-report"
    else (
      let t_typing, post_typing =
        Pulse.Typing.Combinators.bind_res_and_post_typing g c2 x post_hint in
      let g = push_context g "mk_bind" e1.range in
      // info_doc g None
      //   [prefix 4 1 (doc_of_string "mk_bind e1 = ") (doc_of_string (Pulse.Syntax.Printer.st_term_to_string e1));
      //    prefix 4 1 (doc_of_string "mk_bind c1 = ") (pp #comp c1);
      //    prefix 4 1 (doc_of_string "mk_bind e2 = ") (doc_of_string (Pulse.Syntax.Printer.st_term_to_string e2));
      //    prefix 4 1 (doc_of_string "mk_bind c2 = ") (pp #comp c2)]
      // ;
      let (| e, c, e_typing |) =
        Pulse.Typing.Combinators.mk_bind
          g (tm_star ctxt pre1) 
          e1 e2_closed c1 c2 (ppname, x) e1_typing
          u_of_1 
          e2_typing
          t_typing
          post_typing
          post_hint
      in
      (| e, c, e_typing |)
    )
  in
  k
#pop-options

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y == x} = x

#push-options "--z3rlimit_factor 8 --fuel 1 --ifuel 1"

let st_comp_typing_with_post_hint 
      (#g:env) (#ctxt:_)
      (ctxt_typing:tot_typing g ctxt tm_slprop)
      (post_hint:post_hint_opt g { PostHint? post_hint })
      (c:comp_st { comp_pre c == ctxt /\ comp_post_matches_hint c post_hint })
: st_comp_typing g (st_comp_of_comp c)
= let st = st_comp_of_comp c in
  let PostHint ph = post_hint in
  let post_typing_src
    : tot_typing (push_binding ph.g ph.x ppname_default ph.ret_ty)
                 (open_term ph.post ph.x) tm_slprop
    = ph.post_typing_src
  in
  let x = RU.magic () in //fresh g in
  assume (fresh_wrt x g (freevars ph.post));
  assume (None? (lookup g ph.x));
  let post_typing_src
    : tot_typing (push_binding ph.g x ppname_default ph.ret_ty)
                 (open_term ph.post x) tm_slprop
    = if x = Ghost.reveal ph.x
      then post_typing_src
      else 
        let open Pulse.Typing.Metatheory.Base in
        let tt :
         tot_typing
            (push_binding ph.g x ppname_default ph.ret_ty)
            (subst_term (open_term ph.post ph.x) (renaming ph.x x))
            (subst_term tm_slprop (renaming ph.x x)) =
          tot_typing_renaming1 ph.g ph.x ph.ret_ty (open_term ph.post ph.x) tm_slprop post_typing_src x
        in
        assert (subst_term tm_slprop (renaming ph.x x) == tm_slprop);
        assume (subst_term (open_term ph.post ph.x) (renaming ph.x x) ==
                open_term ph.post x);
        coerce_eq tt ()
  in
  let post_typing_src
    : tot_typing (push_binding g x ppname_default ph.ret_ty)
                 (open_term ph.post x) tm_slprop
    = //weakening: TODO
      RU.magic ()
  in
  let ty_typing : universe_of ph.g st.res st.u = ph.ty_typing in
  let ty_typing : universe_of g st.res st.u =
    Pulse.Typing.Metatheory.tot_typing_weakening_standard ph.g ty_typing g
  in
  assert (st.res == ph.ret_ty);
  assert (st.post == ph.post);
  STC g st x ty_typing ctxt_typing post_typing_src
#pop-options

let continuation_elaborator_with_bind_fn (#g:env) (#ctxt:term)
  (ctxt_typing:tot_typing g ctxt tm_slprop)
  (#e1:st_term)
  (#c1:comp { C_Tot? c1 })
  (b:binder{b.binder_ty == comp_res c1})
  (e1_typing:st_typing g e1 c1)
  (x:nvar { None? (lookup g (snd x)) })
: T.Tac (continuation_elaborator
          g ctxt
          (push_binding g (snd x) ppname_default (comp_res c1)) ctxt)
= let t1 = comp_res c1 in
  assert ((push_binding g (snd x) (fst x) t1) `env_extends` g);
  fun post_hint (| e2, c2, d2 |) ->
    if not (PostHint? post_hint) then T.fail "bind_fn: expects the post_hint to be set";
    let ppname, x = x in
    let e2_closed = close_st_term e2 x in
    assume (open_st_term (close_st_term e2 x) x == e2);
    let e = wrst c2 (Tm_Bind {binder=b; head=e1; body=e2_closed}) in
    let (| u, c1_typing |) = Pulse.Typing.Metatheory.Base.st_typing_correctness_ctot e1_typing in
    let c2_typing : comp_typing g c2 (universe_of_comp c2) =
      match c2 with
      | C_ST st -> 
        let stc = st_comp_typing_with_post_hint ctxt_typing post_hint c2 in
        CT_ST _ _ stc
      
      | C_STAtomic i obs st -> 
        let stc = st_comp_typing_with_post_hint ctxt_typing post_hint c2 in
        let i_typing = CP.core_check_term g i T.E_Total tm_inames in
        CT_STAtomic _ _ obs _ i_typing stc

      | C_STGhost i st ->
        let i_typing = CP.core_check_term g i T.E_Total tm_inames in
        let stc = st_comp_typing_with_post_hint ctxt_typing post_hint c2 in
        CT_STGhost _ i _ i_typing stc
    in
    let d : st_typing g e c2 =
        T_BindFn g e1 e2_closed c1 c2 b x e1_typing u c1_typing d2 c2_typing
    in
    (| e, c2, d |)

let rec check_equiv_emp (g:env) (vp:term)
  : option (slprop_equiv g vp tm_emp)
  = match inspect_term vp with
    | Tm_Emp -> Some (VE_Refl _ _)
    | Tm_Star vp1 vp2 ->
      (match check_equiv_emp g vp1, check_equiv_emp g vp2 with
       | Some d1, Some d2 ->
         let d3 : slprop_equiv g (tm_star vp1 vp2) (tm_star tm_emp tm_emp)
           = VE_Ctxt _ _ _ _ _ d1 d2 in
         let d4 : slprop_equiv g (tm_star tm_emp tm_emp) tm_emp =
           VE_Unit _ _ in
         Some (VE_Trans _ _ _ _ d3 d4)
       | _, _ -> None)
     | _ -> None

let emp_inames_included (g:env) (i:term) (_:tot_typing g i tm_inames)
: prop_validity g (tm_inames_subset tm_emp_inames i)
= RU.magic()

let return_in_ctxt (g:env) (y:var) (y_ppname:ppname) (u:universe) (ty:term) (ctxt:slprop)
  (ty_typing:universe_of g ty u)
  (post_hint0:post_hint_opt g { PostHint? post_hint0 /\ checker_res_matches_post_hint g post_hint0 y ty ctxt})
: Div  (st_typing_in_ctxt g ctxt post_hint0)
       (requires lookup g y == Some ty)
       (ensures fun _ -> True)
= let PostHint post_hint = post_hint0 in
  let x = fresh g in
  assume (~ (x `Set.mem` freevars post_hint.post));
  let ctag =
    match post_hint.effect_annot with
    | EffectAnnotAtomic _ -> STT_Atomic
    | EffectAnnotGhost _ -> STT_Ghost
    | EffectAnnotAtomicOrGhost _ -> STT_Atomic
    | EffectAnnotSTT -> STT
  in
  let y_tm = tm_var {nm_index=y;nm_ppname=y_ppname} in
  let d = T_Return g ctag false u ty y_tm post_hint.post x ty_typing
    (RU.magic ())  // that null_var y is well typed at ty in g, we know since lookup g y == Some ty
    (RU.magic ())  // typing of (open post x) in (g, x) ... post_hint is well-typed, so should get
  in
  let t = wtag (Some ctag) (Tm_Return {expected_type=tm_unknown;insert_eq=false;term=y_tm}) in
  let c = comp_return ctag false u ty y_tm post_hint.post x in
  let d : st_typing g t c = d in
  assume (comp_u c == post_hint.u); // this u should follow from equality of t
  match c, post_hint.effect_annot with
  | C_STAtomic _ obs _, EffectAnnotAtomic { opens }
  | C_STAtomic _ obs _, EffectAnnotAtomicOrGhost { opens } ->
    assert (comp_inames c == tm_emp_inames);
    let pht = post_hint_typing g post_hint x in
    let validity = emp_inames_included g opens pht.effect_annot_typing in
    let d = T_Sub _ _ _ _ d (STS_AtomicInvs _ (st_comp_of_comp c) tm_emp_inames opens obs obs validity) in
    (| _, _, d |)
  | C_STGhost _ _, EffectAnnotGhost { opens }
  | C_STGhost _ _, EffectAnnotAtomicOrGhost { opens } ->
    assert (comp_inames c == tm_emp_inames);
    let pht = post_hint_typing g post_hint x in
    let validity = emp_inames_included g opens pht.effect_annot_typing in
    let d = T_Sub _ _ _ _ d (STS_GhostInvs _ (st_comp_of_comp c) tm_emp_inames opens validity) in
    (| _, _, d |)
  | _ -> 
    (| _, _, d |)

let match_comp_res_with_post_hint (#g:env) (#t:st_term) (#c:comp_st)
  (d:st_typing g t c)
  (post_hint:post_hint_opt g)
  : T.Tac (t':st_term &
           c':comp_st &
           st_typing g t' c') =

  match post_hint with
  | NoHint -> (| t, c, d |)
  | TypeHint ret_ty
  | PostHint { ret_ty } ->
    let cres = comp_res c in
    if eq_tm cres ret_ty
    then (| t, c, d |)
    else match Pulse.Typing.Util.check_equiv_now (elab_env g) cres ret_ty with
         | None, issues ->
           let open Pulse.PP in
           fail_doc_with_subissues g (Some t.range) issues [
            prefix 2 1 (text "Could not prove equality between computed type") (pp cres) ^/^
            prefix 2 1 (text "and expected type") (pp ret_ty);
           ]
         | Some tok, _ ->
           let d_equiv
             : RT.equiv _ cres ret_ty =
             RT.Rel_eq_token _ _ _ (FStar.Squash.return_squash tok) in
           
           let c' = with_st_comp c {(st_comp_of_comp c) with res = ret_ty } in
           let (| cres_typing, cpre_typing, x, cpost_typing |) =
             st_comp_typing_inversion (fst <| comp_typing_inversion (st_typing_correctness d)) in
           let d_stequiv : st_equiv g c c' =
             ST_SLPropEquiv _ c c' _ cpre_typing cres_typing cpost_typing d_equiv (VE_Refl _ _) (VE_Refl _ _)
           in

           (| t, c', Pulse.Typing.Combinators.t_equiv d d_stequiv |)

let apply_checker_result_k (#g:env) (#ctxt:slprop) (#post_hint:post_hint_for_env g)
  (r:checker_result_t g ctxt (PostHint post_hint))
  (res_ppname:ppname)
  : T.Tac (st_typing_in_ctxt g ctxt (PostHint post_hint)) =

  // TODO: FIXME add to checker result type?
  let (| y, g1, (| u_ty, ty_y, d_ty_y |), (| pre', _ |), k |) = r in

  let (| u_ty_y, d_ty_y |) = Pulse.Checker.Pure.check_universe g1 ty_y in

  let d : st_typing_in_ctxt g1 pre' (PostHint post_hint) =
    return_in_ctxt g1 y res_ppname u_ty_y ty_y pre' d_ty_y (PostHint post_hint) in

  k (PostHint post_hint) d

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"
//TODO: refactor and merge with continuation_elaborator_with_bind
let checker_result_for_st_typing (#g:env) (#ctxt:slprop) (#post_hint:post_hint_opt g)
  (d:st_typing_in_ctxt g ctxt post_hint)
  (ppname:ppname)
: T.Tac (checker_result_t g ctxt post_hint)
= let (| e1, c1, d1 |) = d in
  let x = fresh g in
  assume (~ (x `Set.mem` freevars (comp_post c1)));
  let u_of_1, pre_typing, post_typing = 
    Metatheory.(st_comp_typing_inversion_with_name (fst <| comp_typing_inversion (st_typing_correctness d1)) x) in
  let g' = push_binding g x ppname (comp_res c1) in
  let ctxt' = open_term_nv (comp_post c1) (ppname, x) in
  let k
    : continuation_elaborator g (comp_pre c1) g' ctxt'
    = fun post_hint st_k ->
        let (| e2, c2, d2 |) = st_k in
        let e2_closed = close_st_term e2 x in
        assume (open_st_term e2_closed x == e2);
        if x `Set.mem` freevars (comp_post c2)
        then fail g None "Impossible: freevar clash when constructing continuation elaborator for bind, please file a bug-report"
        else (
          let t_typing, post_typing =
            Pulse.Typing.Combinators.bind_res_and_post_typing g c2 x post_hint in
          let (| ee, cc, ee_typing |) =
            Pulse.Typing.Combinators.mk_bind
              g (comp_pre c1)
              e1 e2_closed c1 c2 (ppname, x)
              d1 u_of_1
              d2 t_typing
              post_typing 
              post_hint
          in
          (| ee, cc, ee_typing |)
        )
  in
  let _ : squash (checker_res_matches_post_hint g post_hint x (comp_res c1) ctxt') =
    match post_hint with
    | PostHint post_hint -> ()
    | _ -> () in
    
  assert (g' `env_extends` g);
  let u_of_1_g' : universe_of _ _ _ = Pulse.Typing.Metatheory.tot_typing_weakening_standard g u_of_1 g' in
  assert (~ (x `Set.mem` freevars (comp_post c1)));
  (| x, g', (| _, _, u_of_1_g' |), (| ctxt', post_typing |), k |)
#pop-options

let readback_comp_res_as_comp (c:T.comp) : option comp =
  match c with
  | T.C_Total t -> (
    match readback_comp t with
    | None -> None
    | Some c -> Some c
  )
  | _ -> None

let rec is_stateful_arrow (g:env) (c:option comp) (args:list T.argv) (out:list T.argv)
  : T.Tac (option (list T.argv & T.argv))
  = let open R in
    match c with
    | None -> None
    | Some (C_ST _)
    | Some (C_STGhost _ _)
    | Some (C_STAtomic _ _ _) -> (
      match args, out with
      | [], hd::tl -> Some (List.rev tl, hd)
      | _ -> None //leftover or not enough args
    )

    | Some (C_Tot c_res) -> (
      let ht = T.inspect c_res in
      match ht with
      | T.Tv_Arrow b c -> (
        match args with
        | [] -> ( //no more args; check that only implicits remain, ending in an stateful comp  
          let bs, c = T.collect_arr_ln_bs c_res in
          if List.Tot.for_all (fun b -> R.Q_Implicit? (R.inspect_binder b).qual) bs
          then is_stateful_arrow g (readback_comp_res_as_comp (R.inspect_comp c)) [] out
          else None //too few args    
        )

        | (arg, qual)::args' -> ( //check that this arg qual matches the binder and recurse accordingly
          let bqual =
            (* Ignore equality qualifiers in the binder *)
            match b.qual with
            | Q_Equality -> Q_Explicit
            | q -> q
          in
          match bqual, qual with
          | T.Q_Meta _, T.Q_Implicit
          | T.Q_Implicit, T.Q_Implicit 
          | T.Q_Explicit, T.Q_Explicit ->  //consume this argument
            is_stateful_arrow g (readback_comp_res_as_comp c) args' ((arg, qual)::out)

          | T.Q_Meta _, T.Q_Explicit
          | T.Q_Implicit, T.Q_Explicit -> 
            //don't consume this argument
            is_stateful_arrow g (readback_comp_res_as_comp c) args out

          | _ -> None //incompatible qualifiers; bail
        )
      )
      | _ ->
        let c_res' = RU.whnf_lax (elab_env g) c_res in
        let ht = T.inspect c_res' in
        if T.Tv_Arrow? ht
        then (
          let c_res' = wr c_res' (T.range_of_term c_res') in
          is_stateful_arrow g (Some (C_Tot c_res')) args out
        )
        else None
    )

let checker_result_t_equiv_ctxt (g:env) (ctxt ctxt' : slprop)
  (post_hint:post_hint_opt g)
  (equiv : slprop_equiv g ctxt ctxt')
  (r : checker_result_t g ctxt post_hint)
: checker_result_t g ctxt' post_hint
= let (| x, g1, t, ctxt', k |) = r in
  (| x, g1, t, ctxt', k_elab_equiv k equiv (VE_Refl _ _) |)

module RU = Pulse.RuntimeUtils  
let as_stateful_application (head:term) (args:list T.argv { Cons? args }) r =
  let applied_args, (last_arg, qual) = List.unsnoc args in
  let head = RU.mk_app_flat head applied_args (T.range_of_term head) in
  let qual = 
    match qual with
    | T.Q_Implicit -> Some Implicit
    | _ -> None
  in
  let st_app = Tm_STApp { head; arg=last_arg; arg_qual=qual} in
  mk_term st_app r


let is_stateful_application (g:env) (e:term) 
  : T.Tac (o:option st_term { Some? o ==> Tm_STApp? (Some?.v o).term }) =
  let head, args = T.collect_app_ln e in
  if Nil? args then None else
  match RU.lax_check_term_with_unknown_universes (elab_env g) head with
  | None -> None
  | Some ht -> 
    let head_t = wr ht (T.range_of_term ht) in
    match is_stateful_arrow g (Some (C_Tot head_t)) args [] with 
    | None -> None
    | Some _ -> Some (as_stateful_application head args (RU.range_of_term e))

let apply_conversion
      (#g:env) (#e:term) (#eff:_) (#t0:term)
      (d:typing g e eff t0)
      (#t1:term)
      (eq:Ghost.erased (RT.related (elab_env g) t0 RT.R_Eq t1))
  : typing g e eff t1
  = let d : RT.typing (elab_env g) e (eff, t0) = d._0 in
    let r : RT.related (elab_env g) t0 RT.R_Eq t1 = eq in
    let r  = RT.Rel_equiv _ _ _ RT.R_Sub r in
    let s : RT.sub_comp (elab_env g) (eff, t0) (eff, t1) = 
        RT.Relc_typ _ _ _ _ _ r
    in
    E (RT.T_Sub _ _ _ _ d s)

let norm_typing
      (g:env) (e:term) (eff:_) (t0:term)
      (d:typing g e eff t0)
      (steps:list norm_step)
  : T.Tac (t':term & typing g e eff t')
  = let u_t_typing : Ghost.erased (u:R.universe & RT.typing _ _ _) = 
      Pulse.Typing.Metatheory.Base.typing_correctness d._0
    in
    let (| t', t'_typing, related_t_t' |) =
      Pulse.RuntimeUtils.norm_well_typed_term (dsnd u_t_typing) steps
    in
    let d : typing g e eff t' = apply_conversion d related_t_t' in
    (| t', d |)

module TermEq = FStar.Reflection.TermEq
let norm_typing_inverse
      (g:env) (e:term) (eff:_) (t0:term)
      (d:typing g e eff t0)
      (t1:term)
      (#u:_)
      (d1:tot_typing g t1 (tm_type u))
      (steps:list norm_step)
  : T.Tac (option (typing g e eff t1))
  = let (| t1', t1'_typing, related_t1_t1' |) =
      let d1 = Ghost.hide d1._0 in
      Pulse.RuntimeUtils.norm_well_typed_term d1 steps
    in
    if TermEq.term_eq t0 t1'
    then (
      let related_t1'_t1 = Ghost.hide (RT.Rel_sym _ _ _ related_t1_t1') in
      Some (apply_conversion d related_t1'_t1)
    )
    else None


let norm_st_typing_inverse
      (#g:env) (#e:st_term) (#t0:term)
      (d:st_typing g e (C_Tot t0))
      (#u:_)
      (t1:term)
      (d1:tot_typing g t1 (tm_type u))
      (steps:list norm_step)
  : T.Tac (option (st_typing g e (C_Tot t1)))
  = let d1 
      : Ghost.erased (RT.tot_typing (elab_env g) t1 (RT.tm_type u))
      = Ghost.hide (coerce_eq d1._0 ())
    in
    let (| t1', t1'_typing, related_t1_t1' |) =
      Pulse.RuntimeUtils.norm_well_typed_term d1 steps
    in
    if TermEq.term_eq t0 t1'
    then (
      let t0_typing 
        : Ghost.erased (RT.tot_typing (elab_env g) t0 (RT.tm_type u)) =
        rt_equiv_typing #_ #_ #t0 related_t1_t1' d1
      in
      let eq
        : Ghost.erased (RT.equiv (elab_env g) t0 t1)
        = Ghost.hide (RT.Rel_sym _ _ _ related_t1_t1')
      in
      let steq : st_equiv g (C_Tot t0) (C_Tot t1) =
        ST_TotEquiv _ _ _ u (E (coerce_eq (Ghost.reveal t0_typing) ())) eq
      in
      Some (Pulse.Typing.Combinators.t_equiv d steq)
    )
    else None

open FStar.List.Tot    
module RT = FStar.Reflection.Typing
let decompose_app (g:env) (tt:either term st_term)
: T.Tac (option (term & list T.argv & (args:list T.argv{ Cons? args } -> T.Tac (res:either term st_term { Inr? tt ==> Inr? res }))))
= let decompose_st_app (t:st_term)
  : T.Tac (option (term & list T.argv & (args:list T.argv{ Cons? args } -> T.Tac (res:either term st_term { Inr? tt ==> Inr? res }))))
  = match t.term with
    | Tm_STApp { head; arg=last_arg; arg_qual=last_arg_qual } ->
      let head, args = T.collect_app_ln head in
      let args = args @ [last_arg, Pulse.Elaborate.Pure.elab_qual last_arg_qual] in
      let rebuild (args:list T.argv{Cons? args}) : T.Tac (res:either term st_term { Inr? res }) = 
        let args, last_arg = List.unsnoc args in
        let head = RU.mk_app_flat head args t.range in
        Inr <| mk_term (Tm_STApp { head; arg=fst last_arg; arg_qual=last_arg_qual }) t.range
      in
      Some (head, args, rebuild)
    | _ -> None
  in
  match tt with
  | Inl tt -> (
    match is_stateful_application g tt with
    | Some st_app -> decompose_st_app st_app
    | None -> 
      let head, args = T.collect_app_ln tt in
      let rebuild (args:list T.argv{Cons? args}) : T.Tac (either term st_term) =
        let head = RU.mk_app_flat head args (T.range_of_term tt) in
        Inl head
      in
      Some (head, args, rebuild)
  )
  | Inr st -> decompose_st_app st

let anf_binder name = T.pack (T.Tv_FVar (T.pack_fv (Pulse.Reflection.Util.mk_pulse_lib_core_lid (Printf.sprintf "__%s_binder__" name))))
  
let bind_st_term (g:env) (s:st_term) 
: T.Tac (env & binder & var & term)
= let open Pulse.Syntax in
  let anf_name = Printf.sprintf "__anf%d" (RU.next_id()) in
  let b = {
    binder_ty = tm_unknown;
    binder_ppname = mk_ppname (FStar.Reflection.Typing.seal_pp_name anf_name) s.range;
    binder_attrs = FStar.Sealed.seal [anf_binder anf_name];
  } in
  let x = Pulse.Typing.Env.fresh g in
  let g = Pulse.Typing.Env.push_binding g x b.binder_ppname b.binder_ty in
  g, b, x, RT.var_as_term x

let rec maybe_hoist (g:env) (arg:T.argv)
: T.Tac (env & list (binder & var & st_term) & T.argv)
= let t, q = arg in
  let head, args = T.collect_app_ln t in
  match args with
  | [] -> g, [], arg //no args to hoist
  | _ ->
  match is_stateful_application g t with
  | None -> (
    let g, binders, args = maybe_hoist_args g args in
    match binders with
    | [] -> g, [], arg // no elab
    | _ -> 
      let t = RU.mk_app_flat head args (T.range_of_term t) in
      g, binders, (t, q)
  )
  | Some _ -> (
    let g, binders, args = maybe_hoist_args g args in
    if Nil? args then T.fail "Impossible";
    let st_app = as_stateful_application head args (T.range_of_term t) in
    let g, b, x, t = bind_st_term g st_app in
    let arg = t, q in
    g, binders@[b, x, st_app], arg
  )

and maybe_hoist_args (g:env) (args:list T.argv)
: T.Tac (env & list (binder & var & st_term) & list T.argv)
= T.fold_right
    (fun arg (g, binders, args) ->
      let g, binders', arg = maybe_hoist g arg in
      let binders = binders' @ binders in
      g, binders, arg::args)
    args
    (g, [], [])

let maybe_hoist_top 
  (hoist_top_level:bool)
  (g:env)
  (tt:either term st_term)
: T.Tac (env & list (binder & var & st_term) & res:either term st_term { 
    (if hoist_top_level then Inl? res else tt==res)
    })
= if not hoist_top_level then g, [], tt
  else (
    match tt with
    | Inl _ -> g, [], tt
    | Inr st -> 
      let g, b, x, t = bind_st_term g st in 
      g, [(b, x, st)], Inl t
  )

let hoist_stateful_apps
  (g:env)
  (tt:either term st_term)
  (hoist_top_level:bool)
  (context: (
    x:either term st_term { 
      (Inr? tt ==> Inr? x) /\
      (hoist_top_level /\ Inl? tt ==> Inl? x)
    } -> T.Tac st_term))
: T.Tac (option st_term)
= match decompose_app g tt with
  | None -> None
  | Some (head, args, rebuild) ->
    let _, binders, args = maybe_hoist_args g args in
    match args with
    | [] -> None
    | _ ->
      let tt' = rebuild args in
      let _, binders', tt' = maybe_hoist_top (hoist_top_level && Inl? tt) g tt' in 
      let binders = binders @ binders' in
      match binders with
      | [] -> (
        match tt, tt' with
        | Inl _, Inr _ -> (
          Some (context tt') //we at least elaborated a pure term to an inpure term
        )
        | _ -> None //No elaboration
      )
      | _ ->
        let bind_term = context tt' in
        let res = List.Tot.fold_right
          (fun (b, v, arg) body -> 
            let body = Pulse.Syntax.Naming.close_st_term body v in
            mk_term (Tm_Bind { binder = b; head = arg; body = body }) bind_term.range)
          binders
          bind_term
        in
        Some res

 
let compose_checker_result_t 
  (#g:env) (#g':env { g' `env_extends` g }) (#ctxt #ctxt':slprop) (#post_hint:post_hint_opt g)
  (r1:checker_result_t g ctxt NoHint)
  (r2:checker_result_t g' ctxt' post_hint { composable r1 r2 })
: T.Tac (checker_result_t g ctxt post_hint)
= let (| x1, g1, t1, (| _, ctxt'_typing |), k1 |) = r1 in
  let (| x2, g2, t2, ctxt2, k2 |) = r2 in
  let k = k_elab_trans k1 k2 in
  (| x2, g2, t2, ctxt2, k |)

let rec close_post x_ret dom_g g1 (bs1:list (ppname & var & typ)) (post:slprop)
: T.Tac slprop
= let maybe_close (n, y,ty) (post:slprop) = 
    if not (y `Set.mem` freevars post) then post
    else (
      let b = {binder_ty=ty; binder_ppname=n; binder_attrs=Sealed.seal []} in
      let (| u, _ |) = Pulse.Checker.Pure.check_universe g1 ty in
      tm_exists_sl u b (close_term post y)
    )
  in
  (* generate exists (_:squash pr). post 
     Useful if the well-formedness of post depends on pr in scope *)
  let guard_with_squash pr (post:slprop) : T.Tac slprop =
    let n, u, pr = pr in
    let b = {binder_ty=mk_squash u pr; binder_ppname=n; binder_attrs=Sealed.seal []} in
    tm_exists_sl u_zero b post
  in
  let maybe_elim_rewrites_to pr (post:term) : T.Tac term =
    let _, _, property = pr in
    let open R in
    let hd, args = T.collect_app_ln property in
    match T.inspect_ln hd, args with
    | Tv_UInst hd [u], [(typ, Q_Implicit); (lhs, Q_Explicit); (rhs, Q_Explicit)] ->
      if T.inspect_fv hd = rewrites_to_p_lid
      then (
        match T.inspect_ln lhs with
        | Tv_Var n1 ->
          let n1 = inspect_namedv n1 in
          Pulse.Syntax.Naming.subst_term post [RT.NT n1.uniq rhs]
        | _ -> 
          let eq = RT.eq2 u typ lhs rhs in
          tm_star post (tm_pure eq)
      )
      else tm_star post (tm_pure property) //guard_with_squash pr post?
    | _ -> tm_star post (tm_pure property) //guard_with_squash pr post?
  in
  let close_post = close_post x_ret dom_g g1 in
  match bs1 with
  | [] -> post
  | (n,y,ty)::tl -> (
    if y = x_ret
    then close_post tl post
    else if y `Set.mem` dom_g
    then close_term post x_ret
    else (
      let open R in
      match T.inspect_ln ty with
      | Tv_App hd (p, Q_Explicit) -> (
        match T.inspect_ln hd with
        | Tv_UInst fv [u]->
          if inspect_fv fv = ["Prims"; "squash"]
          then close_post tl (maybe_elim_rewrites_to (n, u, p) post)
          else close_post tl (maybe_close (n,y,ty) post)
        | _ -> close_post tl (maybe_close (n,y,ty) post)
      )
      | _ -> close_post tl (maybe_close (n,y,ty) post)
    )
  )

let infer_post #g #ctxt (r:checker_result_t g ctxt NoHint)
: T.Tac (p:post_hint_for_env g { p.g == g /\ p.effect_annot == EffectAnnotSTT })
= let (| x, g1, (| u, t, _ |), (| post, _ |), k |) = r in
  let bs0 = bindings g in
  let dom_g = dom g in
  let fvs_t = freevars t in
  let fail_fv_typ #a (x:string) 
  : T.Tac a =
    fail_doc g (Some (T.range_of_term t))
        [Pulse.PP.text "Could not infer a type for this block; the return type `";
          Pulse.PP.text (T.term_to_string t); 
          Pulse.PP.text "` contains free variable ";
          Pulse.PP.text x;
          Pulse.PP.text " that escape its environment"]
  in
  let mk_post_hint (post:term) : T.Tac (p:post_hint_for_env g {p.g==g /\ p.effect_annot == EffectAnnotSTT }) = 
    let (| u, ty_typing |) = Pulse.Checker.Pure.check_universe g t in
    let x = fresh g in
    let post' = open_term_nv post (ppname_default, x) in 
    let g' = push_binding g x ppname_default t in
    let post_typing_src = Pulse.Checker.Pure.check_slprop_with_core g' post' in
    assume (fresh_wrt x g (freevars post));
    {
      g; effect_annot=EffectAnnotSTT; effect_annot_typing=();
      ret_ty=t; u; ty_typing;
      post; x; post_typing_src; post_typing=RU.magic()
    }
  in
  let close_post = close_post x dom_g g1 (bindings_with_ppname g1) post in
  Pulse.Checker.Util.debug g "pulse.infer_post" (fun _ ->
    Printf.sprintf "Original postcondition: %s |= %s\nInferred postcondition: %s |= %s\n" 
    (env_to_string g1) (T.term_to_string post) (env_to_string g) (T.term_to_string close_post));
  let ph = mk_post_hint close_post in
  ph