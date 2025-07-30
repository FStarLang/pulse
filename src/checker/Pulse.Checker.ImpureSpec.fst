(*
   Copyright 2025 Microsoft Research

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

module Pulse.Checker.ImpureSpec
module R = FStar.Reflection.V2
module T = FStar.Tactics.V2
module RU = Pulse.RuntimeUtils
module PS = Pulse.Checker.Prover.Substs
open Pulse.Syntax.Base
open Pulse.Syntax.Pure
open Pulse.Checker.Prover.RewritesTo
open Pulse.Checker.Pure
open Pulse.Typing.Env
open Pulse.Checker.Base
open Pulse.Readback
open Pulse.Syntax.Naming
open Pulse.Reflection.Util

let rec get_rewrites_to_from_post (g: env) xres (post: slprop) : T.Tac (option R.term) =
  match inspect_term post with
  | Tm_Star p q ->
    (match get_rewrites_to_from_post g xres p with
    | None -> get_rewrites_to_from_post g xres q
    | Some res -> Some res)
  | Tm_Pure p ->
    ((if RU.debug_at_level (fstar_env g) "hhh" then let open Pulse.PP in info_doc g None [ text "IMPURE_SPEC"; pp post; ]);
    match is_rewrites_to_p p with
    | None -> None
    | Some (lhs, rhs) ->
      match R.inspect_ln lhs with
      | R.Tv_Var x ->
        let x = R.inspect_namedv x in
        if x.uniq = xres then
          ((if RU.debug_at_level (fstar_env g) "hhh" then let open Pulse.PP in info_doc g None [ text "IMPURE_SPEC found"; pp rhs; ]);
          // TODO: check that rhs does not contain xres
          Some rhs)
        else
          None
      | _ -> None)
  | _ -> None

let rec maybe_hoist (g:env) (ctxt: slprop) (t:R.term) : T.Tac (bool & R.term) = 
  match R.inspect_ln t with
  | R.Tv_Abs bv body ->
    let b = R.inspect_binder bv in
    let x = fresh g in
    let ppname = mk_ppname_no_range (T.unseal b.ppname) in
    // let px = b.ppname, x in
    let g' = push_binding g x ppname b.sort in
    let body = open_term_nv body (ppname, x) in
    let changed, body = maybe_hoist g' ctxt body in
    if changed then
      true, R.pack_ln (R.Tv_Abs bv (close_term body x))
    else
      false, t
  | _ ->
  let head, args = T.collect_app_ln t in
  match args with
  | [] -> false, t //no args to hoist
  | _ ->
  match is_stateful_application g t with
  | None -> (
    let g, binders, args = maybe_hoist_args g ctxt args in
    match binders with
    | false -> false, t // no elab
    | _ -> 
      let t = RU.mk_app_flat head args (T.range_of_term t) in
      binders, t
  )
  | Some _ -> (
    let g, binders, args = maybe_hoist_args g ctxt args in
    let t = RU.mk_app_flat head args (T.range_of_term t) in
    let (| uvs, t, ty |) = instantiate_term_implicits_uvs g t true in
    (if RU.debug_at_level (fstar_env g) "hhh" then
    let open Pulse.PP in
    info_doc g None [
      text "IMPURE_SPEC inferred type";
      pp t;
      pp ty;
    ]);
    match readback_comp ty with
    | None | Some (C_Tot ..) -> T.fail "impossible: not a stateful application type"
    | Some c -> match c with
    | C_STAtomic _ _ { pre; post } | C_STGhost _ { pre; post } | C_ST { pre; post } ->
      let x = fresh g in
      let x_ppn = mk_ppname_no_range "result" in
      let g' = push_binding g x (mk_ppname_no_range "result") ty in
      assume disjoint g' uvs;
      let post = open_term_nv post (x_ppn, x) in
      let (| post, _ |) = Pulse.Checker.Prover.normalize_slprop (push_env g' uvs) post true in 
      (if RU.debug_at_level (fstar_env g) "hhh" then let open Pulse.PP in info_doc g None [ text "IMPURE_SPEC post"; pp post; ]);
      match get_rewrites_to_from_post g x post with
      | None -> T.fail "cannot find rewrites_to"
      | Some rwr ->
        let allow_amb = true in
        let (| g', ss, _, _, _ |) = Pulse.Checker.Prover.prove allow_amb #g #ctxt (RU.magic ()) uvs #pre (RU.magic ()) in
        let rwr = PS.nt_subst_term rwr ss in
        // TODO: make sure that the prover doesn't extend the environment
        true, rwr
  )

and maybe_hoist_args (g:env) (ctxt: slprop) (args:list T.argv)
: T.Tac (env & bool & list T.argv)
= T.fold_right
    (fun (arg, q) (g, binders, args) ->
      let binders', arg = maybe_hoist g ctxt arg in
      let binders = binders' || binders in
      g, binders, (arg, q)::args)
    args
    (g, false, [])

(* Adds add to the ctxt in a way that the prover will prefer it when ambiguous. *)
let push_ctxt ctxt add = tm_star add ctxt

let inspect_ast_term (t: term) : term_view =
  let default_view = Tm_FStar t in
  let head, args = T.collect_app_ln t in
  match R.inspect_ln head, args with
  | R.Tv_FVar fv, [a1, R.Q_Explicit; a2, R.Q_Explicit] ->
    if R.inspect_fv fv = star_lid then
      Tm_Star a1 a2
    else
      default_view
  | R.Tv_FVar fv, [a1, R.Q_Explicit] ->
    if R.inspect_fv fv = exists_lid || R.inspect_fv fv = forall_lid then
      match R.inspect_ln a1 with
      | R.Tv_Abs b body ->
        let bview = R.inspect_binder b in
        let b = mk_binder_ppname a1 (mk_ppname bview.ppname (RU.binder_range b)) in
        if R.inspect_fv fv = exists_lid
        then Tm_ExistsSL u_unknown b body
        else Tm_ForallSL u_unknown b body
      | _ -> default_view
    else
      default_view
  | _ ->
    default_view


let rec purify_spec (g: env) (ctxt: slprop) (t: slprop) : T.Tac (t: slprop & tot_typing g t tm_slprop) =
  match inspect_ast_term t with
  | Tm_Star t s ->
    let (| t, _ |) = purify_spec g ctxt t in
    let (| s, _ |) = purify_spec g (push_ctxt ctxt t) s in
    (| tm_star t s, E (RU.magic ()) |)
  // TODO: exists
  | _ ->
    let _, t = maybe_hoist g ctxt t in
    check_slprop g t