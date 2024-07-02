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

module Pulse.Checker.Prover.AutoLem

open FStar.Tactics.V2
open FStar.Reflection.V2.TermEq
open Pulse.Checker.Base
open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Env

open Pulse.PP
open Pulse.Show

open FStar.List.Tot.Base

module PS = Pulse.Checker.Prover.Substs
module R = FStar.Reflection.V2
module Comb = Pulse.Typing.Combinators
module RU = Pulse.Reflection.Util

let debug (g:env) (f : unit -> Tac unit) =
  if true || Pulse.RuntimeUtils.debug_at_level (fstar_env g) "prover.autolem"
  then f ()

class tacmonad (t : Type u#a -> Type u#a) = {
  return : #a:Type -> a -> Tac (t a);
  ( let! ) : #a:Type -> #b:Type -> t a -> (a -> Tac (t b)) -> Tac (t b);
}

instance _ : tacmonad option = {
  return = (fun x -> Some x);
  ( let! ) = (fun #a #b (x : option a) (f : a -> Tac (option b)) ->
    match x with
    | None -> None
    | Some x -> f x);
}

class tac_alternative (t : Type u#a) = {
  empty : t;
  ( <|> ) : t -> (unit -> Tac t) -> Tac t;
}

instance alternative_option (a:Type) : tac_alternative (option a) = {
  empty = None;
  ( <|> ) = (fun x y -> match x with None -> y () | Some _ -> x)
}

let hua (t:R.term) : Tac (option (R.fv & list universe & list argv)) =
  let hd, args = collect_app_ln t in
  match inspect hd with
  | Tv_FVar fv     -> Some (fv, [], args)
  | Tv_UInst fv us -> Some (fv, us, args)
  | _ -> None 

let eager_autolem1 (#preamble:preamble) (pst:prover_state preamble)
  : Tac (option (pst':prover_state preamble { pst' `pst_extends` pst /\
                                        pst'.unsolved == pst.unsolved }))
  = 
  None
  // let rng = match pst.remaining_ctxt with
  //   | [] -> FStar.Range.range_0
  //   | v::_ -> v.range
  // in

  // debug pst.pg (fun () ->
  //   warn_doc pst.pg (Some rng) [
  //     text "Trying eager gather";
  //     text "Unsolved: " ^^ pp pst.unsolved;
  //     text "Solved: " ^^ pp pst.solved;
  //     text "Remaining ctx: " ^^ pp pst.remaining_ctxt;
  //   ]);
  // match find_two_halves pst.remaining_ctxt with
  // | None -> None
  // | Some ((ty, r, p, e), e', v1, v2, ctxt') ->
  //   let v = mk_pts_to v1.range ty r p e in

  //   let eq : vprop = {
  //      t = Tm_Pure (tm_fstar (RU.mk_eq2 (pack_universe Uv_Zero) ty e e') v.range);
  //      range = v.range
  //   } in

  //   let new_ctx = v::eq::ctxt' in
  //   let k1 :
  //     continuation_elaborator pst.pg (Comb.list_as_vprop pst.remaining_ctxt * preamble.frame * PS.ss_term pst.solved pst.ss)
  //                             pst.pg (Comb.list_as_vprop new_ctx * preamble.frame * PS.ss_term pst.solved pst.ss)
  //   = fun post (| t, c, d |) ->
  //       admit();
  //       (| t, c, d |)
  //   in
  //   let k2 :

  //     continuation_elaborator preamble.g0 (preamble.ctxt * preamble.frame)
  //                             pst.pg (Comb.list_as_vprop pst.remaining_ctxt * preamble.frame * PS.ss_term pst.solved pst.ss)
  //   = pst.k
  //   in
  //   let pst' = { pst with
  //     remaining_ctxt = new_ctx;
  //     remaining_ctxt_frame_typing = magic();

  //     k = k_elab_trans k2 k1;
  //   }
  //   in
  //   Some pst'

let rec eager_autolem #preamble pst =
  match eager_autolem1 pst with
  | Some pst' -> eager_autolem pst'
  | None -> pst

let guided_autolem_attr : Reflection.term = pack (Tv_FVar (pack_fv ["Pulse"; "Lib"; "Core"; "guided_autolem"]))

instance pp_fv : printable Reflection.fv = {
  pp = (fun fv -> pp (pack (Tv_FVar fv)))
}
instance pp_aqualv : printable aqualv = {
  pp = (fun x -> match x with | Q_Explicit -> text "Q_Explicit" | Q_Implicit -> text "Q_Implicit" | Q_Meta t -> text "Q_Meta" ^/^ pp t)
}

instance pp_binder : printable Tactics.NamedView.binder = {
  pp = (fun (b:Tactics.NamedView.binder) -> pp (unseal b.ppname, b.sort, b.qual));
}

instance pp_tot_or_ghost : printable tot_or_ghost = {
  pp = (fun x -> match x with | E_Total -> text "E_Total" | E_Ghost -> text "E_Ghost")
}

exception Retry

let rec apply_first #a #b (f : a -> Tac (option b)) (cands : list a) : Tac (option b) =
  match cands with
  | [] -> None
  | x::xs ->
    match try f x with | Retry -> None | e -> raise e with
    | Some y -> Some y
    | None -> apply_first f xs
    
let n_args (typ:R.term) : Tac nat =
  let bs, c = collect_arr typ in
  List.length bs

 
instance pp_comp_view : printable comp_view = {
  pp = (fun x -> match x with
     | C_Total ret -> text "C_Total" ^/^ pp ret
     | C_GTotal ret -> text "C_GTotal" ^/^ pp ret
     | C_Lemma pre post pats -> text "C_Lemma" ^/^ pp pre ^/^ pp post ^/^ pp pats
     | C_Eff us eff_name result eff_args decrs -> text "C_Eff" ^/^ pp us ^/^ pp eff_name ^/^ pp result ^/^ pp eff_args ^/^ pp decrs
)                 
}

(* FIXME: duplicated *)
let binder_to_r_namedv (b:Tactics.NamedView.binder) : R.namedv =
  R.pack_namedv {
    uniq = b.uniq;
    sort = seal b.sort;
    ppname = b.ppname;
  }

let apply_wild (e:R.env) (t : R.term) (bs : binders) : Tac (R.term & subst_t & list R.term) = 
  let rec go (t : R.term) (bs : binders) (subst : subst_t) (uvs:list R.term) : Tac (R.term & subst_t & list R.term) =
    match bs with
    | [] -> t, subst, uvs
    | b::bs -> 
      let ut = uvar_env e (Some (R.subst_term subst b.sort)) in
      let subst' = (R.NT (binder_to_r_namedv b) ut)::subst in
      go (Tv_App t (ut, b.qual)) bs subst' (ut::uvs)
  in
  go t bs [] []

open FStar.Tactics.V2.SyntaxCoercions

let push_binding e (b:R.binding) : Tac R.env =
  // print ("PUSHING BINDING " ^ unseal b.ppname ^ "--" ^ show (b.uniq <: int));
  R.push_binding e b

instance _ : tac_showable R.comp = {
  show = (fun c -> Tactics.comp_to_string c);
}

instance _ : tac_showable Tactics.NamedView.comp = {
  show = (fun c -> show (R.pack_comp c));
}

instance _ : printable R.binding = {
  pp = (fun (b:R.binding) -> pp (unseal b.ppname) ^^ doc_of_string "--" ^^ pp (b.uniq <: int));
}

let instantiate_fun #preamble (pst : prover_state preamble) (e:R.env) (t typ : R.term) : Tac (R.env & (*uvars*)list R.term & R.term & R.typ) =
  let bs, c = collect_arr_bs typ in
  // warn_doc pst.pg None [
  //   text "Destructed" ^/^ pp typ;
  //   text "bs =" ^/^ pp bs;
  //   text "c =" ^/^ pp c;
  // ];

  let e' = Tactics.fold_left (fun e (b:Tactics.NamedView.binder) -> push_binding e b) e bs in
  let t', s, uvs = apply_wild e' t bs in
  let c = R.inspect_comp <| R.subst_comp s <| R.pack_comp c in
  match c with
  | C_Total ty -> e', uvs, t', ty
  | _ -> Tactics.fail "instantiate_fun: not a total comp"
  
  // | Tm_Emp        : term'
  // | Tm_Pure       : p:term -> term'
  // | Tm_Star       : l:vprop -> r:vprop -> term'
  // | Tm_ExistsSL   : u:universe -> b:binder -> body:vprop -> term'
  // | Tm_ForallSL   : u:universe -> b:binder -> body:vprop -> term'
  // | Tm_VProp      : term'
  // | Tm_Inv        : vprop -> term'
  // | Tm_Inames     : term'  // type inames
  // | Tm_EmpInames  : term'
  // | Tm_AddInv     : i:term -> is:term -> term'
  // | Tm_FStar      : host_term -> term'
  // | Tm_Unknown    : term'

let rec explode (t:term) : Tac (list (t:R.term)) =
  match inspect_term t with
  | Tm_Star l r -> explode l @ explode r
  | Tm_FStar t -> [t]
  | _ -> []
 
let rec remove1 e (ctx : list vprop) (p : R.term) : Tac (list vprop) =
  match ctx with
  | [] -> 
    Tactics.print ("Could not find in ctx:" ^ show p );
    raise Retry // Tactics.fail "vprop p in pre not found in ctx"
  | q::qs -> if unify_env e q p then qs else q::(remove1 e qs p)
  
let rec remove e (ctx : list vprop) (pre : list R.term) : Tac (list vprop) =
  match pre with
  | [] -> ctx
  | p::ps ->
    print ("TRYING to remove (" ^ show p ^ ") from ctx: " ^ show ctx);
    remove e (remove1 e ctx p) ps

let typ_of_fv (fv:R.fv) : Tac R.typ =
  match lookup_typ (top_env ()) (inspect_fv fv) with
  | None -> Tactics.fail "sigelt not found"
  | Some se ->
    match inspect_sigelt se with
    | Sg_Let {lbs=[lb]} -> lb.lb_typ
    | Sg_Val {typ} -> typ
    | _ -> Tactics.fail "unexpected sigelt"

#push-options "--z3rlimit 20"
let guided_autolem1 (#preamble:preamble) (pst:prover_state preamble)
  (q:vprop) (unsolved':list vprop)
  (_:squash (pst.unsolved == q::unsolved'))
  (prover:prover_t)
  (fv:Reflection.fv)
: Tac (option (pst':prover_state preamble { pst' `pst_extends` pst }))
=
  let q_rng = range_of_term q in
  debug pst.pg (fun () ->
  warn_doc pst.pg (Some q_rng) [
    text "Trying candidate autolem" ^/^ pp fv ^/^ text "for resource:" ^/^ pp q;
    text "Unsolved:" ^/^ pp pst.unsolved;
    text "Solved:" ^/^ pp pst.solved;
    text "Remaining ctx:" ^/^ pp pst.remaining_ctxt;
    text "env =" ^/^ pp (vars_of_env (elab_env pst.pg));
  ]);
  
  let e0 = pst.pg in

  let tm = pack (Tv_FVar fv) in
  let typ = typ_of_fv fv in
  warn_doc pst.pg (Some q_rng) [
    text "typ = " ^/^ pp typ;
  ];

  let fe0 = elab_env e0 in
  let e', uvs, tm, typ = instantiate_fun pst fe0 tm typ in
  
  match readback_comp typ with | None -> None | Some cc ->

  // debug pst.pg (fun () -> warn_doc pst.pg (Some q_rng) [
  //   text "cc = " ^/^ pp (cc <: comp);
  // ]);
  
  match cc with
  | C_Tot _ ->
    debug pst.pg (fun () -> warn_doc pst.pg (Some q_rng) [
      text "Skipping " ^/^ pp fv ^/^ text "because it's a total term";
    ]);
    None
  | C_STAtomic _ _ _
  | C_ST _ ->
    debug pst.pg (fun () -> warn_doc pst.pg (Some q_rng) [
      text "Skipping " ^/^ pp fv ^/^ text "because it's a" ^/^ pp (ctag_of_comp_st cc);
    ]);
    None
  | C_STGhost _ {u; res; pre; post} ->
    // FIXME: check res is unit
    debug pst.pg (fun () -> warn_doc pst.pg (Some q_rng) [
      pp fv ^/^ text "is a ghost step";
      text "u = " ^/^ pp u;
      text "res = " ^/^ pp res;
      text "pre = " ^/^ pp pre;
      text "post = " ^/^ pp (map (fun (t:(t:R.term)) -> t <: R.term) <| explode post);
    ]);
    match explode post with
    | [] -> None
    | trig::rest ->
    // debug pst.pg (fun () ->
    warn_doc pst.pg (Some q_rng) [
      text "Trying to unify post with the resource";
      text "trig = " ^/^ pp trig;
      text "q = " ^/^ pp q;
      text "env =" ^/^ pp (vars_of_env e');
    ];
    print "{{";
    let b = unify_env e' trig q in
    print "}}";
    debug pst.pg (fun () -> warn_doc pst.pg (Some q_rng) [
      text "unif result = " ^/^ pp b;
      text "u = " ^/^ pp u;
      text "res = " ^/^ pp res;
      text "pre = " ^/^ pp pre;
      text "post = " ^/^ pp (map (fun (t:(t:R.term)) -> t <: R.term) <| explode post);
      text "t = " ^/^ pp tm;
    ]);
    
    if not b then raise Retry;
    
    (* SUCCESS *)
    
    let pre' = map (fun (t:(t:R.term)) -> t <: R.term) <| explode pre in
    let new_ctx = rest @ (remove e' pst.remaining_ctxt pre') in
    warn_doc pst.pg (Some q_rng) [
      text "new_ctx = " ^/^ pp new_ctx;
    ];
    let k1 :
      continuation_elaborator pst.pg (list_as_vprop pst.remaining_ctxt * preamble.frame * PS.ss_term pst.solved pst.ss)
                              pst.pg (list_as_vprop new_ctx * preamble.frame * PS.ss_term (q * pst.solved) pst.ss)
    = fun post (| t, c, d |) ->
        admit();
        (| t, c, d |)
    in
    let k2 :

      continuation_elaborator preamble.g0 (preamble.ctxt * preamble.frame)
                              pst.pg (list_as_vprop pst.remaining_ctxt * preamble.frame * PS.ss_term pst.solved pst.ss)
    = pst.k
    in
    let pst' = { pst with
      remaining_ctxt = new_ctx;
      remaining_ctxt_frame_typing = magic();

      unsolved = unsolved';
      solved = q * pst.solved;

      goals_inv = magic();
      solved_inv = magic();

      k = k_elab_trans k2 k1;
    }
    in
    Some pst'

let guided_autolem (#preamble:preamble) (pst:prover_state preamble)
  (q:vprop) (unsolved':list vprop)
  (_:squash (pst.unsolved == q::unsolved'))
  (prover:prover_t)
: Tac (option (pst':prover_state preamble { pst' `pst_extends` pst }))
=
  let q_rng = range_of_term q in
  debug pst.pg (fun () ->
  warn_doc pst.pg (Some q_rng) [
    text "Trying autolem for resource:" ^/^ pp q;
    text "Unsolved:" ^/^ pp pst.unsolved;
    text "Solved:" ^/^ pp pst.solved;
    text "Remaining ctx:" ^/^ pp pst.remaining_ctxt;
  ]);
  
  let cands = lookup_attr (guided_autolem_attr) (fstar_env pst.pg) in
  
  debug pst.pg (fun () ->
  warn_doc pst.pg (Some q_rng) [
    text "Candidates = " ^/^ pp cands;
  ]);
  
  (* Try candidates in order, stop on first success. *)
  cands |> apply_first (guided_autolem1 pst q unsolved' () prover)
