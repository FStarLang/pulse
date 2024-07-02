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

module Pulse.Checker.Prover.ShareGather

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
  if Pulse.RuntimeUtils.debug_at_level (fstar_env g) "prover.share_gather"
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

let destruct_pts_to (v : vprop) : Tac (option (R.typ & R.term & R.term & R.term)) =
  match hua v with
  | Some (fv, _, [(ty, Q_Implicit); (r, Q_Explicit); (p, Q_Implicit); (e, Q_Explicit)]) ->
    if inspect_fv fv = ["Pulse"; "Lib"; "Reference"; "pts_to"]
    then Some (ty, r, p, e)
    else None
  | _ -> None


(* Returns Some p' when p is of the form (p' /. 2.0R) *)
let is_half (p:R.term) : T.Tac (option R.term) =
  match hua p with
  | Some (fv, [], [(perm, Q_Explicit); (denom, Q_Explicit)]) ->
    if inspect_fv fv = ["FStar"; "Real"; "op_Slash_Dot"]
       && term_eq denom (`2.0R)
    then Some perm
    else None
  | _ -> None


let rec destruct_halves (t : R.term) : Tac (nat & R.term) =
  match is_half t with
  | Some p ->
    let n, p = destruct_halves p in
    (n + 1, p)
  | _ -> (0, t)

let destruct_pts_to_half_n (v : vprop) : Tac (option (nat & R.typ & R.term & R.term & R.term)) =
  match destruct_pts_to v with
  | Some (ty, r, p, e) -> (
    let n, p = destruct_halves p in
    Some (n, ty, r, p, e)
  )
  | _ -> None

let destruct_pts_to_half (v : vprop) : Tac (option (R.typ & R.term & R.term & R.term)) =
  match destruct_pts_to v with
  | Some (ty, r, p, e) -> (
    (match is_half p with
     | Some p' -> Some (ty, r, p', e)
     | None -> None)
  )
  | _ -> None

let is_pts_to (t_r t_p t_e : R.term) (v : vprop) : Tac bool =
  match destruct_pts_to v with
  | Some (_, r, p, e) -> term_eq t_r r && term_eq t_p p && term_eq t_e e
  | None -> false

let is_pts_to_half_any (t_r t_p : R.term) (v : vprop) : Tac (option R.term) =
  match destruct_pts_to_half v with
  | Some (_, r, p, e) ->
    if term_eq t_r r && term_eq t_p p
    then Some e
    else None
  | None -> None

let is_pts_to_half (t_r t_p t_e : R.term) (v : vprop) : Tac bool =
  match destruct_pts_to_half v with
  | Some (_, r, p, e) -> term_eq t_r r && term_eq t_p p && term_eq t_e e
  | None -> false
  
let mk_pts_to rng (ty r p e : R.term) : term =
  mk_app (pack (Tv_FVar (pack_fv ["Pulse"; "Lib"; "Reference"; "pts_to"]))) [
    (ty, Q_Implicit);
    (r, Q_Explicit);
    (p, Q_Implicit);
    (e, Q_Explicit);
  ]

let rec find_pts_to (t_r t_p t_v : R.term) (ctx : list vprop) : Tac (option (vprop & list vprop)) =
  match ctx with
  | [] -> None
  | v::vs ->
    if is_pts_to t_r t_p t_v v then
      Some (v, vs)
    else
      let! (v', vs) = find_pts_to t_r t_p t_v vs in
      return (v', v::vs)

let rec find_pts_to_half (t_r t_p t_v : R.term) (ctx : list vprop) : Tac (option (vprop & list vprop)) =
  match ctx with
  | [] -> None
  | v::vs ->
    if is_pts_to_half t_r t_p t_v v then
      Some (v, vs)
    else
      let! (v', vs) = find_pts_to_half t_r t_p t_v vs in
      return (v', v::vs)

let rec find_pts_to_half_any (t_r t_p : R.term) (ctx : list vprop) : Tac (option (R.term & vprop & list vprop)) =
  match ctx with
  | [] -> None
  | v::vs ->
    match is_pts_to_half_any t_r t_p v with
    | Some e -> Some (e, v, vs)
    | None ->
      let! (e', v', vs) = find_pts_to_half_any t_r t_p vs in
      return (e', v', v::vs)

let rec find_two_halves (ctx : list vprop) : Tac (option ((R.typ & R.term & R.term & R.term) & R.term & vprop & vprop & list vprop)) =
  match ctx with
  | [] -> None
  | v::vs ->
    let fallback () =
      let! (r, e, v1, v2, vs) = find_two_halves vs in
      Some (r, e, v1, v2, v::vs)
    in
    (
      let! (ty, r, p, e) = destruct_pts_to_half v in
      let! (e', v', vs') = find_pts_to_half_any r p vs in
      Some ((ty, r, p, e), e', v, v', vs')
     ) <|> fallback

let eager_gather1 (#preamble:preamble) (pst:prover_state preamble)
  : T.Tac (option (pst':prover_state preamble { pst' `pst_extends` pst /\
                                        pst'.unsolved == pst.unsolved }))
  = 
  let rng = match pst.remaining_ctxt with
    | [] -> FStar.Range.range_0
    | v::_ -> range_of_term v
  in

  debug pst.pg (fun () ->
    warn_doc pst.pg (Some rng) [
      text "Trying eager gather";
      text "Unsolved: " ^^ pp pst.unsolved;
      text "Solved: " ^^ pp pst.solved;
      text "Remaining ctx: " ^^ pp pst.remaining_ctxt;
    ]);
  match find_two_halves pst.remaining_ctxt with
  | None ->
    T.print "No two halves found";
    None
  | Some ((ty, r, p, e), e', v1, v2, ctxt') ->
    let v = mk_pts_to (range_of_term v1) ty r p e in

    let eq : vprop = tm_pure (RU.mk_eq2 (pack_universe Uv_Zero) ty e e') in

    let new_ctx = v::eq::ctxt' in
    let k1 :
      continuation_elaborator pst.pg (list_as_vprop pst.remaining_ctxt * preamble.frame * PS.ss_term pst.solved pst.ss)
                              pst.pg (list_as_vprop new_ctx * preamble.frame * PS.ss_term pst.solved pst.ss)
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

      k = k_elab_trans k2 k1;
    }
    in
    Some pst'

let rec eager_gather #preamble pst =
  match eager_gather1 pst with
  | Some pst' -> eager_gather { pst' with progress = true }
  | None -> pst
  
let rec mk_n_half (n:nat) (p : R.term) : R.term =
  if n = 0
  then p
  else
  mk_e_app
    (pack (Tv_FVar (pack_fv ["FStar"; "Real"; "op_Slash_Dot"])))
    [
      (mk_n_half (n - 1) p);
      (`2.0R);	
    ]
  
let mk_half (p : R.term) : R.term = mk_n_half 1 p

let rec find_least_split (nsplits : nat) (ty r p e : R.term) (ctx : list vprop)
: Tac (option (
      (* number of splits *) nat &
      (* perm  *) R.term &
      (* the matched vprop *) vprop &
      (* other halves breakdown *) list vprop &
      (* rest of ctx *)list vprop))
=
  let p' = mk_n_half nsplits p in
  match find_pts_to r p' e ctx with
  | None ->
    if nsplits > 0
    then 
      let other_half = mk_pts_to Range.range_0 ty r p' e in
      let! (n, p', v, hs, ctx') = find_least_split (nsplits - 1) ty r p e ctx in
      Some (n, p', v, other_half::hs, ctx')
    else None
  | Some (v, ctxt') ->
    Some (nsplits, p', v, [], ctxt')

let share (#preamble:preamble) (pst:prover_state preamble)
  (q:vprop) (unsolved':list vprop)
  (_:squash (pst.unsolved == q::unsolved'))
  (prover:prover_t)
: T.Tac (option (pst':prover_state preamble { pst' `pst_extends` pst }))
=
  let q_rng = range_of_term q in
  debug pst.pg (fun () ->
  warn_doc pst.pg (Some q_rng) [
    text "Trying share for resource:" ^/^ pp q;
    text "Unsolved:" ^/^ pp pst.unsolved;
    text "Solved:" ^/^ pp pst.solved;
    text "Remaining ctx:" ^/^ pp pst.remaining_ctxt;
  ]);

  match destruct_pts_to_half_n q with
  | None ->
    debug pst.pg (fun () ->
    warn_doc pst.pg (Some (range_of_term q)) [
      text "Goal is not a pts_to";
    ]);
    None
  | Some (nsplits, ty, r, p, e) ->
  (* We got pts_to r #(full / 2^nsplits) e *)

  (* Find some pts_to r #(full / 2^n) e in the context, with n <= nsplits *)
  match find_least_split nsplits ty r p e pst.remaining_ctxt with
  | None ->
    debug pst.pg (fun () ->
    warn_doc pst.pg (Some q_rng) [
      text "NO SPLIT FOUND"
    ]);
    None
  | Some (n', p', v, hs, ctxt') ->
  
  debug pst.pg (fun () ->
  warn_doc pst.pg (Some q_rng) [
    text "Found half of: " ^/^ pp q ^/^ text "in ctx" ^/^ pp ((n' <: int), p', v, hs, ctxt');
  ]);
  
  let new_ctx = hs@ctxt' in
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

let gather (#preamble:preamble) (pst:prover_state preamble)
  (q:vprop) (unsolved':list vprop)
  (_:squash (pst.unsolved == q::unsolved'))
  (prover:prover_t)
: T.Tac (option (pst':prover_state preamble { pst' `pst_extends` pst }))
=
  let q_rng = range_of_term q in
  debug pst.pg (fun () ->
  warn_doc pst.pg (Some q_rng) [
    text "Trying gather for resource:" ^/^ pp q;
    text "Unsolved:" ^/^ pp pst.unsolved;
    text "Solved:" ^/^ pp pst.solved;
    text "Remaining ctx:" ^/^ pp pst.remaining_ctxt;
  ]);

  match destruct_pts_to q with
  | None ->
    debug pst.pg (fun () ->
    warn_doc pst.pg (Some q_rng) [
      text "Goal is not a pts_to";
    ]);
    None
  | Some (ty, r, p, e) ->
  (* We got pts_to #ty r #p e *)

  (* Is the same vprop already in the context? *)
  match find_pts_to r p e pst.remaining_ctxt with
  | Some (v, ctxt') -> (
    let new_ctx = ctxt' in
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
  )

  | None ->
    (* Not exactly in ctxt, is are there two pts_to #ty r #(p /. 2.0R) e? *)
    match find_pts_to_half r p e pst.remaining_ctxt with
    | None ->
      None
    | Some (v, ctxt') ->
      match find_pts_to_half r p e ctxt' with
      | None ->
        None
      | Some (v', ctxt'') ->
        let new_ctx = ctxt'' in
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
