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

module Pulse.Readback
module R = FStar.Reflection.V2
open Pulse.Syntax.Base
open Pulse.Reflection.Util
module RU = Pulse.RuntimeUtils
module T = FStar.Tactics
let debug_log (f: unit -> T.Tac unit) : T.Tac unit = if RU.debug_at_level_no_module "readback" then f()

let (let?) (f:option 'a) (g:'a -> option 'b) : option 'b =
  match f with
  | None -> None
  | Some x -> g x

let readback_observability (t:R.term)
: option (obs:observability { elab_observability obs == t })
= let open R in
  match inspect_ln t with
  | R.Tv_FVar fv ->
    let fv_lid = inspect_fv fv in
    if fv_lid = observable_lid
    then Some Observable
    else if fv_lid = unobservable_lid
    then Some Unobservable
    else if fv_lid = neutral_lid
    then Some Neutral
    else None
  | _ -> None

#push-options "--z3rlimit_factor 20"
// TODO: FIXME: may be mark as opaque_to_smt
let try_readback_st_comp (t:R.term)
  : option (c:comp{elab_comp c == t}) =

  let open R in
  let hd, args = collect_app_ln t in
  match inspect_ln hd with
  | Tv_UInst fv [u] ->
    let fv_lid = inspect_fv fv in
    if fv_lid = stt_lid
    then match args with
         | [res; pre; post] ->
           (match inspect_ln (fst post) with
            | Tv_Abs b body ->
              let { qual=aq; attrs=attrs; sort=sort } =
                  inspect_binder b
              in    
              assume (fv == stt_fv);
              assume (aq == Q_Explicit           /\
                      attrs == []                /\
                      sort == fst res /\
                      snd res == Q_Explicit      /\
                      snd pre == Q_Explicit      /\
                      snd post == Q_Explicit);

              assume (t == mk_stt_comp u (fst res) (fst pre) (mk_abs (fst res) R.Q_Explicit body));
              let res' = fst res in
              let pre' = fst pre in
              let post' = body in
              let c = C_ST {u; res=res'; pre=pre';post=post'} in
              Some (c <: c:Pulse.Syntax.Base.comp{ elab_comp c == t })
            | _ -> None)
         | _ -> None
    else if fv_lid = stt_atomic_lid
    then match args with
         | [res; obs; opened; pre; post] ->
           (match inspect_ln (fst post) with
            | Tv_Abs b body ->
              let { qual=aq; attrs=attrs }
                  = inspect_binder b
              in    
              let res' = fst res in
              let? obs' = readback_observability (fst obs) in
              let opened' = fst opened in
              let pre' = fst pre in
              let post' = body in
              assume (t == mk_stt_atomic_comp (fst obs) u (fst res) (fst opened) (fst pre) (mk_abs (fst res) R.Q_Explicit body));
              let c = C_STAtomic opened' obs' ({u; res=res'; pre=pre';post=post'}) in
              Some (c <: c:Pulse.Syntax.Base.comp { elab_comp c == t })
            | _ -> None)
         | _ -> None
    else if fv_lid = stt_ghost_lid
    then match args with
         | [res; pre; post] ->
           (match inspect_ln (fst post) with
            | Tv_Abs b body ->
              let { qual=aq; attrs=attrs }
                  = inspect_binder b
              in    
              let res' = fst res in
              let pre' = fst pre in
              let post' = body in
              assume (t == mk_stt_ghost_comp u (fst res) (fst pre) (mk_abs (fst res) R.Q_Explicit body));
              let c = C_STGhost ({u; res=res'; pre=pre';post=post'}) in
              Some (c <: c:Pulse.Syntax.Base.comp { elab_comp c == t })
            | _ -> None)
         | _ -> None    
    else None  
  | _ -> None
#pop-options

let readback_qual = function
  | R.Q_Implicit -> Some Implicit
  | _ -> None

let rec readback_ty (t:R.term)
  : (r:option term_view { Some? r ==> (Some?.v r `is_view_of` t) }) =

  let open R in
  let open Pulse.Syntax.Base in

  let return tv = Some tv in
  pack_inspect_inv t;

  match inspect_ln t with
  | Tv_FVar fv ->
    let fv_lid = inspect_fv fv in
    if fv_lid = vprop_lid
    then return Tm_VProp
    else if fv_lid = emp_lid
    then return Tm_Emp
    else if fv_lid = inames_lid
    then return Tm_Inames
    else if fv_lid = emp_inames_lid
    then return Tm_EmpInames
    else None

  | Tv_App hd (a, q) ->
    admit(); //this case doesn't work because it is using collect_app_ln, etc.
    let head, args = collect_app_ln t in
    begin
      match inspect_ln head, args with
      | Tv_FVar fv, [a1; a2] ->
        if inspect_fv fv = star_lid
        then return (Tm_Star (fst a1) (fst a2))
        else None
      | Tv_UInst fv [u], [a1; a2] ->
        if inspect_fv fv = exists_lid ||
           inspect_fv fv = forall_lid
        then (
          let t1 : R.term = fst a1 in
          let t2 : R.term = fst a2 in
          let ty = t1 in
          let? (ppname, range, p) =
            match inspect_ln t2 with
            | Tv_Abs b body ->
              let p = body in
              let bview = inspect_binder b in
              Some (bview.ppname, RU.binder_range b, p) <: option (ppname_t & range & term)
            | _ -> None in  // TODO: FIXME: provide error from this function?
          let b = mk_binder_ppname ty (mk_ppname ppname range) in
          if inspect_fv fv = exists_lid
          then return (Tm_ExistsSL u b p)
          else return (Tm_ForallSL u b p)
        )
        else None
     | Tv_FVar fv, [a] ->
        if inspect_fv fv = pure_lid
        then return (Tm_Pure (fst a))
        else if inspect_fv fv = inv_lid
        then return (Tm_Inv (fst a))
        else None
     | _ -> None
    end

  | Tv_Refine _ _
  | Tv_Arrow _ _
  | Tv_Type _
  | Tv_Const _
  | Tv_Let _ _ _ _ _
  | Tv_Var _
  | Tv_BVar _
  | Tv_UInst _ _
  | Tv_Match _ _ _
  | Tv_Abs _ _ -> None

  | Tv_AscribedT t _ _ _
  | Tv_AscribedC t _ _ _ ->
    //this case doesn't work because it is unascribing
    admit();
    readback_ty t

  | Tv_Uvar _ _ -> None
  
  | Tv_Unknown -> return Tm_Unknown

  | Tv_Unsupp -> None


let readback_comp (t:R.term)
  : option (c:comp { elab_comp c == t }) =

  let ropt = try_readback_st_comp t in
  match ropt with
  | Some c ->
    // debug_log (fun _ -> T.print (Printf.sprintf "readback_comp: %s as\n%s\n" (T.term_to_string t) (P.comp_to_string c)));
    ropt
  | _ ->
    let t' = t in
    Some (C_Tot t' <: c:comp{ elab_comp c == t })
