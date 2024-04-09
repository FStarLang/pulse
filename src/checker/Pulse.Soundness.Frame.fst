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

module Pulse.Soundness.Frame
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common
(*** Soundness of frame elaboration *)

#push-options "--fuel 2 --ifuel 1"
let inst_frame_t #u #g #head
                 (head_typing: RT.tot_typing g head (frame_type u))
                 (#t:_)
                 (t_typing: RT.tot_typing g t (RT.tm_type u))
  : GTot (RT.tot_typing g (R.mk_app head [(t, R.Q_Implicit)]) (frame_type_t u t))
  = admit()

let inst_frame_pre #u #g #head #t
                 (head_typing: RT.tot_typing g head (frame_type_t u t))
                 (#pre:_)
                 (pre_typing: RT.tot_typing g pre vprop_tm)
  : GTot (RT.tot_typing g (R.mk_app head [(pre, R.Q_Implicit)]) (frame_type_t_pre u t pre))
  = admit()

let inst_frame_post #u #g #head #t #pre
                    (head_typing: RT.tot_typing g head (frame_type_t_pre u t pre))
                    (#post:_)
                    (post_typing: RT.tot_typing g post (mk_arrow (t, R.Q_Explicit) vprop_tm))
  : GTot (RT.tot_typing g (R.mk_app head [(post, R.Q_Implicit)])
                          (frame_type_t_pre_post u t pre post))
  = admit()

let inst_frame_frame #u #g #head #t #pre #post
                     (head_typing: RT.tot_typing g head (frame_type_t_pre_post u t pre post))
                     (#frame:_)
                     (frame_typing: RT.tot_typing g frame vprop_tm)
  : GTot (RT.tot_typing g (R.mk_app head [(frame, R.Q_Explicit)])
                          (frame_type_t_pre_post_frame u t pre post frame))
  = admit()

let inst_frame_comp #u #g #head #t #pre #post #frame
                    (head_typing: RT.tot_typing g head (frame_type_t_pre_post_frame u t pre post frame))
                    (#f:_)
                    (f_typing:RT.tot_typing g f (mk_stt_comp u t pre post))
  : GTot (RT.tot_typing g (R.mk_app head [(f, R.Q_Explicit)])
                          (frame_res u t pre post frame))
  = admit()

(* stt t pre (fun x -> (fun x -> post) x * frame)   ~ 
   stt t pre (fun x -> post * frame) *)
let equiv_frame_post (g:R.env) 
                     (u:R.universe)
                     (t:R.term)
                     (pre:R.term) 
                     (post:term) // ln 1
                     (frame:R.term) //ln 0
  : GTot (RT.equiv g (mk_stt_comp u t pre (mk_abs t R.Q_Explicit (mk_star (R.mk_app (mk_abs t R.Q_Explicit post)
                                                                           [bound_var 0, R.Q_Explicit]) frame)))
                     (mk_stt_comp u t pre (mk_abs t R.Q_Explicit (mk_star post frame))))
  = admit()

#push-options "--z3rlimit_factor 4 --ifuel 1 --fuel 4"
let elab_frame_typing (g:stt_env)
                      (e:R.term)
                      (c:ln_comp)
                      (frame:term)
                      (frame_typing: tot_typing g frame tm_vprop)
                      (e_typing: RT.tot_typing (elab_env g) e (elab_comp c))
  : GTot (RT.tot_typing (elab_env g)
                        (elab_frame c frame e)
                        (elab_comp (add_frame c frame)))
  = if C_ST? c then
    let frame_typing = tot_typing_soundness frame_typing in
    let rg = elab_env g in
    let u = comp_u c in
    let frame_fv = R.pack_fv (mk_pulse_lib_core_lid "frame_stt") in
    let head = R.pack_ln (R.Tv_UInst frame_fv [u]) in
    assume (RT.lookup_fvar_uinst rg frame_fv [u] == Some (frame_type u));
    let head_typing : RT.tot_typing _ _ (frame_type u) = RT.T_UInst rg frame_fv [u] in
    let (| _, c_typing |) = RT.type_correctness _ _ _ e_typing in
    let t_typing, pre_typing, post_typing = inversion_of_stt_typing _ _ c_typing in
    let t = comp_res c in
    let t_typing : RT.tot_typing rg t (RT.tm_type u) = t_typing in
    let d : RT.tot_typing (elab_env g)
                          (elab_frame c frame e)
                          (frame_res u t (comp_pre c)
                                         (elab_comp_post c)
                                         frame) =
        inst_frame_comp
          (inst_frame_frame
            (inst_frame_post
                (inst_frame_pre 
                  (inst_frame_t head_typing t_typing)
                 pre_typing)
             post_typing)
           frame_typing)
          e_typing
    in
    RT.T_Sub _ _ _ _ d
      (RT.Relc_typ _ _ _ _ _
         (RT.Rel_equiv _ _ _ _
            (equiv_frame_post rg u t 
               (tm_star (comp_pre c) frame)
               (comp_post c)
               frame)))
    else admit ()
#pop-options

#pop-options
