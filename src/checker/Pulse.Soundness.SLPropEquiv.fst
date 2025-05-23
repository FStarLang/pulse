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

module Pulse.Soundness.SLPropEquiv
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Elaborate
open Pulse.Soundness.Common
open Pulse.Checker.SLPropEquiv

(*** Soundness of slprop equivalence **)

let slprop_equiv_refl_type = 
  let var = 0 in
  let v = mk_name var in
  mk_arrow (tm_slprop, R.Q_Explicit)
           (RT.close_term (stt_slprop_equiv v v) var)

let inst_slprop_equiv_refl #g #v
                          (d:RT.tot_typing g v tm_slprop)
  : GTot (pf:R.term &
          RT.tot_typing g pf (stt_slprop_equiv v v))
  = admit()

let slprop_equiv_sym_type = 
  let var0 = 0 in
  let v0 = mk_name var0 in
  let var1 = 1 in
  let v1 = mk_name var1 in
  mk_arrow 
    (tm_slprop, R.Q_Implicit)
    (RT.close_term
      (mk_arrow
        (tm_slprop, R.Q_Implicit)
        (RT.close_term 
          (mk_arrow
             (stt_slprop_equiv v0 v1, R.Q_Explicit)
             (stt_slprop_equiv v0 v1)) var1))
        var0)
            
let inst_slprop_equiv_sym #g #v0 #v1
  (d0:RT.tot_typing g v0 tm_slprop)
  (d1:RT.tot_typing g v1 tm_slprop)
  (#pf:_)
  (deq:RT.tot_typing g pf (stt_slprop_equiv v0 v1))
  : GTot (pf:R.term &
          RT.tot_typing g pf (stt_slprop_equiv v1 v0))
  = admit()

let inst_slprop_equiv_trans #g #v0 #v1 #v2
                         (d0:RT.tot_typing g v0 tm_slprop)
                         (d1:RT.tot_typing g v1 tm_slprop)
                         (d2:RT.tot_typing g v2 tm_slprop)
                         (#pf01:_)
                         (d01:RT.tot_typing g pf01 (stt_slprop_equiv v0 v1))
                         (#pf12:_)                         
                         (d12:RT.tot_typing g pf12 (stt_slprop_equiv v1 v2))
  : GTot (pf:R.term &
          RT.tot_typing g pf (stt_slprop_equiv v0 v2))
  = admit()


let inst_slprop_equiv_cong #g #v0 #v1 #v0' #v1'
                         (d0:RT.tot_typing g v0 tm_slprop)
                         (d1:RT.tot_typing g v1 tm_slprop)
                         (d0':RT.tot_typing g v0' tm_slprop)
                         (d1':RT.tot_typing g v1' tm_slprop)
                         (#pf0:_)
                         (eq0:RT.tot_typing g pf0 (stt_slprop_equiv v0 v0'))
                         (#pf1:_)                         
                         (eq1:RT.tot_typing g pf1 (stt_slprop_equiv v1 v1'))
  : GTot (pf:R.term &
          RT.tot_typing g pf (stt_slprop_equiv (mk_star v0 v1) (mk_star v0' v1')))
  = admit()


let inst_slprop_equiv_unit #g #v
                         (d:RT.tot_typing g v tm_slprop)
  : GTot (pf:R.term &
          RT.tot_typing g pf (stt_slprop_equiv (mk_star tm_emp v) v))
  = admit()


let inst_slprop_equiv_comm #g #v0 #v1
                         (d0:RT.tot_typing g v0 tm_slprop)
                         (d1:RT.tot_typing g v1 tm_slprop)
  : GTot (pf:R.term &
          RT.tot_typing g pf (stt_slprop_equiv (mk_star v0 v1) (mk_star v1 v0)))
  = admit()


let inst_slprop_equiv_assoc #g #v0 #v1 #v2
                         (d0:RT.tot_typing g v0 tm_slprop)
                         (d1:RT.tot_typing g v1 tm_slprop)
                         (d2:RT.tot_typing g v2 tm_slprop)
  : GTot (pf:R.term &
          RT.tot_typing g pf (stt_slprop_equiv (mk_star v0 (mk_star v1 v2)) (mk_star (mk_star v0 v1) v2)))
  = admit()


let slprop_tm = R.pack_ln (R.Tv_FVar  (R.pack_fv slprop_lid))

let slprop_equiv_ext_type : R.term =
  let open R in
  let v_typ = pack_ln (Tv_FVar  (pack_fv slprop_lid)) in
  let mk_bv index = pack_ln (Tv_BVar (pack_bv {
    ppname = RT.pp_name_default;
    index = index;
    sort = Sealed.seal tun;
  })) in

  mk_arrow
    (slprop_tm, Q_Explicit)
    (
     mk_arrow
       (slprop_tm, Q_Explicit)
       (
        mk_arrow
          (slprop_eq_tm (mk_bv 1) (mk_bv 0), Q_Explicit)
          (
           stt_slprop_equiv (mk_bv 2) (mk_bv 1)
          )
       )
    )

let inst_slprop_equiv_ext_aux #g #v0 #v1
  (equiv:RT.equiv g v0 v1)
  : GTot (RT.equiv g (stt_slprop_equiv v0 v0) (stt_slprop_equiv v0 v1)) =

  let ctxt = RT.Ctxt_app_arg
    (R.pack_ln (R.Tv_App stt_slprop_equiv_tm (v0, R.Q_Explicit)))
    R.Q_Explicit
    RT.Ctxt_hole in

  RT.Rel_ctxt _ _ _ ctxt equiv

let inst_slprop_equiv_ext #g #v0 #v1
  (d0:RT.tot_typing g v0 slprop_tm)
  (d1:RT.tot_typing g v1 slprop_tm)
  (token:RT.equiv g v0 v1)
  : GTot (pf:R.term &
          RT.tot_typing g pf (stt_slprop_equiv v0 v1)) =

  let (| pf, typing |)
    : (pf:R.term &
       RT.tot_typing g pf (stt_slprop_equiv v0 v0)) =
    inst_slprop_equiv_refl d0 in

  let d_st_equiv
    : RT.equiv g (stt_slprop_equiv v0 v0) (stt_slprop_equiv v0 v1) =
    inst_slprop_equiv_ext_aux token in

  let sub_typing
    : RT.sub_typing g (stt_slprop_equiv v0 v0) (stt_slprop_equiv v0 v1)
    = RT.Rel_equiv _ _ _ _ d_st_equiv in

  let pf_typing
    : RT.tot_typing g pf (stt_slprop_equiv v0 v1) =
    RT.T_Sub _ _ _ _ typing
      (RT.Relc_typ _ _ _ _ _ sub_typing) in

  (| pf, pf_typing |)
    
#push-options "--z3rlimit_factor 4"
let rec slprop_equiv_soundness (#g:stt_env) (#v0 #v1:term) 
                              (d:tot_typing g v0 tm_slprop)
                              (eq:slprop_equiv g v0 v1)
  : GTot (pf:R.term &
          RT.tot_typing (elab_env g)
                        pf
                        (stt_slprop_equiv v0 v1))
         (decreases eq)
  = match eq with
    | VE_Refl _ _ ->
      let d = tot_typing_soundness d in
      inst_slprop_equiv_refl d
    
    | VE_Sym g _v1 _v0 eq' ->
      let fwd, _ = slprop_equiv_typing eq in
      let d' = fwd d in
      let (| pf, dd |) = slprop_equiv_soundness d' eq' in
      inst_slprop_equiv_sym (tot_typing_soundness d')
                           (tot_typing_soundness d)
                           dd

    | VE_Trans _ _ v _ eq_0v eq_v1 ->
      let dv = fst (slprop_equiv_typing eq_0v) d in
      let d1 = fst (slprop_equiv_typing eq_v1) dv in
      let (| pf_0v, eq_0v |) = slprop_equiv_soundness d eq_0v in
      let (| pf_v1, eq_v1 |) = slprop_equiv_soundness dv eq_v1 in
      inst_slprop_equiv_trans 
        (tot_typing_soundness d)
        (tot_typing_soundness dv)        
        (tot_typing_soundness d1)
        eq_0v
        eq_v1

    | VE_Ctxt _ t0 t1 t0' t1' eq0 eq1 ->
      let t0_typing, t1_typing = star_typing_inversion d  in
      let t0'_typing = fst (slprop_equiv_typing eq0) t0_typing in
      let t1'_typing = fst (slprop_equiv_typing eq1) t1_typing in      
      let (| pf0, dd0 |) = slprop_equiv_soundness t0_typing eq0 in
      let (| pf1, dd1 |) = slprop_equiv_soundness t1_typing eq1 in      
      inst_slprop_equiv_cong (tot_typing_soundness t0_typing)
                            (tot_typing_soundness t1_typing)
                            (tot_typing_soundness t0'_typing)
                            (tot_typing_soundness t1'_typing)
                            dd0 dd1

    | VE_Unit _ _v1 ->
      let v1_typing = fst (slprop_equiv_typing eq) d in
      inst_slprop_equiv_unit (tot_typing_soundness v1_typing)

    | VE_Comm _ t0 t1 ->
      let t0_typing, t1_typing = star_typing_inversion #_ #t0 #t1 d  in
      inst_slprop_equiv_comm (tot_typing_soundness t0_typing)
                            (tot_typing_soundness t1_typing)

    | VE_Assoc _ t0 t1 t2 ->
      let t0_typing, t12_typing = star_typing_inversion #_ #t0 #(tm_star t1 t2) d  in
      let t1_typing, t2_typing =  star_typing_inversion #_ #t1 #t2 t12_typing in
      inst_slprop_equiv_assoc (tot_typing_soundness t0_typing)
                             (tot_typing_soundness t1_typing)
                             (tot_typing_soundness t2_typing)

    | VE_Ext _ t0 t1 token ->
      let t0_typing, t1_typing = slprop_eq_typing_inversion _ t0 t1 token in
      inst_slprop_equiv_ext (tot_typing_soundness t0_typing)
                           (tot_typing_soundness t1_typing)
                           token

    | VE_Fa _ _ _ _ _ _ _ ->
      (* see Pulse.Lib.Core.slprop_equiv_forall *)
      admit()
#pop-options

let stt_slprop_equiv_is_prop (#g:R.env) (#v0 #v1:R.term)
                            (d0: RT.tot_typing g v0 tm_slprop)
                            (d1: RT.tot_typing g v1 tm_slprop)
   : GTot (RT.tot_typing g (stt_slprop_equiv v0 v1) RT.tm_prop)
   = admit()
   
let slprop_equiv_unit_soundness (#g:stt_env) (#v0 #v1:term) 
                               (d0:tot_typing g v0 tm_slprop)
                               (eq:slprop_equiv g v0 v1)
  : GTot (RT.tot_typing (elab_env g) (`()) (stt_slprop_equiv v0 v1))
  = let (| pf, s |) = slprop_equiv_soundness d0 eq in
    let d1 = fst (slprop_equiv_typing eq) d0 in
    let s_prop = stt_slprop_equiv_is_prop (tot_typing_soundness d0) (tot_typing_soundness d1) in
    RT.T_PropIrrelevance _ _ _ _ _ s s_prop
