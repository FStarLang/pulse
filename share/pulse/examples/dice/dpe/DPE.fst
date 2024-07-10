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

module DPE
open Pulse.Lib.Pervasives
open DPETypes
open HACL
open EngineTypes
open EngineCore
open L0Types
open L0Core

module G = FStar.Ghost
module PCM = FStar.PCM
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module PP = PulseCore.Preorder
module PM = Pulse.Lib.PCMMap
module FP = Pulse.Lib.PCM.FractionalPreorder
module M = Pulse.Lib.MutexToken
module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module HT = Pulse.Lib.HashTable
module PHT = Pulse.Lib.HashTable.Spec

open PulseCore.Preorder
open Pulse.Lib.OnRange
open Pulse.Lib.HashTable.Type
open Pulse.Lib.HashTable
open Pulse.Lib.MutexToken

assume
val run_stt (#a:Type) (#post:a -> slprop) (f:stt a emp post) : a

let sid_hash (s:sid_t) : SZ.t = SZ.uint16_to_sizet s  //fstar_code

[@@ Rust_const_fn]
```pulse
fn initialize_global_state ()  //pulse_spec
  requires emp  //pulse_spec
  returns b:(r:gref & mutex (dpe_inv r))  //pulse_spec
  ensures emp  //pulse_spec
{
  let r = ghost_alloc #_ #pcm all_sids_unused;  //pulse_proof
  with _v. rewrite (ghost_pcm_pts_to r (G.reveal (G.hide _v))) as  //pulse_proof
                   (ghost_pcm_pts_to r _v);  //pulse_proof
  fold (dpe_inv r None);  //pulse_proof
  let m = new_mutex (dpe_inv r) None;  //pulse_code
  ((| r, m |) <: (r:gref & mutex (dpe_inv r)))  //pulse_code
}
```

let gst : (r:gref & mutex (dpe_inv r)) = run_stt (initialize_global_state ())  //pulse_code

let trace_ref = dfst gst  //pulse_proof

//
// DPE API implementation
//

//
// A wrapper over ghost_gather
//
// ghost_gather takes erased arguments,
//   sometimes that leads to unnecessary reveals and hides
//
// This version works much better
//
```pulse
ghost
fn gather_ (r:gref)  //pulse_spec
  (v0 v1:pcm_t)  //pulse_spec
  requires ghost_pcm_pts_to r v0 **  //pulse_spec
           ghost_pcm_pts_to r v1  //pulse_spec
  returns _:squash (PCM.composable pcm v0 v1)  //pulse_spec
  ensures ghost_pcm_pts_to r (PCM.op pcm v0 v1)  //pulse_spec
{
  ghost_gather r v0 v1;  //pulse_proof
  with _v. rewrite (ghost_pcm_pts_to r _v) as  //pulse_proof
                   (ghost_pcm_pts_to r (PCM.op pcm v0 v1))  //pulse_proof
}
```

//
// A gather to work with map pcm
//
// The caller provides v and the proof that
//   v is `Map.equal` to op of v0 and v1
//
// 
```pulse
ghost
fn gather_v (r:gref)  //pulse_spec
  (v0 v1 v:pcm_t)  //pulse_spec
  requires ghost_pcm_pts_to r v0 **  //pulse_spec
           ghost_pcm_pts_to r v1 **  //pulse_spec
           pure (PCM.composable pcm v0 v1 ==> Map.equal (PCM.op pcm v0 v1) v)  //pulse_spec
  ensures ghost_pcm_pts_to r v **  //pulse_spec
          pure (PCM.composable pcm v0 v1)  //pulse_spec
{
  ghost_gather r v0 v1;  //pulse_proof
  with _v. rewrite (ghost_pcm_pts_to r _v) as  //pulse_proof
                   (ghost_pcm_pts_to r v)  //pulse_proof
}
```

//
// Corresponding share, with a Map.equal proof in the precondition
//
```pulse
ghost
fn share_ (r:gref)  //pulse_spec
  (v v0 v1:pcm_t)  //pulse_spec
  requires ghost_pcm_pts_to r v **  //pulse_spec
           pure (PCM.composable pcm v0 v1 /\  //pulse_spec
                 Map.equal (PCM.op pcm v0 v1) v)  //pulse_spec
  ensures ghost_pcm_pts_to r v0 **  //pulse_spec
          ghost_pcm_pts_to r v1  //pulse_spec
{
  rewrite (ghost_pcm_pts_to r v) as  //pulse_proof
          (ghost_pcm_pts_to r (PCM.op pcm v0 v1));  //pulse_proof
  ghost_share r v0 v1;  //pulse_proof
}
```

noextract
let full (t0:trace) = Some #perm 1.0R, t0  //pulse_proof

noextract
let half (t0:trace) = Some #perm 0.5R, t0  //pulse_proof

```pulse
ghost
fn upd_sid_pts_to  //pulse_spec
  (r:gref) (sid:sid_t)  //pulse_spec
  (#t0 #t1:trace)  //pulse_spec
  (s:g_session_state { valid_transition t0 s })  //pulse_spec

  requires sid_pts_to r sid t0 **  //pulse_spec
           sid_pts_to r sid t1  //pulse_spec
  ensures sid_pts_to r sid (next_trace t0 s) **  //pulse_spec
          sid_pts_to r sid (next_trace t0 s) **  //pulse_spec
          pure (t0 == t1)
{
  unfold (sid_pts_to r sid t0);  //pulse_proof
  unfold (sid_pts_to r sid t1);  //pulse_proof

  gather_v r (singleton sid 0.5R t0)  //pulse_proof
             (singleton sid 0.5R t1)  //pulse_proof
             (singleton sid 1.0R t0);  //pulse_proof

  let fp : PCM.frame_preserving_upd trace_pcm (full t0) (full (next_trace t0 s)) =  //pulse_proof
    mk_frame_preserving_upd t0 s;  //pulse_proof

  assert (pure (Map.equal (Map.upd (singleton sid 1.0R t0) sid (full (next_trace t0 s)))  //pulse_proof
                          (singleton sid 1.0R (next_trace t0 s))));  //pulse_proof

  let fp : PCM.frame_preserving_upd pcm (singleton sid 1.0R t0) (singleton sid 1.0R (next_trace t0 s)) =  //pulse_proof
    PM.lift_frame_preserving_upd #_ #_ #trace_pcm  //pulse_proof
      (full t0)  //pulse_proof
      (full (next_trace t0 s))  //pulse_proof
      fp  //pulse_proof
      (singleton sid 1.0R t0) sid;  //pulse_proof

  ghost_write r  //pulse_proof
    (singleton sid 1.0R t0)  //pulse_proof
    (singleton sid 1.0R (next_trace t0 s))  //pulse_proof
    fp;  //pulse_proof

  share_ r (singleton sid 1.0R (next_trace t0 s))  //pulse_proof
           (singleton sid 0.5R (next_trace t0 s))  //pulse_proof
           (singleton sid 0.5R (next_trace t0 s));  //pulse_proof

  fold (sid_pts_to r sid (next_trace t0 s));  //pulse_proof
  fold (sid_pts_to r sid (next_trace t0 s));  //pulse_proof
}
```

let safe_incr (i:U16.t)
  : r:option U16.t { Some? r ==> (U16.v (Some?.v r) == U16.v i + 1) } =

  let open FStar.UInt16 in  //fstar_code
  if i <^ 0xffffus  //fstar_code
  then Some (i +^ 1us)  //fstar_code
  else None  //fstar_code

noextract
let session_table_eq_on_range  //pulse_spec
  (pht0 pht1:pht_t)  //pulse_spec
  (i j:nat)  //pulse_spec
  : prop =  //pulse_spec
  forall (k:sid_t). i <= U16.v k && U16.v k < j ==> PHT.lookup pht0 k == PHT.lookup pht1 k  //pulse_spec

```pulse
ghost
fn frame_session_perm_at_sid  //pulse_spec
  (r:gref)  //pulse_spec
  (pht0 pht1:pht_t)  //pulse_spec
  (i j:nat)  //pulse_spec
  (_:squash (session_table_eq_on_range pht0 pht1 i j))  //pulse_spec
  (sid:(sid:nat { i <= sid /\ sid < j }))  //pulse_spec
  requires session_perm r pht0 sid  //pulse_spec
  ensures session_perm r pht1 sid  //pulse_spec
{
  if (UInt.fits sid 16) {  //pulse_proof
    let sid16 = U16.uint_to_t sid;  //pulse_proof
    rewrite (session_perm r pht0 sid) as  //pulse_proof
            (session_state_perm r pht0 sid16);  //pulse_proof
    unfold session_state_perm;  //pulse_proof
    fold (session_state_perm r pht1 sid16);  //pulse_proof
    rewrite (session_state_perm r pht1 sid16) as  //pulse_proof
            (session_perm r pht1 sid)  //pulse_proof
  } else {  //pulse_proof
    rewrite (session_perm r pht0 sid) as  //pulse_proof
            (session_perm r pht1 sid)  //pulse_proof
  }
}
```

```pulse
ghost
fn frame_session_perm_on_range  //pulse_spec
  (r:gref)  //pulse_spec
  (pht0 pht1:pht_t)  //pulse_spec
  (i j:nat)  //pulse_spec
  requires on_range (session_perm r pht0) i j **  //pulse_spec
           pure (session_table_eq_on_range pht0 pht1 i j)  //pulse_spec
  ensures on_range (session_perm r pht1) i j  //pulse_spec
{
  Pulse.Lib.OnRange.on_range_weaken  //pulse_proof
    (session_perm r pht0)  //pulse_proof
    (session_perm r pht1)  //pulse_proof
    i j  //pulse_proof
    (frame_session_perm_at_sid r pht0 pht1 i j ())  //pulse_proof
}
```

let emp_to_start_valid () : Lemma (valid_transition emp_trace G_SessionStart) = ()  //fstar_proof

#push-options "--fuel 0 --ifuel 2 --split_queries no --z3rlimit_factor 2"
```pulse
fn __open_session (s:st)  //pulse_spec
  requires dpe_inv trace_ref (Some s)  //pulse_spec
  returns b:(st & option sid_t)  //pulse_spec
  ensures dpe_inv trace_ref (Some (fst b)) **  //pulse_spec
          open_session_client_perm (snd b)  //pulse_spec
{
  unfold (dpe_inv trace_ref (Some s));  //pulse_proof

  let ctr = s.st_ctr;  //pulse_code
  let tbl = s.st_tbl;  //pulse_code

  rewrite each  //pulse_proof
    s.st_ctr as ctr,  //pulse_proof
    s.st_tbl as tbl;  //pulse_proof

  with pht. assert (models tbl pht);  //pulse_proof
  assert (on_range (session_perm trace_ref pht) 0 (U16.v ctr));  //pulse_proof
  assert (ghost_pcm_pts_to trace_ref (sids_above_unused ctr));  //pulse_proof

  let copt = safe_incr ctr;  //pulse_code

  match copt {  //pulse_code
    None -> {  //pulse_code
      let s = { st_ctr = ctr; st_tbl = tbl };  //pulse_code
      let ret = s, None #sid_t;  //pulse_code
      rewrite each  //pulse_proof
        ctr as (fst ret).st_ctr,  //pulse_proof
        tbl as (fst ret).st_tbl;  //pulse_proof
      fold (dpe_inv trace_ref (Some (fst ret)));  //pulse_proof
      rewrite emp as (open_session_client_perm (snd ret));  //pulse_proof
      ret  //pulse_code
    }

    Some ctr1 -> {  //pulse_code
      let ret = HT.insert_if_not_full tbl ctr SessionStart;  //pulse_code
      let tbl1 = fst ret;  //pulse_code
      let b = snd ret;  //pulse_code
      rewrite each fst ret as tbl1;  //pulse_proof
      with pht1. assert (models tbl1 pht1);  //pulse_proof
      if b {  //pulse_code
        share_ trace_ref (sids_above_unused ctr)  //pulse_proof
                         (sids_above_unused ctr1)  //pulse_proof
                         (singleton ctr 1.0R emp_trace);  //pulse_proof
        share_ trace_ref (singleton ctr 1.0R emp_trace)  //pulse_proof
                         (singleton ctr 0.5R emp_trace)  //pulse_proof
                         (singleton ctr 0.5R emp_trace);  //pulse_proof
        fold (sid_pts_to trace_ref ctr emp_trace);  //pulse_proof
        fold (sid_pts_to trace_ref ctr emp_trace);  //pulse_proof
        emp_to_start_valid ();  //pulse_proof
        upd_sid_pts_to trace_ref ctr #emp_trace #emp_trace G_SessionStart;  //pulse_proof
        rewrite emp as (session_state_related SessionStart G_SessionStart);  //pulse_proof
        fold (session_state_perm trace_ref pht1 ctr);  //pulse_proof
        rewrite (session_state_perm trace_ref pht1 ctr) as  //pulse_proof
                (session_perm trace_ref pht1 (U16.v ctr));  //pulse_proof
        frame_session_perm_on_range trace_ref pht pht1 0 (U16.v ctr);  //pulse_proof
        on_range_snoc () #(session_perm trace_ref pht1) #0 #(U16.v ctr);  //pulse_proof
        let s = { st_ctr = ctr1; st_tbl = tbl1 };  //pulse_code
        let ret = s, Some ctr;  //pulse_code
        rewrite each  //pulse_proof
          ctr1 as (fst ret).st_ctr,  //pulse_proof
          tbl1 as (fst ret).st_tbl;  //pulse_proof
        fold (dpe_inv trace_ref (Some (fst ret)));  //pulse_proof
        fold (open_session_client_perm (Some ctr));  //pulse_proof
        ret  //pulse_code
      } else {  //pulse_code
        let s = { st_ctr = ctr; st_tbl = tbl1 };  //pulse_code
        let ret = s, None #sid_t;  //pulse_code
        rewrite each  //pulse_proof
          tbl1 as (fst ret).st_tbl,  //pulse_proof
          pht1 as pht,  //pulse_proof
          ctr as (fst ret).st_ctr;  //pulse_proof
        fold (dpe_inv trace_ref (Some (fst ret)));  //pulse_proof
        rewrite emp as (open_session_client_perm (snd ret));  //pulse_proof
        ret  //pulse_code
      }
    }
  }
}
```
#pop-options

```pulse
fn maybe_mk_session_tbl (sopt:option st)  //pulse_spec
  requires dpe_inv trace_ref sopt  //pulse_spec
  returns s:st  //pulse_spec
  ensures dpe_inv trace_ref (Some s)  //pulse_spec
{
  match sopt {  //pulse_code
    None -> {  //pulse_code
      let tbl = HT.alloc #sid_t #session_state sid_hash 256sz;  //pulse_code
      let s = {  //pulse_code
        st_ctr = 0us;  //pulse_code
        st_tbl = tbl;  //pulse_code
      };

      rewrite each tbl as s.st_tbl;  //pulse_proof

      unfold dpe_inv;  //pulse_proof
      assert (pure (Map.equal all_sids_unused (sids_above_unused s.st_ctr)));  //pulse_proof
      rewrite (ghost_pcm_pts_to trace_ref all_sids_unused) as  //pulse_proof
              (ghost_pcm_pts_to trace_ref (sids_above_unused s.st_ctr));  //pulse_proof

      with pht. assert (models s.st_tbl pht);  //pulse_proof
      on_range_empty (session_perm trace_ref pht) 0;  //pulse_proof
      rewrite (on_range (session_perm trace_ref pht) 0 0) as  //pulse_proof
              (on_range (session_perm trace_ref pht) 0 (U16.v s.st_ctr));  //pulse_proof
  
      fold (dpe_inv trace_ref (Some s));  //pulse_proof
      s  //pulse_code
    }
    Some s -> {  //pulse_code
      s  //pulse_code
    }
  }
}
```

```pulse
ghost
fn to_dpe_inv_trace_ref (#s:option st) ()  //pulse_spec
  requires dpe_inv (Mkdtuple2?._1 gst) s  //pulse_spec
  ensures dpe_inv trace_ref s  //pulse_spec
{
  rewrite (dpe_inv (Mkdtuple2?._1 gst) s) as  //pulse_proof
          (dpe_inv trace_ref s)  //pulse_proof
}
```

```pulse
ghost
fn from_dpe_inv_trace_ref (#s:option st) ()  //pulse_spec
  requires dpe_inv trace_ref s  //pulse_spec
  ensures dpe_inv (Mkdtuple2?._1 gst) s  //pulse_spec
{
  rewrite (dpe_inv trace_ref s) as  //pulse_proof
          (dpe_inv (Mkdtuple2?._1 gst) s)  //pulse_proof
}
```

```pulse
fn open_session ()  //pulse_spec
  requires emp  //pulse_spec
  returns r:(option sid_t)  //pulse_spec
  ensures open_session_client_perm r  //pulse_spec
{
  let mg = M.lock (dsnd gst);  //pulse_code
  to_dpe_inv_trace_ref ();  //pulse_proof

  let sopt = M.replace #(option st) mg None;  //pulse_code

  let s = maybe_mk_session_tbl sopt;  //pulse_code
  let ret = __open_session s;  //pulse_code
  let s = fst ret;  //pulse_code
  let sid_opt = snd ret;  //pulse_code
  rewrite each  //pulse_proof
    fst ret as s,  //pulse_proof
    snd ret as sid_opt;  //pulse_proof
  mg := Some s;  //pulse_code

  from_dpe_inv_trace_ref ();  //pulse_proof
  M.unlock (dsnd gst) mg;  //pulse_code
  
  sid_opt  //pulse_code
}
```

[@@allow_ambiguous]
```pulse
ghost
fn gather_sid_pts_to (sid:sid_t) (#t0 #t1:trace)  //pulse_spec
  requires sid_pts_to trace_ref sid t0 **  //pulse_spec
           sid_pts_to trace_ref sid t1  //pulse_spec
  ensures ghost_pcm_pts_to trace_ref (singleton sid 1.0R t0) **  //pulse_spec
          pure (t0 == t1)  //pulse_spec
{
  unfold (sid_pts_to trace_ref sid t0);  //pulse_proof
  unfold (sid_pts_to trace_ref sid t1);  //pulse_proof
  gather_ trace_ref (singleton sid 0.5R t0) (singleton sid 0.5R t1);  //pulse_proof
  with v. assert (ghost_pcm_pts_to trace_ref v);  //pulse_proof
  assert (pure (Map.equal v (singleton sid 1.0R t0)));  //pulse_proof
  rewrite (ghost_pcm_pts_to trace_ref v) as  //pulse_proof
          (ghost_pcm_pts_to trace_ref (singleton sid 1.0R t0))  //pulse_proof
}
```

```pulse
ghost
fn share_sid_pts_to (sid:sid_t) (#t:trace)  //pulse_spec
  requires ghost_pcm_pts_to trace_ref (singleton sid 1.0R t)  //pulse_spec
  ensures sid_pts_to trace_ref sid t **  //pulse_spec
          sid_pts_to trace_ref sid t  //pulse_spec
{
  share_ trace_ref (singleton sid 1.0R t)  //pulse_proof
                   (singleton sid 0.5R t)  //pulse_proof
                   (singleton sid 0.5R t);  //pulse_proof
  fold sid_pts_to;  //pulse_proof
  fold sid_pts_to  //pulse_proof
}
```

```pulse
ghost
fn upd_singleton  //pulse_spec
  (sid:sid_t)  //pulse_spec
  (#t:trace)  //pulse_spec
  (s:g_session_state { valid_transition t s })  //pulse_spec
  requires ghost_pcm_pts_to trace_ref (singleton sid 1.0R t)  //pulse_spec
  ensures ghost_pcm_pts_to trace_ref (singleton sid 1.0R (next_trace t s))  //pulse_spec
{
  let fp : PCM.frame_preserving_upd trace_pcm (full t) (full (next_trace t s)) =  //pulse_proof
    mk_frame_preserving_upd t s;  //pulse_proof

  assert (pure (Map.equal (Map.upd (singleton sid 1.0R t) sid (full (next_trace t s)))  //pulse_proof
                          (singleton sid 1.0R (next_trace t s))));  //pulse_proof

  let fp : PCM.frame_preserving_upd pcm (singleton sid 1.0R t) (singleton sid 1.0R (next_trace t s)) =  //pulse_proof
    PM.lift_frame_preserving_upd #_ #_ #trace_pcm  //pulse_proof
      (full t)  //pulse_proof
      (full (next_trace t s))  //pulse_proof
      fp  //pulse_proof
      (singleton sid 1.0R t) sid;  //pulse_proof

  ghost_write trace_ref  //pulse_proof
    (singleton sid 1.0R t)  //pulse_proof
    (singleton sid 1.0R (next_trace t s))  //pulse_proof
    fp;  //pulse_proof
}
```

#push-options "--fuel 0 --ifuel 2 --split_queries no --z3rlimit_factor 2"
```pulse
fn replace_session  //pulse_spec
  (sid:sid_t)  //pulse_spec
  (t:G.erased trace)  //pulse_spec
  (sst:session_state)  //pulse_spec
  (gsst:g_session_state { valid_transition t gsst})  //pulse_spec

  requires sid_pts_to trace_ref sid t **  //pulse_spec
           session_state_related sst gsst  //pulse_spec

  returns r:session_state  //pulse_spec

  ensures session_state_related r (current_state t) **  //pulse_spec
          sid_pts_to trace_ref sid (next_trace t gsst)  //pulse_spec
{
  let mg = M.lock (dsnd gst);  //pulse_code
  to_dpe_inv_trace_ref ();  //pulse_proof

  let sopt = M.replace mg None;  //pulse_code
  match sopt {  //pulse_code
    None -> {  //pulse_code
      unfold (dpe_inv trace_ref None);  //pulse_proof
      unfold sid_pts_to;  //pulse_proof
      gather_ trace_ref all_sids_unused (singleton sid 0.5R t);  //pulse_proof
      unreachable ()  //pulse_proof
    }
    Some s -> {  //pulse_code
      unfold (dpe_inv trace_ref (Some s));  //pulse_proof
      let ctr = s.st_ctr;  //pulse_code
      let tbl = s.st_tbl;  //pulse_code
      rewrite each  //pulse_proof
        s.st_ctr as ctr,  //pulse_proof
        s.st_tbl as tbl;  //pulse_proof
      with pht0. assert (models tbl pht0);  //pulse_proof
      assert (on_range (session_perm trace_ref pht0) 0 (U16.v ctr));  //pulse_proof
      if U16.lt sid ctr {  //pulse_code
        on_range_get (U16.v sid) #(session_perm trace_ref pht0) #0 #(U16.v ctr);  //pulse_proof
        rewrite (session_perm trace_ref pht0 (U16.v sid)) as  //pulse_proof
                (session_state_perm trace_ref pht0 sid);  //pulse_proof
        unfold session_state_perm;  //pulse_proof
        gather_sid_pts_to sid;  //pulse_proof
        with t1. assert (ghost_pcm_pts_to trace_ref (singleton sid 1.0R t1));  //pulse_proof
        assert (pure (t1 == t));  //pulse_proof
        let ret = HT.lookup tbl sid;  //pulse_code
        let tbl = tfst ret;  //pulse_code
        let b = tsnd ret;  //pulse_code
        let idx = tthd ret;  //pulse_code
        rewrite each  //pulse_proof
          tfst ret as tbl,  //pulse_proof
          tsnd ret as b,  //pulse_proof
          tthd ret as idx;  //pulse_proof
        with pht. assert (models tbl pht);  //pulse_proof
        if b {  //pulse_code
          match idx {  //pulse_code
            Some idx -> {  //pulse_code
              let ret = HT.replace #_ #_ #pht tbl idx sid sst ();  //pulse_code
              let tbl = fst ret;  //pulse_code
              let st = snd ret;  //pulse_code
              rewrite each  //pulse_proof
                fst ret as tbl,  //pulse_proof
                snd ret as st;  //pulse_proof
              assert (session_state_related sst gsst);  //pulse_proof
              with sst' gsst'. assert (  //pulse_proof
                session_state_related sst' gsst' **  //pulse_proof
                session_state_related sst gsst  //pulse_proof
              );
              rewrite (session_state_related sst' gsst')  //pulse_proof
                   as (session_state_related st (current_state t1));  //pulse_proof
              with pht. assert (models tbl pht);  //pulse_proof
              upd_singleton sid #t1 gsst;  //pulse_proof
              share_sid_pts_to sid;  //pulse_proof
              rewrite (session_state_related sst gsst) as  //pulse_proof
                      (session_state_related sst (current_state (next_trace t1 gsst)));  //pulse_proof
              fold (session_state_perm trace_ref pht sid);  //pulse_proof
              rewrite (session_state_perm trace_ref pht sid) as  //pulse_proof
                      (session_perm trace_ref pht (U16.v sid));  //pulse_proof
              frame_session_perm_on_range trace_ref pht0 pht 0 (U16.v sid);  //pulse_proof
              frame_session_perm_on_range trace_ref pht0 pht (U16.v sid + 1) (U16.v ctr);  //pulse_proof
              on_range_put 0 (U16.v sid) (U16.v ctr) #(session_perm trace_ref pht);  //pulse_proof
              let s = { st_ctr = ctr; st_tbl = tbl };  //pulse_code
              rewrite each  //pulse_proof
                ctr as s.st_ctr,  //pulse_proof
                tbl as s.st_tbl;  //pulse_proof
              fold (dpe_inv trace_ref (Some s));  //pulse_proof
              mg := Some s;  //pulse_code

              from_dpe_inv_trace_ref ();  //pulse_proof
              M.unlock (dsnd gst) mg;  //pulse_code
              
              st  //pulse_code
            }
            None -> {  //pulse_code
              unreachable ()  //pulse_proof
            }
          }
        } else {
          //
          // AR: TODO: would be nice if we can prove this can't happen
          //           i.e. if sid is in pht, then its lookup should succeed
          assume_ (pure False);
          unreachable ()
        }
      } else {
        unfold sid_pts_to;  //pulse_proof
        gather_ trace_ref (sids_above_unused ctr) (singleton sid 0.5R t);  //pulse_proof
        unreachable ()  //pulse_proof
      }
    }
  }
}
```
#pop-options

```pulse
fn init_engine_ctxt  //pulse_spec
  (uds:A.array U8.t { A.length uds == SZ.v uds_len })  //pulse_spec
  (#p:perm)  //pulse_spec
  (#uds_bytes:Ghost.erased (Seq.seq U8.t))  //pulse_spec
  requires A.pts_to uds #p uds_bytes  //pulse_spec
  returns ctxt:context_t  //pulse_spec
  ensures A.pts_to uds #p uds_bytes **  //pulse_spec
          context_perm ctxt (Engine_context_repr uds_bytes)  //pulse_spec
{ 
  let uds_buf = V.alloc 0uy uds_len;  //pulse_code
  A.pts_to_len uds;  //pulse_proof
  V.pts_to_len uds_buf;  //pulse_proof

  V.to_array_pts_to uds_buf;  //pulse_proof
  A.memcpy uds_len uds (V.vec_to_array uds_buf);  //pulse_code
  V.to_vec_pts_to uds_buf;  //pulse_proof

  let engine_context = mk_engine_context_t uds_buf;  //pulse_code

  rewrite each uds_buf as (engine_context.uds);  //pulse_proof
  fold (engine_context_perm engine_context uds_bytes);  //pulse_proof

  let ctxt = mk_context_t_engine engine_context;  //pulse_code
  rewrite (engine_context_perm engine_context uds_bytes)   //pulse_proof
       as (context_perm ctxt (Engine_context_repr uds_bytes));  //pulse_proof
  ctxt  //pulse_code
}
```

let session_state_tag_related (s:session_state) (gs:g_session_state) : GTot bool =  //pulse_spec
  match s, gs with  //pulse_spec
  | SessionStart, G_SessionStart  //pulse_spec
  | InUse, G_InUse _  //pulse_spec
  | SessionClosed, G_SessionClosed _  //pulse_spec
  | SessionError, G_SessionError _  //pulse_spec
  | Available _, G_Available _ -> true  //pulse_spec
  | _ -> false  //pulse_spec


```pulse
ghost
fn intro_session_state_tag_related (s:session_state) (gs:g_session_state)  //pulse_spec
  requires session_state_related s gs  //pulse_spec
  ensures session_state_related s gs **  //pulse_spec
          pure (session_state_tag_related s gs)  //pulse_spec
{
  let b = session_state_tag_related s gs;  //pulse_proof
  if b {  //pulse_proof
    ()  //pulse_proof
  } else {  //pulse_proof
    rewrite (session_state_related s gs) as  //pulse_proof
            (pure False);  //pulse_proof
    unreachable ()  //pulse_proof
  }
}
```

#push-options "--fuel 2 --ifuel 2 --split_queries no"
```pulse
fn initialize_context (sid:sid_t)  //pulse_spec
  (t:G.erased trace { trace_valid_for_initialize_context t })  //pulse_spec
  (#p:perm) (#uds_bytes:Ghost.erased (Seq.seq U8.t))  //pulse_spec
  (uds:A.larray U8.t (SZ.v uds_len))   //pulse_spec
                       
  requires A.pts_to uds #p uds_bytes **  //pulse_spec
           sid_pts_to trace_ref sid t  //pulse_spec

  ensures A.pts_to uds #p uds_bytes **  //pulse_spec
          initialize_context_client_perm sid uds_bytes  //pulse_spec
{
  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));  //pulse_proof
  let s = replace_session sid t InUse (G_InUse (current_state t));  //pulse_code
  with t1. assert (sid_pts_to trace_ref sid t1);  //pulse_proof

  match s {  //pulse_code
    SessionStart -> {  //pulse_code
      rewrite (session_state_related s (current_state t)) as emp;  //pulse_proof
      let context = init_engine_ctxt uds;  //pulse_code
      let s = Available { context };  //pulse_code
      rewrite (context_perm context (Engine_context_repr uds_bytes)) as  //pulse_proof
              (session_state_related s (G_Available (Engine_context_repr uds_bytes)));  //pulse_proof
      let s = replace_session sid t1 s (G_Available (Engine_context_repr uds_bytes));  //pulse_code
      intro_session_state_tag_related s (current_state t1);  //pulse_proof
      with _x _y. rewrite (session_state_related _x _y) as emp;  //pulse_proof
      fold (initialize_context_client_perm sid uds_bytes)  //pulse_proof
    }
    InUse -> {  //pulse_code
      rewrite (session_state_related s (current_state t)) as  //pulse_proof
              (pure False);  //pulse_proof
      unreachable ()  //pulse_proof
    }
    SessionClosed -> {  //pulse_code
      rewrite (session_state_related s (current_state t)) as  //pulse_proof
              (pure False);  //pulse_proof
      unreachable ()  //pulse_proof
    }
    SessionError -> {  //pulse_code
      rewrite (session_state_related s (current_state t)) as  //pulse_proof
              (pure False);  //pulse_proof
      unreachable ()  //pulse_proof
    }
    Available _ -> {  //pulse_code
      rewrite (session_state_related s (current_state t)) as  //pulse_proof
              (pure False);  //pulse_proof
      unreachable ()  //pulse_proof
    }
  }
}
```
#pop-options

```pulse
fn init_l0_ctxt  //pulse_spec
  (cdi:A.array U8.t { A.length cdi == SZ.v dice_digest_len })  //pulse_spec
  (#engine_repr:erased engine_record_repr)  //pulse_spec
  (#s:erased (Seq.seq U8.t))  //pulse_spec
  (#uds_bytes:erased (Seq.seq U8.t))  //pulse_spec
  (_:squash (cdi_functional_correctness s uds_bytes engine_repr /\  //pulse_spec
             l0_is_authentic engine_repr))  //pulse_spec
  requires A.pts_to cdi s  //pulse_spec
  returns ctxt:l0_context_t  //pulse_spec
  ensures  //pulse_spec
    A.pts_to cdi s **  //pulse_spec
    l0_context_perm ctxt (mk_l0_context_repr_t uds_bytes s engine_repr)  //pulse_spec
{
  let cdi_buf = V.alloc 0uy dice_digest_len;  //pulse_code
  A.pts_to_len cdi;  //pulse_proof
  V.pts_to_len cdi_buf;  //pulse_proof

  V.to_array_pts_to cdi_buf;  //pulse_proof
  A.memcpy dice_digest_len cdi (V.vec_to_array cdi_buf);  //pulse_code
  V.to_vec_pts_to cdi_buf;  //pulse_proof
  
  let l0_context = mk_l0_context_t cdi_buf;  //pulse_code
  let l0_context_repr = hide (mk_l0_context_repr_t uds_bytes s engine_repr);  //pulse_proof
  rewrite each cdi_buf as (l0_context.cdi);  //pulse_proof
  fold (l0_context_perm l0_context l0_context_repr);  //pulse_proof
  l0_context  //pulse_code
}
```

```pulse
fn init_l1_ctxt  //pulse_spec
  (cdi:erased (Seq.seq U8.t))  //pulse_spec
  (deviceID_label_len:(n:erased U32.t { valid_hkdf_lbl_len n }))  //pulse_spec
  (aliasKey_label_len:(n:erased U32.t { valid_hkdf_lbl_len n }))  //pulse_spec
  (deviceIDCSR_ingredients:erased deviceIDCSR_ingredients_t)  //pulse_spec
  (aliasKeyCRT_ingredients:erased aliasKeyCRT_ingredients_t)  //pulse_spec
  (deviceID_pub:V.lvec U8.t 32)  //pulse_spec
  (aliasKey_priv:V.lvec U8.t 32)  //pulse_spec
  (aliasKey_pub:V.lvec U8.t 32)  //pulse_spec
  (deviceIDCSR_len:(n:U32.t { valid_deviceIDCSR_ingredients deviceIDCSR_ingredients n }))  //pulse_spec
  (deviceIDCSR:V.lvec U8.t (U32.v deviceIDCSR_len))  //pulse_spec
  (aliasKeyCRT_len:(n:U32.t { valid_aliasKeyCRT_ingredients aliasKeyCRT_ingredients n }))  //pulse_spec
  (aliasKeyCRT:V.lvec U8.t (U32.v aliasKeyCRT_len))  //pulse_spec
  (repr:erased l0_record_repr_t)  //pulse_spec
  (#deviceID_pub_repr #aliasKey_pub_repr #aliasKey_priv_repr  //pulse_spec
   #deviceIDCSR_repr #aliasKeyCRT_repr:erased (Seq.seq U8.t))  //pulse_spec
  (_:squash (l0_post  //pulse_spec
     cdi  //pulse_spec
     repr.fwid  //pulse_spec
     deviceID_label_len  //pulse_spec
     repr.deviceID_label  //pulse_spec
     aliasKey_label_len  //pulse_spec
     repr.aliasKey_label  //pulse_spec
     deviceIDCSR_ingredients  //pulse_spec
     aliasKeyCRT_ingredients  //pulse_spec
     deviceID_pub_repr  //pulse_spec
     aliasKey_pub_repr  //pulse_spec
     aliasKey_priv_repr  //pulse_spec
     deviceIDCSR_len  //pulse_spec
     deviceIDCSR_repr  //pulse_spec
     aliasKeyCRT_len  //pulse_spec
     aliasKeyCRT_repr))  //pulse_spec
  requires V.pts_to deviceID_pub deviceID_pub_repr **  //pulse_spec
           V.pts_to aliasKey_pub aliasKey_pub_repr **  //pulse_spec
           V.pts_to aliasKey_priv aliasKey_priv_repr **  //pulse_spec
           V.pts_to deviceIDCSR deviceIDCSR_repr **  //pulse_spec
           V.pts_to aliasKeyCRT aliasKeyCRT_repr **  //pulse_spec
           pure (V.is_full_vec deviceID_pub /\  //pulse_spec
                 V.is_full_vec aliasKey_pub /\  //pulse_spec
                 V.is_full_vec aliasKey_priv /\  //pulse_spec
                 V.is_full_vec deviceIDCSR /\  //pulse_spec
                  V.is_full_vec aliasKeyCRT)  //pulse_spec
  returns ctxt:l1_context_t  //pulse_spec
  ensures  //pulse_spec
    l1_context_perm ctxt (mk_l1_context_repr_t  //pulse_spec
      cdi deviceID_label_len aliasKey_label_len deviceIDCSR_ingredients aliasKeyCRT_ingredients  //pulse_spec
      deviceID_pub_repr aliasKey_pub_repr aliasKey_priv_repr  //pulse_spec
      deviceIDCSR_len deviceIDCSR_repr aliasKeyCRT_len aliasKeyCRT_repr repr)  //pulse_spec
{
  let ctxt = mk_l1_context_t  //pulse_code
    deviceID_pub aliasKey_pub aliasKey_priv deviceIDCSR_len deviceIDCSR aliasKeyCRT_len aliasKeyCRT;  //pulse_code
  
  let l1_ctxt_repr = hide (mk_l1_context_repr_t  //pulse_proof
    cdi deviceID_label_len aliasKey_label_len  //pulse_proof
    deviceIDCSR_ingredients aliasKeyCRT_ingredients  //pulse_proof
    deviceID_pub_repr aliasKey_pub_repr aliasKey_priv_repr  //pulse_proof
    deviceIDCSR_len deviceIDCSR_repr aliasKeyCRT_len aliasKeyCRT_repr  //pulse_proof
    repr);  //pulse_proof

  rewrite each  //pulse_proof
    deviceID_pub as ctxt.deviceID_pub,  //pulse_proof
    aliasKey_pub as ctxt.aliasKey_pub,  //pulse_proof
    aliasKey_priv as ctxt.aliasKey_priv,  //pulse_proof
    deviceIDCSR as ctxt.deviceIDCSR,  //pulse_proof
    aliasKeyCRT as ctxt.aliasKeyCRT;  //pulse_proof

  rewrite each  //pulse_proof
    cdi as l1_ctxt_repr.cdi,  //pulse_proof
    deviceID_pub_repr as l1_ctxt_repr.deviceID_pub,  //pulse_proof
    aliasKey_pub_repr as l1_ctxt_repr.aliasKey_pub,  //pulse_proof
    aliasKey_priv_repr as l1_ctxt_repr.aliasKey_priv,  //pulse_proof
    deviceIDCSR_repr as l1_ctxt_repr.deviceIDCSR,  //pulse_proof
    aliasKeyCRT_repr as l1_ctxt_repr.aliasKeyCRT;  //pulse_proof

  fold (l1_context_perm ctxt l1_ctxt_repr);  //pulse_proof
  ctxt  //pulse_code
}
```

```pulse
ghost
fn l0_record_perm_aux (r1 r2:l0_record_t) (#p:perm) (#repr:l0_record_repr_t)  //pulse_spec
  requires l0_record_perm r1 p repr **  //pulse_spec
           pure (r1.fwid == r2.fwid /\  //pulse_spec
                 r1.deviceID_label_len == r2.deviceID_label_len /\  //pulse_spec
                 r1.deviceID_label == r2.deviceID_label /\  //pulse_spec
                 r1.aliasKey_label_len == r2.aliasKey_label_len /\  //pulse_spec
                 r1.aliasKey_label == r2.aliasKey_label)  //pulse_spec
  ensures l0_record_perm r2 p repr  //pulse_spec
{
  unfold (l0_record_perm r1 p repr);  //pulse_proof
  rewrite (V.pts_to r1.fwid #p repr.fwid) as (V.pts_to r2.fwid #p repr.fwid);  //pulse_proof
  rewrite (V.pts_to r1.deviceID_label #p repr.deviceID_label)  //pulse_proof
       as (V.pts_to r2.deviceID_label #p repr.deviceID_label);  //pulse_proof
  rewrite (V.pts_to r1.aliasKey_label #p repr.aliasKey_label)  //pulse_proof
       as (V.pts_to r2.aliasKey_label #p repr.aliasKey_label);  //pulse_proof
  fold (l0_record_perm r2 p repr)  //pulse_proof
}
```

noextract
let context_derives_from_input (r:context_repr_t) (rrepr:repr_t) : prop =  //pulse_spec
  match r, rrepr with  //pulse_spec
  | L0_context_repr l0_repr, Engine_repr erepr ->  //pulse_spec
    l0_repr.repr == erepr  //pulse_spec
  | L1_context_repr l1_repr, L0_repr lrepr ->  //pulse_spec
    l1_repr.repr == lrepr  //pulse_spec
  | _ -> False  //pulse_spec
    
let maybe_context_perm (r:context_repr_t) (rrepr:repr_t) (c:option context_t) =  //pulse_spec
  match c with  //pulse_spec
  | Some c ->  //pulse_spec
    exists* repr. context_perm c repr **  //pulse_spec
                  pure (next_repr r repr /\ context_derives_from_input repr rrepr)  //pulse_spec
  | None -> emp  //pulse_spec

noextract
let valid_context_and_record_for_derive_child (c:context_repr_t) (r:repr_t) : prop =  //pulse_spec
  match c, r with  //pulse_spec
  | Engine_context_repr _, Engine_repr _ -> True  //pulse_spec
  | L0_context_repr _, L0_repr _ -> True  //pulse_spec
  | _ -> False  //pulse_spec

```pulse 
fn destroy_ctxt (ctxt:context_t) (#repr:erased context_repr_t)  //pulse_spec
  requires context_perm ctxt repr  //pulse_spec
  ensures emp  //pulse_spec
{
  match ctxt  //pulse_code
  {
    Engine_context c ->  //pulse_code
    {
      let uds = rewrite_context_perm_engine c;  //pulse_proof
      unfold (engine_context_perm c uds);  //pulse_proof
      V.free c.uds;  //pulse_code
    }
    L0_context c ->  //pulse_code
    {
      let r = rewrite_context_perm_l0 c;  //pulse_proof
      unfold (l0_context_perm c r);  //pulse_proof
      V.free c.cdi;  //pulse_code
    }
    L1_context c ->  //pulse_code
    {
      let r = rewrite_context_perm_l1 c;  //pulse_proof
      unfold (l1_context_perm c r);  //pulse_proof
      V.free c.deviceID_pub;  //pulse_code
      V.free c.aliasKey_priv;  //pulse_code
      V.free c.aliasKey_pub;  //pulse_code
      V.free c.aliasKeyCRT;  //pulse_code
      V.free c.deviceIDCSR;  //pulse_code
    }
  }
}
```

```pulse
fn derive_child_from_context  //pulse_spec
    (context:context_t)  //pulse_spec
    (record:record_t)  //pulse_spec
    (#record_repr: erased repr_t)  //pulse_spec
    (#context_repr:erased (context_repr_t))  //pulse_spec
    (_:squash (valid_context_and_record_for_derive_child context_repr record_repr))  //pulse_spec

  requires  //pulse_spec
    context_perm context context_repr **  //pulse_spec
    record_perm record 1.0R record_repr  //pulse_spec
  returns res:(option context_t)  //pulse_spec
  ensures  //pulse_spec
    maybe_context_perm context_repr record_repr res  //pulse_spec
{
  intro_context_and_repr_tag_related context context_repr;  //pulse_proof
  intro_record_and_repr_tag_related record 1.0R record_repr;  //pulse_proof
 
  match context {  //pulse_code
    Engine_context c -> {  //pulse_code
      match record {  //pulse_code
        Engine_record r -> {  //pulse_code
          let uds_bytes = rewrite_context_perm_engine c;  //pulse_proof
          unfold (engine_context_perm c uds_bytes);  //pulse_proof

          let engine_record_repr = rewrite_record_perm_engine r;  //pulse_proof

          let mut cdi = [| 0uy; dice_digest_len |];  //pulse_code

          V.to_array_pts_to c.uds;  //pulse_proof
          let ret = EngineCore.engine_main cdi (V.vec_to_array c.uds) r;  //pulse_code
          V.to_vec_pts_to c.uds;  //pulse_proof

          let r = fst ret;  //pulse_code
          rewrite each fst ret as r;  //pulse_proof

          with s. assert (A.pts_to cdi s);  //pulse_proof
          fold (engine_context_perm c uds_bytes);  //pulse_proof
          rewrite (engine_context_perm c uds_bytes)  //pulse_proof
               as (context_perm (Engine_context c) context_repr);  //pulse_proof
          rewrite (engine_record_perm r 1.0R engine_record_repr)  //pulse_proof
               as (record_perm (Engine_record r) 1.0R record_repr);  //pulse_proof

          destroy_ctxt (Engine_context c);  //pulse_code
          //
          // TODO: FIXME: deallocate
          //
          drop_ (record_perm (Engine_record r) 1.0R record_repr);  //pulse_proof
         
          match snd ret {  //pulse_code
            DICE_SUCCESS -> {  //pulse_code
              let l0_ctxt = init_l0_ctxt cdi #engine_record_repr #s #uds_bytes ();  //pulse_code
              with l0_ctxt_repr. assert (l0_context_perm l0_ctxt l0_ctxt_repr);  //pulse_proof
              fold (context_perm (L0_context l0_ctxt) (L0_context_repr l0_ctxt_repr));  //pulse_proof
              fold (maybe_context_perm context_repr record_repr (Some (L0_context l0_ctxt)));  //pulse_proof
              let ret = Some (L0_context l0_ctxt);  //pulse_code
              rewrite each  //pulse_proof
                Some (L0_context l0_ctxt) as ret;  //pulse_proof
              ret  //pulse_code
            }

            DICE_ERROR -> {  //pulse_code
              A.zeroize dice_digest_len cdi;  //pulse_code
              let ret = None #context_t;  //pulse_code
              rewrite emp as (maybe_context_perm context_repr record_repr ret);  //pulse_proof
              ret  //pulse_code
            }
          }
        }
        L0_record _ -> {  //pulse_code
          unreachable ()  //pulse_proof
        }
      }
    }
    
    L0_context c -> {  //pulse_code
      match record {  //pulse_code
        L0_record r -> {  //pulse_code
          let cr = rewrite_context_perm_l0 c;  //pulse_proof
          unfold (l0_context_perm c cr);  //pulse_proof
          with s. assert (V.pts_to c.cdi s);  //pulse_proof

          let r0 = rewrite_record_perm_l0 r;  //pulse_proof
          unfold (l0_record_perm r 1.0R r0);  //pulse_proof

          let deviceID_pub = V.alloc 0uy (SZ.uint_to_t 32);  //pulse_code
          let aliasKey_pub = V.alloc 0uy (SZ.uint_to_t 32);  //pulse_code
          let aliasKey_priv = V.alloc 0uy (SZ.uint_to_t 32);  //pulse_code
          assume_ (pure (SZ.fits_u32));  //pulse_proof
          let deviceIDCSR_len = L0Types.len_of_deviceIDCSR r.deviceIDCSR_ingredients;  //pulse_code
          let aliasKeyCRT_len = L0Types.len_of_aliasKeyCRT r.aliasKeyCRT_ingredients;  //pulse_code
          let deviceIDCSR = V.alloc 0uy (SZ.uint32_to_sizet deviceIDCSR_len);  //pulse_code
          let aliasKeyCRT = V.alloc 0uy (SZ.uint32_to_sizet aliasKeyCRT_len);  //pulse_code

          V.to_array_pts_to c.cdi;  //pulse_proof
          V.to_array_pts_to r.fwid;  //pulse_proof
          V.to_array_pts_to r.deviceID_label;  //pulse_proof
          V.to_array_pts_to r.aliasKey_label;  //pulse_proof
          V.to_array_pts_to deviceID_pub;  //pulse_proof
          V.to_array_pts_to aliasKey_pub;  //pulse_proof
          V.to_array_pts_to aliasKey_priv;  //pulse_proof
          V.to_array_pts_to deviceIDCSR;  //pulse_proof
          V.to_array_pts_to aliasKeyCRT;  //pulse_proof

          assume_ (pure (A.length (V.vec_to_array c.cdi) == 32));  //pulse_proof

          let _ : unit = l0  //pulse_code
            (V.vec_to_array c.cdi)  //pulse_code
            (V.vec_to_array r.fwid)  //pulse_code
            r.deviceID_label_len  //pulse_code
            (V.vec_to_array r.deviceID_label)  //pulse_code
            r.aliasKey_label_len  //pulse_code
            (V.vec_to_array r.aliasKey_label)  //pulse_code
            r.deviceIDCSR_ingredients  //pulse_code
            r.aliasKeyCRT_ingredients  //pulse_code
            (V.vec_to_array deviceID_pub)  //pulse_code
            (V.vec_to_array aliasKey_pub)  //pulse_code
            (V.vec_to_array aliasKey_priv)  //pulse_code
            deviceIDCSR_len  //pulse_code
            (V.vec_to_array deviceIDCSR)  //pulse_code
            aliasKeyCRT_len  //pulse_code
            (V.vec_to_array aliasKeyCRT);  //pulse_code
          
          V.to_vec_pts_to c.cdi;  //pulse_proof
          V.to_vec_pts_to r.fwid;  //pulse_proof
          V.to_vec_pts_to r.deviceID_label;  //pulse_proof
          V.to_vec_pts_to r.aliasKey_label;  //pulse_proof
          V.to_vec_pts_to deviceID_pub;  //pulse_proof
          V.to_vec_pts_to aliasKey_pub;  //pulse_proof
          V.to_vec_pts_to aliasKey_priv;  //pulse_proof
          V.to_vec_pts_to deviceIDCSR;  //pulse_proof
          V.to_vec_pts_to aliasKeyCRT;  //pulse_proof

          let l1_context : l1_context_t = init_l1_ctxt  //pulse_code
            s  //pulse_code
            (hide r.deviceID_label_len)  //pulse_proof
            (hide r.aliasKey_label_len)  //pulse_proof
            (hide r.deviceIDCSR_ingredients)  //pulse_proof
            (hide r.aliasKeyCRT_ingredients)  //pulse_proof
            deviceID_pub  //pulse_code
            aliasKey_priv  //pulse_code
            aliasKey_pub  //pulse_code
            deviceIDCSR_len  //pulse_code
            deviceIDCSR  //pulse_code
            aliasKeyCRT_len  //pulse_code
            aliasKeyCRT  //pulse_code
            r0  //pulse_proof
            (magic ());  //pulse_proof

          fold (l0_context_perm c cr);  //pulse_proof
          rewrite (l0_context_perm c cr) as  //pulse_proof
                  (context_perm (L0_context c) context_repr);  //pulse_proof
          fold (l0_record_perm r 1.0R r0);  //pulse_proof
          rewrite (l0_record_perm r 1.0R r0) as  //pulse_proof
                  (record_perm (L0_record r) 1.0R record_repr);  //pulse_proof

          destroy_ctxt (L0_context c);  //pulse_code
          drop_ (record_perm (L0_record r) 1.0R record_repr);  //pulse_proof
                    
          with l1_context_repr. assert (l1_context_perm l1_context l1_context_repr);  //pulse_proof
          
          fold (context_perm (L1_context l1_context) (L1_context_repr l1_context_repr));  //pulse_proof

          fold (maybe_context_perm context_repr record_repr (Some (L1_context l1_context)));  //pulse_proof
          let ret = Some (L1_context l1_context);  //pulse_code
          rewrite each  //pulse_proof
            Some (L1_context l1_context) as ret;  //pulse_proof

          ret  //pulse_code
        }
        Engine_record _ -> {  //pulse_code
          unreachable ()  //pulse_proof
        }
      }
    }

    L1_context _ -> {  //pulse_code
      unreachable ()  //pulse_proof
    }
  }
}
```

```pulse
ghost
fn rewrite_session_state_related_available  //pulse_spec
  context  //pulse_spec
  (s:session_state { s == Available { context } })  //pulse_spec
  (t:trace)  //pulse_spec
  requires session_state_related s (current_state t)  //pulse_spec
  returns r:G.erased context_repr_t  //pulse_spec
  ensures context_perm context r ** pure (current_state t == G_Available r)  //pulse_spec
{
  let cur = current_state t;  //pulse_proof
  intro_session_state_tag_related s cur;  //pulse_proof
  let repr = G_Available?.repr cur;  //pulse_proof
  rewrite (session_state_related s cur) as  //pulse_proof
          (context_perm context repr);  //pulse_proof
  hide repr  //pulse_proof
}
```

#push-options "--fuel 2 --ifuel 2 --split_queries no"
```pulse
fn derive_child (sid:sid_t)  //pulse_spec
  (t:G.erased trace)  //pulse_spec
  (record:record_t)  //pulse_spec
  (#rrepr:erased repr_t { trace_and_record_valid_for_derive_child t rrepr })  //pulse_spec
  requires record_perm record 1.0R rrepr **  //pulse_spec
           sid_pts_to trace_ref sid t  //pulse_spec
  returns b:bool  //pulse_spec
  ensures derive_child_client_perm sid t rrepr b  //pulse_spec
{
  intro_record_and_repr_tag_related record 1.0R rrepr;  //pulse_proof

  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));  //pulse_proof
  let s = replace_session sid t InUse (G_InUse (current_state t));  //pulse_code
  with t1. assert (sid_pts_to trace_ref sid t1);  //pulse_proof

  match s {  //pulse_code
    Available hc -> {  //pulse_code
      match hc.context {  //pulse_code
        L1_context _ -> {  //pulse_code
          rewrite (session_state_related s (current_state t)) as  //pulse_proof
                  (pure False);  //pulse_proof
          unreachable ()  //pulse_proof
        }
        _ -> {  //pulse_code
          assume_ (pure (~ (L1_context? hc.context)));  //pulse_proof
          let repr = rewrite_session_state_related_available hc.context s t;  //pulse_proof
          intro_context_and_repr_tag_related hc.context repr;  //pulse_proof
          let ret = derive_child_from_context hc.context record #rrepr #repr ();  //pulse_code

          match ret {  //pulse_code
            Some nctxt -> {  //pulse_code
              unfold (maybe_context_perm repr rrepr (Some nctxt));  //pulse_proof
              with nrepr. assert (context_perm nctxt nrepr);  //pulse_proof
              intro_context_and_repr_tag_related nctxt nrepr;  //pulse_proof
              let s = Available { context = nctxt };  //pulse_code
              rewrite (context_perm nctxt nrepr) as  //pulse_proof
                      (session_state_related s (G_Available nrepr));  //pulse_proof
              let s = replace_session sid t1 s (G_Available nrepr);  //pulse_code
              intro_session_state_tag_related s (current_state t1);  //pulse_proof
              fold (derive_child_client_perm sid t rrepr true);  //pulse_proof
              with _x _y. rewrite (session_state_related _x _y) as emp;  //pulse_proof
              true  //pulse_code
            }
            None -> {  //pulse_code
              let s = SessionError;  //pulse_code
              rewrite (maybe_context_perm repr rrepr ret) as emp;  //pulse_proof
              rewrite emp as (session_state_related s (G_SessionError (current_state t1)));  //pulse_proof
              let s = replace_session sid t1 s (G_SessionError (current_state t1));  //pulse_code
              intro_session_state_tag_related s (current_state t1);  //pulse_proof
              fold (derive_child_client_perm sid t rrepr false);  //pulse_proof
              with _x _y. rewrite (session_state_related _x _y) as emp;  //pulse_proof
              false  //pulse_code
            }
          }
        }
      }
    }
    SessionStart -> {  //pulse_code
      rewrite (session_state_related s (current_state t)) as  //pulse_proof
              (pure False);  //pulse_proof
      unreachable ()  //pulse_proof
    }
    InUse -> {  //pulse_code
      rewrite (session_state_related s (current_state t)) as  //pulse_proof
              (pure False);  //pulse_proof
      unreachable ()  //pulse_proof
    }
    SessionClosed -> {  //pulse_code
      rewrite (session_state_related s (current_state t)) as  //pulse_proof
              (pure False);  //pulse_proof
      unreachable ()  //pulse_proof
    }
    SessionError -> {  //pulse_code
      rewrite (session_state_related s (current_state t)) as  //pulse_proof
              (pure False);  //pulse_proof
      unreachable ()  //pulse_proof
    }
  }
}
```

```pulse
fn destroy_session_state (s:session_state) (t:G.erased trace)  //pulse_spec
  requires session_state_related s (current_state t)  //pulse_spec
  ensures emp  //pulse_spec
{
  intro_session_state_tag_related s (current_state t);  //pulse_proof
  match s {  //pulse_code
    Available hc -> {  //pulse_code
      rewrite_session_state_related_available hc.context s t;  //pulse_proof
      destroy_ctxt hc.context  //pulse_code
    }
    _ -> {  //pulse_code
      assume_ (pure (~ (Available? s)));  //pulse_proof
      with _x _y. rewrite (session_state_related _x _y) as emp  //pulse_proof
    }
  }
}
```

```pulse
fn close_session (sid:sid_t)  //pulse_spec
  (t:G.erased trace { trace_valid_for_close t })  //pulse_spec
  requires sid_pts_to trace_ref sid t  //pulse_spec
  ensures session_closed_client_perm sid t  //pulse_spec
{
  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));  //pulse_proof
  let s = replace_session sid t InUse (G_InUse (current_state t));  //pulse_code
  with t1. assert (sid_pts_to trace_ref sid t1);  //pulse_proof

  intro_session_state_tag_related s (current_state t);  //pulse_proof

  destroy_session_state s t;  //pulse_code

  rewrite emp as (session_state_related SessionClosed (G_SessionClosed (current_state t1)));  //pulse_proof
  let s = replace_session sid t1 SessionClosed (G_SessionClosed (current_state t1));  //pulse_code
  intro_session_state_tag_related s (current_state t1);  //pulse_proof
  with _x _y. rewrite (session_state_related _x _y) as emp;  //pulse_proof
  fold (session_closed_client_perm sid t)  //pulse_proof
}
```

#push-options "--z3rlimit_factor 4 --fuel 2 --ifuel 1 --split_queries no"
```pulse
fn certify_key (sid:sid_t)  //pulse_spec
  (pub_key:A.larray U8.t 32)  //pulse_spec
  (crt_len:U32.t)  //pulse_spec
  (crt:A.larray U8.t (U32.v crt_len))  //pulse_spec
  (t:G.erased trace { trace_valid_for_certify_key t })  //pulse_spec
  requires sid_pts_to trace_ref sid t **  //pulse_spec
           (exists* pub_key_repr crt_repr.  //pulse_spec
              A.pts_to pub_key pub_key_repr **  //pulse_spec
              A.pts_to crt crt_repr)  //pulse_spec
  returns _:U32.t  //pulse_spec
  ensures certify_key_client_perm sid t **  //pulse_spec
          (exists* pub_key_repr crt_repr.  //pulse_spec
             A.pts_to pub_key pub_key_repr **  //pulse_spec
             A.pts_to crt crt_repr)  //pulse_spec
{
  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));  //pulse_proof
  let s = replace_session sid t InUse (G_InUse (current_state t));  //pulse_code
  with t1. assert (sid_pts_to trace_ref sid t1);  //pulse_proof

  match s {  //pulse_code
    Available hc -> {  //pulse_code
      match hc.context {  //pulse_code
        L1_context c -> {  //pulse_code
          let c_crt_len = c.aliasKeyCRT_len;  //pulse_code
          if U32.lt crt_len c_crt_len {  //pulse_code
            let ns = Available { context = L1_context c };  //pulse_code
            rewrite (session_state_related s (current_state t)) as  //pulse_proof
                    (session_state_related ns (current_state t));  //pulse_proof
            let s = replace_session sid t1 ns (current_state t);  //pulse_code
            intro_session_state_tag_related s (current_state t1);  //pulse_proof
            with _x _y. rewrite (session_state_related _x _y) as emp;  //pulse_proof
            fold (certify_key_client_perm sid t);  //pulse_proof
            0ul  //pulse_code
          } else {  //pulse_code
            let r = rewrite_session_state_related_available (L1_context c) s t;  //pulse_proof
            let r = rewrite_context_perm_l1 c;  //pulse_proof
            unfold (l1_context_perm c r);  //pulse_proof

            V.to_array_pts_to c.aliasKey_pub;  //pulse_proof
            memcpy_l (SZ.uint_to_t 32) (V.vec_to_array c.aliasKey_pub) pub_key;  //pulse_code
            V.to_vec_pts_to c.aliasKey_pub;  //pulse_proof

            assume_ (pure (SZ.fits_u32));  //pulse_proof
            V.to_array_pts_to c.aliasKeyCRT;  //pulse_proof
            
            memcpy_l (SZ.uint32_to_sizet c.aliasKeyCRT_len) (V.vec_to_array c.aliasKeyCRT) crt;  //pulse_code
            V.to_vec_pts_to c.aliasKeyCRT;  //pulse_proof

            fold (l1_context_perm c r);  //pulse_proof
            rewrite (l1_context_perm c r) as  //pulse_proof
                    (context_perm (L1_context c) (L1_context_repr r));  //pulse_proof
            
            let ns = Available { context = L1_context c };  //pulse_code
            rewrite (context_perm (L1_context c) (L1_context_repr r)) as  //pulse_proof
                    (session_state_related ns (current_state t));  //pulse_proof
            
            let s = replace_session sid t1 ns (current_state t);  //pulse_code
            intro_session_state_tag_related s (current_state t1);  //pulse_proof
            with _x _y. rewrite (session_state_related _x _y) as emp;  //pulse_proof
            fold (certify_key_client_perm sid t);  //pulse_proof
            c_crt_len  //pulse_code
          }
        }
        _ -> {  //pulse_code
          assume_ (pure (~ (L1_context? hc.context)));  //pulse_proof
          rewrite (session_state_related s (current_state t)) as  //pulse_proof
                  (pure False);  //pulse_proof
          unreachable ()  //pulse_proof
        }
      }
    }
    _ -> {  //pulse_code
      assume_ (pure (~ (Available? s)));  //pulse_proof
      rewrite (session_state_related s (current_state t)) as  //pulse_proof
              (pure False);  //pulse_proof
      unreachable ()  //pulse_proof
    }
  }
}
```
#pop-options

#push-options "--split_queries no"
```pulse
fn sign (sid:sid_t)  //pulse_spec
  (signature:A.larray U8.t 64)  //pulse_spec
  (msg_len:SZ.t { SZ.v msg_len < pow2 32 })  //pulse_spec
  (msg:A.larray U8.t (SZ.v msg_len))  //pulse_spec
  (t:G.erased trace { trace_valid_for_sign t })  //pulse_spec
  requires sid_pts_to trace_ref sid t **  //pulse_spec
           (exists* signature_repr msg_repr.  //pulse_spec
              A.pts_to signature signature_repr **  //pulse_spec
              A.pts_to msg msg_repr)  //pulse_spec
  ensures sign_client_perm sid t **  //pulse_spec
          (exists* signature_repr msg_repr.  //pulse_spec
             A.pts_to signature signature_repr **  //pulse_spec
             A.pts_to msg msg_repr)  //pulse_spec
{
  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));  //pulse_proof
  let s = replace_session sid t InUse (G_InUse (current_state t));  //pulse_code
  with t1. assert (sid_pts_to trace_ref sid t1);  //pulse_proof

  match s {  //pulse_code
    Available hc -> {  //pulse_code
      match hc.context {  //pulse_code
        L1_context c -> {  //pulse_code
          let r = rewrite_session_state_related_available (L1_context c) s t;  //pulse_proof
          let r = rewrite_context_perm_l1 c;  //pulse_proof
          unfold (l1_context_perm c r);  //pulse_proof

          V.to_array_pts_to c.aliasKey_priv;  //pulse_proof
          HACL.ed25519_sign signature (V.vec_to_array c.aliasKey_priv) msg_len msg;  //pulse_code
          V.to_vec_pts_to c.aliasKey_priv;  //pulse_proof

          fold (l1_context_perm c r);  //pulse_proof
          rewrite (l1_context_perm c r) as  //pulse_proof
                  (context_perm (L1_context c) (L1_context_repr r));  //pulse_proof
            
          let ns = Available { context = L1_context c };  //pulse_code
          rewrite (context_perm (L1_context c) (L1_context_repr r)) as  //pulse_proof
                  (session_state_related ns (current_state t));  //pulse_proof
            
          let s = replace_session sid t1 ns (current_state t);  //pulse_code
          intro_session_state_tag_related s (current_state t1);  //pulse_proof
          with _x _y. rewrite (session_state_related _x _y) as emp;  //pulse_proof
          fold (sign_client_perm sid t);  //pulse_proof
        }
        _ -> {  //pulse_code
          assume_ (pure (~ (L1_context? hc.context)));  //pulse_proof
          rewrite (session_state_related s (current_state t)) as  //pulse_proof
                  (pure False);  //pulse_proof
          unreachable ()  //pulse_proof
        }
      }
    }
    _ -> {  //pulse_code
      assume_ (pure (~ (Available? s)));  //pulse_proof
      rewrite (session_state_related s (current_state t)) as  //pulse_proof
              (pure False);  //pulse_proof
      unreachable ()  //pulse_proof
    }
  }
}
```
#pop-options

(*
  GetProfile: Part of DPE API 
  Get the DPE's profile. 
*)
```pulse
fn get_profile ()
  requires emp
  returns d:profile_descriptor_t
  ensures emp
{
  mk_profile_descriptor
    (*name=*)""
    (*dpe_spec_version=*)1ul
    (*max_message_size=*)0ul // irrelevant: using direct interface
    (*uses_multi_part_messages=*)false
    (*supports_concurrent_operations=*)false // irrelevant by uses_multi_part_messages
    (*supports_encrypted_sessions=*)false // irrelevant by uses_multi_part_messages
    (*supports_derived_sessions=*)false // irrelevant by supports_encrypted_sessions
    (*max_sessions=*)0sz // irrelevant by supports_encrypted_sessions
    (*session_protocol=*)"" // irrelevant by supports_encrypted_sessions
    (*supports_session_sync=*)false // by supports_encrypted_sessions
    (*session_sync_policy=*)"" // irrelevant by supports_session_sync
    (*session_migration_protocol=*)"" // irrelevant by supports_session_migration
    (*supports_default_context=*)false
    (*supports_context_handles=*)true 
    (*max_contexts_per_session=*)1sz // 1 context per session
    (*max_context_handle_size=*)16sz // 16 bits
    (*supports_auto_init=*)false // irrelevant by supports_default_context
    (*supports_simulation=*)false
    (*supports_attestation=*)false
    (*supports_sealing=*)false 
    (*supports_get_profile=*)true
    (*supports_open_session=*)false // irrelevant by supports_encrypted_sessions
    (*supports_close_session=*)false // irrelevant by supports_encrypted_sessions
    (*supports_sync_session=*)false // irrelevant by supports_encrypted_sessions
    (*supports_export_session=*)false
    (*supports_import_session=*)false
    (*supports_init_context=*)true
    (*supports_certify_key=*)false // irrelevant by supports_attestation
    (*supports_sign=*)false // irrelevant by supports_attestation
    (*supports_seal=*)false // irrelevant by supports_sealing
    (*supports_unseal=*)false // irrelevant by supports_sealing
    (*supports_sealing_public=*)false // irrelevant by supports_sealing
    (*supports_rotate_context_handle=*)true
    (*dice_derivation=*)"" // FIXME: name for DICE algorithms
    (*asymmetric_derivation=*)"" // irrelevant by supports_attestation
    (*symmetric_derivation=*)"" // irrelevant by supports_attestation
    (*supports_any_label=*)false
    (*supported_labels=*)"" // FIXME: what are lables?
    (*initial_derivation=*)"" // FIXME: name?
    (*input_format=*)"" // FIXME: create CDDL spec for input record formats
    (*supports_internal_inputs=*)false
    (*supports_internal_dpe_info=*)false // irrelevant by supports_internal_inputs
    (*supports_internal_dpe_dice=*)false // irrelevant by supports_internal_inputs
    (*internal_dpe_info_type=*)"" // irrelevant by supports_internal_inputs
    (*internal_dpe_dice_type=*)"" // irrelevant by supports_internal_inputs
    (*internal_inputs=*)"" // irrelevant by supports_internal_inputs
    (*supports_certificates=*)false // irrelevant by supports_attestation
    (*max_certificate_size=*)0sz // irrelevant by supports_certificates
    (*max_certificate_chain_size=*)0sz // irrelevant by supports_certificates
    (*appends_more_certificates=*)false // irrelevant by supports_certificates
    (*supports_certificate_policies=*)false // irrelevant by supports_certificates
    (*supports_policy_identity_init=*)false // irrelevant by supports_certificate_policies
    (*supports_policy_identity_loc=*)false // irrelevant by supports_certificate_policies
    (*supports_policy_attest_init=*)false // irrelevant by supports_certificate_policies
    (*supports_policy_attest_loc=*)false // irrelevant by supports_certificate_policies
    (*supports_policy_assert_init=*)false // irrelevant by supports_certificate_policies
    (*supports_policy_assert_loc=*)false // irrelevant by supports_certificate_policies
    (*certificate_policies=*)"" // irrelevant by supports_certificate_policies
    (*supports_eca_certificates=*)false // irrelevant by supports_certificate_policies
    (*eca_certificate_format=*)"" // irrelevant by supports_eca_certificates
    (*leaf_certificate_format=*)"" // irrelevant by supports_certificates
    (*public_key_format=*)"" // irrelevant by supports_asymmetric_unseal
    (*supports_external_key=*)false // irrelevant by supports_certificates
    (*to_be_signed_format=*)"" // irrelevant by supports_sign
    (*signature_format=*)"" // irrelevant by supports_sign
    (*supports_symmetric_sign=*)false // irrelevant by supports_attestation
    (*supports_asymmetric_unseal=*)false // irrelevant by supports_attestation
    (*supports_unseal_policy=*)false// irrelevant by supports_sealing
    (*unseal_policy_format=*)"" // irrelevant by supports_unseal_policy 
}
```
