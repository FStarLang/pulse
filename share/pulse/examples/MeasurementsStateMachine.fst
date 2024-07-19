module MeasurementsStateMachine
open Pulse.Lib.Pervasives
open FStar.Mul

module G = FStar.Ghost
module PCM = FStar.PCM
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module PM = Pulse.Lib.PCMMap
module FP = Pulse.Lib.PCM.FractionalPreorder
module A = Pulse.Lib.Array
module HT = Pulse.Lib.HashTable
module PHT = Pulse.Lib.HashTable.Spec

open PulseCore.Preorder
open Pulse.Lib.OnRange

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec

[@@CMacro]
let max_measurement_record_size = 0x1000

[@@CMacro]
let max_transcript_record_size = 0x1000

[@@CMacro]
let spdm_nonce_size = 32

[@@CMacro]
let spdm_max_asym_key_size = 512

[@@CMacro]
let spdm_max_opaque_data_size = 1024

[@@CMacro]
let max_version_count = 5

[@@CMacro]
let max_message_vca_buf_size = (200 + 2 * max_version_count)

//Fix it later - #define LIBSPDM_MAX_MESSAGE_D_BUFFER_SIZE (4 + \
//                                           (LIBSPDM_MAX_HASH_SIZE + 4) * SPDM_MAX_SLOT_COUNT)
[@@CMacro]
let max_message_d_buf_size =  (200 + 2 * max_version_count)

[@@CMacro]
let max_message_m_buf_size = 
  (63 + spdm_nonce_size + max_measurement_record_size + spdm_max_asym_key_size + spdm_max_opaque_data_size)

[@@CMacro]
let max_transcript_buf_size =
  1024

(*noeq
type spdm_message_m_managed_buffer_t = {
    max_buffer_size: U32.t;
    buffer_size : U32.t;
    buf : V.lvec U8.t (max_message_m_buf_size);
}

type g_spdm_message_m_managed_buffer_t = Seq.seq U8.t*)

(*noeq type st = {
     key_size: U32.t;
     transcript : V.lvec spdm_message_m_managed_buffer_t(max_transcript_buf_size)
}*)

noeq type st = {
     key_size: U32.t;
     transcript : V.vec U8.t//(max_message_m_buf_size * max_transcript_buf_size)
}


type g_st = Seq.seq U8.t

(*State the relation between st and g_st
   1. st is the vector version of g_st
   2. relate each message buffers inside st with that of g_st*)

let is_state (s:st) (g_s:g_st) = 
 V.pts_to s.transcript g_s

noeq
type transcript_context_t = { 
  uds: V.vec U8.t; 
}

noeq
type transcript_t = 
  | Transcript_context : c:transcript_context_t-> transcript_t

noeq
type transcript_repr_t = 
  | Transcript_context_repr : uds:Seq.seq U8.t -> transcript_repr_t

noeq
type session_state =
  | Start           {context:transcript_t}

  | No_Sign_Process {context:transcript_t}     

 [@@ erasable]
noeq
type g_session_state : Type u#1 =
  | G_UnInitialized : g_session_state
  | G_Start : repr:transcript_repr_t ->g_session_state
  | G_No_Sign_Process : repr:transcript_repr_t ->g_session_state

//
// State machine
//
noextract
let next (s0 s1:g_session_state) : prop =
  match s0, s1 with
  //
  // UnInitialized may only go to SessionStart
  // No other incoming/outgoing edges to/from it
  //
  | G_UnInitialized, G_Start(Transcript_context_repr _) -> True
  | G_UnInitialized, _
  | _, G_UnInitialized -> False
  | G_Start(Transcript_context_repr _), G_Start(Transcript_context_repr _) -> True

  | G_Start(Transcript_context_repr _),  G_No_Sign_Process(Transcript_context_repr _) -> True

  | G_No_Sign_Process(Transcript_context_repr _), G_Start (Transcript_context_repr _) -> True

  | G_No_Sign_Process(Transcript_context_repr _), G_No_Sign_Process(Transcript_context_repr _) -> True

  | _ -> False

noextract
let rec well_formed_trace (l:list g_session_state) : prop =
  match l with
  | []
  | [G_Start(Transcript_context_repr _)] -> True
  | s1::s0::tl -> next s0 s1 /\ well_formed_trace (s0::tl)
  | _ -> False
  
  noextract
type trace_elt : Type u#1 = l:list g_session_state { well_formed_trace l }

noextract
let trace_extension (t0 t1:trace_elt) : prop =
  Cons? t1 /\ t0 == List.Tot.tail t1

noextract
let trace_preorder : FStar.Preorder.preorder trace_elt =
  FStar.ReflexiveTransitiveClosure.closure trace_extension

noextract
type trace = hist trace_preorder

noextract
type trace_pcm_t : Type u#1 = FP.pcm_carrier trace_preorder

//
// Trace PCM is fractional preorder PCM,
//   with trace preorder
//
noextract
let trace_pcm : FStar.PCM.pcm trace_pcm_t = FP.fp_pcm trace_preorder

//
// Current state of a trace
//
// We use UnInitialized as the current state of empty trace
//
noextract
let current_state (t:trace) : g_session_state =
  match t with
  | [] -> G_UnInitialized
  | hd::_ ->
    match hd with
    | [] -> G_UnInitialized
    | s::_ -> s

//
// Given a trace t, valid_transition t s means that
//   current state of t may go to s in the state machine
//
noextract
let valid_transition (t:trace) (s:g_session_state) : prop =
  next (current_state t) s

//
// The next trace after a transition
//
noextract
let next_trace (t:trace) (s:g_session_state { valid_transition t s }) : trace =
  match t with
  | [] -> [[s]]
  | hd::tl ->
    match hd with
    | [] -> [s]::t
    | l -> (s::l)::t

noextract
let mk_frame_preserving_upd
  (t:hist trace_preorder)
  (s:g_session_state { valid_transition t s })
  : FStar.PCM.frame_preserving_upd trace_pcm (Some 1.0R, t) (Some 1.0R, next_trace t s) =
  fun _ -> Some 1.0R, next_trace t s

noextract
let snapshot (x:trace_pcm_t) : trace_pcm_t = None, snd x

let snapshot_idempotent (x:trace_pcm_t)
  : Lemma (snapshot x == snapshot (snapshot x)) = ()

let snapshot_duplicable (x:trace_pcm_t)
  : Lemma
      (requires True)
      (ensures x `FStar.PCM.composable trace_pcm` snapshot x) = ()

let full_perm_empty_history_compatible ()
  : Lemma (FStar.PCM.compatible trace_pcm (Some 1.0R, []) (Some 1.0R, [])) = ()

noextract
type pcm_t : Type u#1 = trace_pcm_t

noextract
let pcm : PCM.pcm pcm_t = trace_pcm

[@@ erasable]
noextract
type gref = ghost_pcm_ref pcm

noextract
let emp_trace : trace = []

noextract
let singleton (p:perm) (t:trace) : GTot pcm_t =
  (Some p, t)

//
// The main permission we provide to the client,
//   to capture the session history for a sid
//
noextract
let session_pts_to (r:gref)  (t:trace) : slprop =
  ghost_pcm_pts_to r (singleton 0.5R t)

let transcript_context_perm (c:transcript_context_t) (uds_bytes:Seq.seq U8.t) : slprop
  = V.pts_to c.uds uds_bytes ** 
    pure (V.is_full_vec c.uds)


let context_perm (context:transcript_t) (repr:transcript_repr_t): slprop = 
  match context, repr with
  | Transcript_context c, Transcript_context_repr uds -> transcript_context_perm c uds

noextract
let trace_valid_for_start (t:trace) : prop =
   match current_state t with
   | G_UnInitialized 
   | G_Start _
   | G_No_Sign_Process _ -> True
   | _ -> False

let session_state_related (s:session_state) (gs:g_session_state) : v:slprop { is_slprop2 v } =
    match s, gs with
  | Start{context}, G_Start repr ->  context_perm context repr
  | No_Sign_Process {context}, G_No_Sign_Process repr -> context_perm context repr
  | _ -> pure False

//
// Invariant for sessions that have been started
//
let session_state_perm (r:gref) : v:slprop { is_slprop2 v } =
  exists* (s:session_state) (t:trace).
    session_pts_to r t **
    session_state_related s (current_state t)

let session_perm (r:gref)  =
  session_state_perm r 
  
let meas_inv (r:gref) (s:option st) : slprop =
  match s with
  | None -> ghost_pcm_pts_to r (Some 1.0R, emp_trace)
  | Some s -> admit()


let inv_is_slprop2 (r:gref) (s:option st)
  : Lemma (is_slprop2 (meas_inv r s))
          [SMTPat (is_slprop2 (meas_inv r s))] = admit()

val trace_ref : gref

let trace_ref = admit()


noextract
let trace_valid_for_initialize_context (t:trace) (*(repr:transcript_repr_t)*) : prop =
  current_state t == G_UnInitialized

let initialize_context_client_perm (uds:Seq.seq U8.t) =
  exists* t. session_pts_to trace_ref  t **
             pure (current_state t == G_Start (Transcript_context_repr uds)) **
             pure (Seq.length uds == 0)

val initialize_context
  (t:G.erased trace {trace_valid_for_initialize_context t })
  (#p:perm) (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  (uds:A.array U8.t) 
  : stt unit
        (requires
           A.pts_to uds #p uds_bytes **
           session_pts_to trace_ref  t)
        (ensures fun b ->
           A.pts_to uds #p uds_bytes **
           initialize_context_client_perm uds_bytes)
