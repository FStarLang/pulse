module SPDM

open Pulse.Lib.Pervasives
open PulseCore.Preorder

module G = FStar.Ghost

module V = Pulse.Lib.Vec
module FP = Pulse.Lib.PCM.FractionalPreorder



type u8 = FStar.UInt8.t
type u32 = FStar.UInt32.t

//
// Setup:
// We will call a (possible empty) sequence of no_sign_resp messages, followed by a
//   sign_resp_message as a session
//

//
// Concrete state
// Only maintains the current session transcript
//
noeq
type st = {
  key_size : u32;
  signing_pub_key : V.vec u8;
  session_transcript : V.vec u8;
}

//
// Ghost transcript maintains transcripts for all the sessions
// The current session is the last element of the sequence
//
type g_transcript = Seq.seq (Seq.seq u8)

//
// Ghost repr
//
noeq
type repr = {
  signing_pub_key_repr : Seq.seq u8;
  transcript : t:g_transcript { Seq.length t > 0 };
}

let g_transcript_non_empty (t:g_transcript) : prop =
  Seq.length t > 0

let g_transcript_all_but_current_session (t:g_transcript { g_transcript_non_empty t})
  : g_transcript =
  
  Seq.slice t 0 (Seq.length t - 1)

let g_transcript_current_session (t:g_transcript { g_transcript_non_empty t }) : Seq.seq u8 =
  Seq.index t (Seq.length t - 1)

let is_prefix_of (#a:Type) (s0 s1:Seq.seq a) : prop =
  Seq.length s0 < Seq.length s1 /\
  s0 == Seq.slice s1 0 (Seq.length s0)

//
// An initialized transcript keeps an empty sequence as transcript for the current session
//
let is_initialized_transcript (t:g_transcript) : prop =
  g_transcript_non_empty t /\
  Seq.equal (g_transcript_current_session t) Seq.empty

//
// t0 and t1 have same sessions, the current session grows from t0 to t1
//
let g_transcript_current_session_grows (t0 t1:g_transcript) : prop =
  g_transcript_non_empty t0 /\
  Seq.length t0 == Seq.length t1 /\
  g_transcript_all_but_current_session t0 == g_transcript_all_but_current_session t1 /\
  is_prefix_of (g_transcript_current_session t0) (g_transcript_current_session t1)  

//
// States of the state machine
//
noeq
type state =
  | Initialized : st -> state
  | Recv_no_sign_resp : st -> state

//
// Corresponding ghost states
//
noeq
type g_state : Type u#1 =
  | G_UnInitialized : g_state
  | G_Initialized : repr -> g_state
  | G_Recv_no_sign_resp : repr -> g_state

//
// The transition function
//
let next (s0 s1:g_state) : prop =
  match s0, s1 with
  | G_UnInitialized, G_Initialized r ->
    //
    // When the state machine starts, the transcript is [[]]
    //
    Seq.equal r.transcript (Seq.create 1 Seq.empty)
  
    //
    // No other transitions to/from UnInitialized
    //
  | G_UnInitialized, _
  | _, G_UnInitialized -> False

    //
    // These two transitions process a sign_resp message
    //
  | G_Initialized r0, G_Initialized r1
  | G_Recv_no_sign_resp r0, G_Initialized r1 ->
    g_transcript_current_session_grows r0.transcript (g_transcript_all_but_current_session r1.transcript) /\
    is_initialized_transcript r1.transcript

    //
    // These two transitions process a np_sign_resp message
    //
  | G_Initialized r0, G_Recv_no_sign_resp r1  
  | G_Recv_no_sign_resp r0, G_Recv_no_sign_resp r1 ->
    g_transcript_current_session_grows r0.transcript r1.transcript  

  | _ -> False

//
// Until gref, this is setting up the trace PCM
//
noextract
let rec well_formed_trace (l:list g_state) : prop =
  match l with
  | []
  | [G_Initialized _] -> True
  | s1::s0::tl -> next s0 s1 /\ well_formed_trace (s0::tl)
  | _ -> False

noextract
type trace_elt : Type u#1 = l:list g_state { well_formed_trace l }

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

noextract
let trace_pcm : FStar.PCM.pcm trace_pcm_t = FP.fp_pcm trace_preorder

noextract
let current_state (t:trace) : g_state =
  match t with
  | [] -> G_UnInitialized
  | hd::_ ->
    match hd with
    | [] -> G_UnInitialized
    | s::_ -> s

noextract
let valid_transition (t:trace) (s:g_state) : prop =
  next (current_state t) s

noextract
let next_trace (t:trace) (s:g_state { valid_transition t s }) : trace =
  match t with
  | [] -> [[s]]
  | hd::tl ->
    match hd with
    | [] -> [s]::t
    | l -> (s::l)::t

noextract
type gref = ghost_pcm_ref trace_pcm


//
// Concrete state s is related to the ghost state gs
//
// (I don't think we need this to be slprop2.)
//
let session_state_related (s:state) (gs:g_state) : v:slprop { is_slprop2 v } =
  match s, gs with
  | Initialized st, G_Initialized repr
  | Recv_no_sign_resp st, G_Recv_no_sign_resp repr ->
    V.pts_to st.signing_pub_key repr.signing_pub_key_repr **
    V.pts_to st.session_transcript (g_transcript_current_session repr.transcript)

  | _ -> pure False

//
// The main invariant
//
let inv (s:state) (r:gref) (t:trace) : v:slprop { is_slprop2 v } =
  ghost_pcm_pts_to r (Some 1.0R, t) **
  session_state_related s (current_state t)

assume val trace_ref : gref

let init_client_perm (s:state) : slprop =
  exists* (t:trace).
    inv s trace_ref t ** pure (G_Initialized? (current_state t))

assume val init ()
  : stt state (requires emp)
              (ensures fun s -> init_client_perm s)