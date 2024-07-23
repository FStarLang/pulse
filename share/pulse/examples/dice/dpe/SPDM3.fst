module SPDM3

open Pulse.Lib.Pervasives
open PulseCore.Preorder

module G = FStar.Ghost
module U32 = FStar.UInt32

module V = Pulse.Lib.Vec
module FP = Pulse.Lib.PCM.FractionalPreorder
module L = FStar.List.Tot


type u8 = FStar.UInt8.t
type u16 = FStar.UInt16.t
type u32 = FStar.UInt32.t

type u8_v = FStar.UInt8.v
type u16_v = FStar.UInt16.v
type u32_v = FStar.UInt32.v

//
// Setup:
// We will call a (possible empty) sequence of no_sign_resp messages, followed by a
//   sign_resp_message as a session
//

//
// Concrete state
// Only maintains the current session transcript
// This is the memory state associated with a state of the state machine. A state of the state machine takes
// the current memory state and returns a state of the state machine.
//
noeq
type st = {
  key_size : u32;
  signing_pub_key : V.vec u8;
  session_transcript : V.vec u8;
}

type g_transcript = (Seq.seq u8)

// Ghost repr
//
noeq
type repr = {
  signing_pub_key_repr : Seq.seq u8;
  transcript : g_transcript;
}

let g_transcript_non_empty (t:g_transcript) : prop =
  Seq.length t > 0

let is_initialized_transcript (t:g_transcript) : prop =
  Seq.equal t Seq.empty

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
  | G_Initialized : repr:repr{is_initialized_transcript repr.transcript} -> g_state
  | G_Recv_no_sign_resp : repr:repr ->  g_state

  | G_Recv_sign_resp : repr:repr -> g_state

let is_prefix_of (#a:Type) (s0 s1:Seq.seq a) : prop =
  Seq.length s0 < Seq.length s1 /\
  s0 == Seq.slice s1 0 (Seq.length s0)

  //
// The transition function
//
let next (s0 s1:g_state) : prop =
  match s0, s1 with
  //Uninit ---> initial (upon init call)
  |G_UnInitialized, G_Initialized r -> true
  //initial ---> no_sign (upon no_sign call)
  | G_Initialized r0 , G_Recv_no_sign_resp r1 ->
        g_transcript_non_empty r1.transcript

  // initial ---> sign (upon sign call)
  | G_Initialized r0 , G_Recv_sign_resp r1->
        g_transcript_non_empty r1.transcript

  // no_sign --> no_sign (upon no_sign call)
  | G_Recv_no_sign_resp r0 ,  G_Recv_no_sign_resp r1 ->
        g_transcript_non_empty r1.transcript /\
        g_transcript_non_empty r0.transcript /\
        is_prefix_of r0.transcript r1.transcript

  //no_sign ---> sign (upon sign call)
  | G_Recv_no_sign_resp r0, G_Recv_sign_resp r1  ->
        g_transcript_non_empty r1.transcript /\
        g_transcript_non_empty r0.transcript /\
        is_prefix_of r0.transcript r1.transcript
        
  //sign ---> initial (no call is needed)
  | G_Recv_sign_resp r0, G_Initialized r1 ->
        g_transcript_non_empty r0.transcript 

  //no_sign --> initial (upon reset call)
  |G_Recv_no_sign_resp r0, G_Initialized r1 ->
        g_transcript_non_empty r0.transcript

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

let session_state_related (s:state) (gs:g_state) : v:slprop { is_slprop2 v } =
  match s, gs with
  | Initialized st, G_Initialized repr
  | Recv_no_sign_resp st, G_Recv_no_sign_resp repr ->
    V.pts_to st.signing_pub_key repr.signing_pub_key_repr **
    V.pts_to st.session_transcript repr.transcript

  | _ -> pure False

  //
// The main invariant
// The session_state_related connects the concrete state with the current ghost state of the trace.
// r is the trace pointer with permission
//
let inv (s:state) (r:gref) (t:trace) : v:slprop { is_slprop2 v } =
  ghost_pcm_pts_to r (Some 1.0R, t) **
  session_state_related s (current_state t)

assume val trace_ref : gref

let init_client_perm (s:state) : slprop =
  exists* (t:trace).
    inv s trace_ref t ** pure (G_Initialized? (current_state t))

assume val init (key_len:u32) (signing_key:V.vec u8 { V.length signing_key == U32.v key_len })
  : stt state (requires exists* p b. V.pts_to signing_key #p b)
              (ensures fun s -> exists* p b. V.pts_to signing_key #p b ** init_client_perm s)


noeq
type resp_repr = {
  some_field : u32;
  // TODO
}

//
// Related to parser
//
assume val valid_resp (resp:V.vec u8) (repr:resp_repr) : slprop

type result =
  | Success
  | Parse_error
  | Signature_verification_error

//
//Measurement block structure
//

noeq
type spdm_measurement_block_t  = {
  index : u8;
  measurement_specification : u8;
  measurement_size : u16;
  measurement : V.vec u8
}
//
//result structure
//
noeq
type spdm_measurement_result_t  = {
  measurement_block_vector : V.vec  spdm_measurement_block_t;
  measurement_block_count : u8;
  status : result
}

//
//Signature of get_measurement_blocks_without_signature
//
let valid_state (s:g_state) :prop =
  G_Initialized? s \/ G_Recv_no_sign_resp? s \/ G_Recv_sign_resp? s

let g_transcript_of_gst (s:g_state { valid_state s })
  : g_transcript =
  match s with
  | G_Initialized r
  | G_Recv_no_sign_resp r
  | G_Recv_sign_resp r -> r.transcript

let g_key_of_gst (s:g_state { valid_state s })
  : Seq.seq u8 =
  match s with
  | G_Initialized r
  | G_Recv_no_sign_resp r
  | G_Recv_sign_resp r -> r.signing_pub_key_repr

let current_transcript (t:trace { valid_state (current_state t) }) : g_transcript =
  g_transcript_of_gst (current_state t)

let current_key (t:trace { valid_state (current_state t) }) : Seq.seq u8 =
  g_key_of_gst (current_state t)

let g_transcript_current_session_grows (t0 t1:g_transcript) : prop =
  is_prefix_of t0 t1 

let g_transcript_current_session_grows_by (t0 t1:g_transcript) (s:Seq.seq u8) : prop =
   g_transcript_current_session_grows t0 t1 /\
   t1 == Seq.append t0 s

let g_transcript_current_session_grows_lemma (t0 t1:g_transcript) (s:Seq.seq u8)
  : Lemma (g_transcript_current_session_grows_by t0 t1 s ==>
           g_transcript_current_session_grows t0 t1) = ()


assume val no_sign_resp
  (req:V.vec u8)
  (resp:V.vec u8)
  (req_size: u8)
  (resp_size: u8)
  (st:state)
  (#tr0:trace {valid_state (current_state tr0) })
  : stt spdm_measurement_result_t 
    (requires (exists* p_req b_req p_resp b_resp.
                          V.pts_to req #p_req b_req **
                          V.pts_to resp #p_resp b_resp **
                          pure (Seq.length b_req == u8_v req_size) **
                          pure (Seq.length b_resp == u8_v resp_size)) **
                          inv st trace_ref tr0 **
                          pure (G_Recv_no_sign_resp? (current_state tr0) \/
                                G_Initialized? (current_state tr0))
                          )
    (ensures fun res -> 
               (exists* p_req b_req p_resp b_resp.
                         V.pts_to req #p_req b_req **
                         V.pts_to resp #p_resp b_resp **
                         pure (Seq.length b_req == u8_v req_size) **
                         pure (Seq.length b_resp == u8_v resp_size) **
                         (let measurement_blocks = res.measurement_block_vector in
                          let measurement_block_count = res.measurement_block_count in
                          let result = res.status in
                          (match result with
                          | Parse_error -> pure (u8_v measurement_block_count == 0) //zero out the measurement blocks
                          | Signature_verification_error -> pure False
                          | Success -> 
                               (exists* r tr1. valid_resp resp r **
                                        inv st trace_ref tr1 **
                                        (let s = current_state tr1 in
                                        pure (G_Recv_no_sign_resp? s) **
                                        pure (valid_transition tr0 s) **
                                        pure (valid_transition tr0 s /\ tr1 == next_trace tr0 s)
                                        ) **
                                        (let t0 = current_transcript tr0 in
                                         let t1 = current_transcript tr1 in
                                         pure (g_transcript_current_session_grows_by t0 t1 (Seq.append b_req b_resp)))
                                )))))

assume val valid_signature (signature msg key:Seq.seq u8): prop

assume val sign_resp
  (req:V.vec u8)
  (resp:V.vec u8)
  (req_size: u8)
  (resp_size: u8)
  (st:state)
  (#tr0:trace {valid_state (current_state tr0) })
  : stt spdm_measurement_result_t 
    (requires (exists* p_req b_req p_resp b_resp.
                          V.pts_to req #p_req b_req **
                          V.pts_to resp #p_resp b_resp **
                          pure (Seq.length b_req == u8_v req_size) **
                          pure (Seq.length b_resp == u8_v resp_size)) **
                          inv st trace_ref tr0 **
                          pure (G_Recv_no_sign_resp? (current_state tr0) \/
                                G_Initialized? (current_state tr0))
                          )
    (ensures fun res -> 
               (exists* p_req b_req p_resp b_resp.
                         V.pts_to req #p_req b_req **
                         V.pts_to resp #p_resp b_resp **
                         pure (Seq.length b_req == u8_v req_size) **
                         pure (Seq.length b_resp == u8_v resp_size) **
                         (let measurement_blocks = res.measurement_block_vector in
                          let measurement_block_count = res.measurement_block_count in
                          let result = res.status in
                          
                          (match result with
                          | Parse_error -> pure (u8_v measurement_block_count == 0) //zero out the measurement blocks
                          | Signature_verification_error -> pure (u8_v measurement_block_count == 0)
                          | Success -> 
                               (exists* r tr1 sign inter_gstate inter_trace. valid_resp resp r **
                                        inv st trace_ref tr1 **
                                        //tr1 current_state is G_Initailized
                                        pure (G_Initialized? (current_state tr1)) **
                                        //intermedite trace inter_trace exists and inter g_state exists
                                        pure (G_Recv_sign_resp?inter_gstate) **
                                        //Relation between inter_trace and inter_gstate
                                        pure (current_state inter_trace == inter_gstate) **

                                        //inter_trace transcript gets the req resp appended
                                        (let s = current_state tr1 in
                                         let s1 = current_state inter_trace in
                                         let t0 = current_transcript tr0 in
                                         let t' = current_transcript inter_trace in
                                         let key = current_key inter_trace in
                                         let msg = t' in

                                         //From inter_trace l2 is found out
                                         pure (valid_signature sign msg key) **
                                         pure (g_transcript_current_session_grows_by t0 t' (Seq.append b_req b_resp)) **
                                         pure (valid_transition tr0 s1 /\ 
                                                valid_transition inter_trace s)) **
                                        
                                        //inter_trace ---> tr1
                                        (let t1 = current_transcript tr1 in
                                         pure (t1 == Seq.empty)
                                         )
                                )))))

//
//Reset function
//
assume val reset
  (st:state)
  (#tr0:trace {valid_state (current_state tr0) })
  : stt unit
    (requires (inv st trace_ref tr0 **
                          pure (G_Recv_no_sign_resp? (current_state tr0))
                          ))
    (ensures fun res -> init_client_perm st)

