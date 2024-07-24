module SPDM3

open Pulse.Lib.Pervasives
open PulseCore.Preorder

module G = FStar.Ghost

module U16 = FStar.UInt16
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

type g_transcript = s:Seq.seq u8 { Seq.length s > 0 }

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
  | G_Initialized : signing_pub_key_repr:Seq.seq u8 -> g_state
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
  | G_UnInitialized, G_Initialized _ -> True
  //initial ---> no_sign (upon no_sign call)
  | G_Initialized k , G_Recv_no_sign_resp r
  // initial ---> sign (upon sign call)
  | G_Initialized k, G_Recv_sign_resp r ->
    k == r.signing_pub_key_repr

  // no_sign --> no_sign (upon no_sign call)
  | G_Recv_no_sign_resp r0,  G_Recv_no_sign_resp r1
  //no_sign ---> sign (upon sign call)
  | G_Recv_no_sign_resp r0, G_Recv_sign_resp r1  ->
    r0.signing_pub_key_repr == r1.signing_pub_key_repr /\
    is_prefix_of r0.transcript r1.transcript
        
  //sign ---> initial (no call is needed)
  | G_Recv_sign_resp r, G_Initialized k
  //no_sign --> initial (upon reset call)
  | G_Recv_no_sign_resp r, G_Initialized k ->
    r.signing_pub_key_repr == k

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
let previous_current_state (t:trace) : g_state =
  match t with
  | [] -> G_UnInitialized
  | hd::_ ->
    match hd with
    | [] -> G_UnInitialized
    | [s] -> G_UnInitialized
    | s::r::_ -> r


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
    | l -> (s::l)::t //t == l::tl

//previous_trace should remove the current_state from trace. Current state is the head of the head of the trace.
//head of the trace is list g_state. So head of the head of the trace is g_state
noextract
let previous_trace (t:trace): trace =
  match t with
  | [] -> []
  | hd::tl ->
    match hd with
    | [] -> tl
    | l -> admit()


noextract
type gref = ghost_pcm_ref trace_pcm

let session_state_related (s:state) (gs:g_state) : slprop =
  match s, gs with
  | Initialized st, G_Initialized k ->
    V.pts_to st.signing_pub_key k **
    V.pts_to st.session_transcript Seq.empty

  | Recv_no_sign_resp st, G_Recv_no_sign_resp repr ->
    V.pts_to st.signing_pub_key repr.signing_pub_key_repr **
    V.pts_to st.session_transcript repr.transcript

  | _ -> pure False

//
// The main invariant
// The session_state_related connects the concrete state with the current ghost state of the trace.
// r is the trace pointer with permission
//
let inv (s:state) (r:gref) (t:trace) : v:slprop =
  ghost_pcm_pts_to r (Some 1.0R, t) **
  session_state_related s (current_state t)

assume val trace_ref : gref

let init_client_perm (s:state) : slprop =
  exists* (t:trace). inv s trace_ref t ** pure (G_Initialized? (current_state t))

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
  measurement : v:V.vec u8 { V.length v == U16.v measurement_size }
}

//
//result structure
//
noeq
type spdm_measurement_result_t  = {
  measurement_block_count : u8;
  measurement_block_vector : v:V.vec spdm_measurement_block_t {
    V.length v == u8_v measurement_block_count
  };
  status : result  //TODO: Add refinement for the vector and length being 0 if result is not Success
}

//
//Signature of get_measurement_blocks_without_signature
//
let has_transcript (s:g_state) :prop =
  G_Recv_no_sign_resp? s \/ G_Recv_sign_resp? s

let g_transcript_of_gst (s:g_state { has_transcript s })
  : g_transcript =
  match s with
  | G_Recv_no_sign_resp r
  | G_Recv_sign_resp r -> r.transcript

let has_key (s:g_state) :prop =
  G_Initialized? s \/ G_Recv_no_sign_resp? s \/ G_Recv_sign_resp? s

let g_key_of_gst (s:g_state { has_key s })
  : Seq.seq u8 =
  match s with
  | G_Initialized k -> k
  | G_Recv_no_sign_resp r
  | G_Recv_sign_resp r -> r.signing_pub_key_repr

let current_transcript (t:trace { has_transcript (current_state t) }) : g_transcript =
  g_transcript_of_gst (current_state t)

let current_key (t:trace { has_transcript (current_state t) }) : Seq.seq u8 =
  g_key_of_gst (current_state t)

let g_transcript_current_session_grows (t0 t1:g_transcript) : prop =
  is_prefix_of t0 t1 

let g_transcript_current_session_grows_by (t0 t1:g_transcript) (s:Seq.seq u8) : prop =
   t1 == Seq.append t0 s

// let g_transcript_current_session_grows_lemma (t0 t1:g_transcript) (s:Seq.seq u8)
//   : Lemma (g_transcript_current_session_grows_by t0 t1 s ==>
//            g_transcript_current_session_grows t0 t1) = ()


assume val no_sign_resp
  (req_size: u8)
  (resp_size: u8)
  (req:V.vec u8 { V.length req == u8_v req_size })
  (resp:V.vec u8 { V.length resp == u8_v resp_size })
  (st:state)
  (#tr0:trace {has_transcript (current_state tr0) })  // TODO: it is either Initialized or Recv_no_sign_resp
  : stt spdm_measurement_result_t 
    (requires (exists* p_req b_req p_resp b_resp.
                          V.pts_to req #p_req b_req **
                          V.pts_to resp #p_resp b_resp) **
               inv st trace_ref tr0)
    (ensures fun res -> 
               (exists* p_req b_req p_resp b_resp.
                         V.pts_to req #p_req b_req **
                         V.pts_to resp #p_resp b_resp **
                         pure (Seq.length b_req == u8_v req_size) **
                         pure (Seq.length b_resp == u8_v resp_size) **
                         (let measurement_block_count = res.measurement_block_count in
                          let result = res.status in
                          (match result with
                          | Parse_error -> pure (u8_v measurement_block_count == 0) //zero out the measurement blocks, TODO: this will go away
                          | Signature_verification_error -> pure False
                          | Success -> 
                               (exists* r tr1. valid_resp resp r **
                                        inv st trace_ref tr1 **
                                        (let s = current_state tr1 in
                                        pure (G_Recv_no_sign_resp? s) **
                                        pure (valid_transition tr0 s /\ tr1 == next_trace tr0 s)  // TODO: Why multiple pure slprops
                                        ) **
                                        (let t0 = current_transcript tr0 in
                                         let t1 = current_transcript tr1 in
                                         pure (g_transcript_current_session_grows_by t0 t1 (Seq.append b_req b_resp)))
                                )))))

assume val valid_signature (signature msg key:Seq.seq u8): prop

let sign_resp_pre (st:state) 
                  (req_size: u8)
                  (resp_size: u8)
                  (req:V.vec u8 { V.length req == u8_v req_size })
                  (resp:V.vec u8 { V.length resp == u8_v resp_size })
                  (#tr0:trace {has_transcript (current_state tr0) }): slprop =
                  
(exists* p_req b_req p_resp b_resp.
                          V.pts_to req #p_req b_req **
                          V.pts_to resp #p_resp b_resp **
                          pure (Seq.length b_req == u8_v req_size) **
                          pure (Seq.length b_resp == u8_v resp_size)) **
                          inv st trace_ref tr0 **
                          pure (G_Recv_no_sign_resp? (current_state tr0) \/
                                G_Initialized? (current_state tr0))

let sign_resp_post_pts_to (req_size: u8)
                          (resp_size: u8)
                          (req:V.vec u8 { V.length req == u8_v req_size })
                          (resp:V.vec u8 { V.length resp == u8_v resp_size })
                          (p_req : perm)
                          (p_resp : perm)
                          (b_req : Seq.seq u8)
                          (b_resp : Seq.seq u8): slprop =
  V.pts_to req #p_req b_req **
  V.pts_to resp #p_resp b_resp **
  pure (Seq.length b_req == u8_v req_size) **
  pure (Seq.length b_resp == u8_v resp_size)

noextract
let next_next_trace (t:trace) (s1:g_state { valid_transition t s1 }) (s2:g_state { valid_transition ((next_trace t s1)) s2 }) : trace =
 next_trace (next_trace t s1) s2

let sign_resp_post_result_success (st:state) 
                                  (resp:V.vec u8 )
                                  (#tr0:trace {has_transcript (current_state tr0) })
                                  (p_req : perm)
                                  (p_resp : perm)
                                  (b_req : Seq.seq u8)
                                  (b_resp : Seq.seq u8): slprop =
  (exists* r tr1 sign. valid_resp resp r**
                                        inv st trace_ref tr1 **
                                        //tr1 current_state is G_Initailized
                                        pure (G_Initialized? (current_state tr1)) **
                                        
                                       //(previous_current_state tr1) transcript gets the req resp appended
                                        pure (G_Recv_sign_resp?(previous_current_state tr1) /\
                                        (let curr_state_post_trace = current_state tr1 in
                                         let previous_to_curr_state_post_trace = previous_current_state tr1 in
                                         let t0 = current_transcript tr0 in
                                         let t' = g_transcript_of_gst previous_to_curr_state_post_trace in
                                         let key = g_key_of_gst previous_to_curr_state_post_trace in
                                         let msg = t' in
                                         valid_signature sign msg key /\
                                         g_transcript_current_session_grows_by t0 t' (Seq.append b_req b_resp) /\
                                         tr1 == next_next_trace tr0 (previous_to_curr_state_post_trace) (curr_state_post_trace))) **
                                        
                                       
                                        (let t1 = current_transcript tr1 in
                                         pure (t1 == Seq.empty)
                                         )
                                )

assume val sign_resp
  (req_size: u8)
  (resp_size: u8)
  (req:V.vec u8 { V.length req == u8_v req_size })
  (resp:V.vec u8 { V.length resp == u8_v resp_size })
  (st:state)
  (#tr0:trace {has_transcript (current_state tr0) })
  : stt spdm_measurement_result_t 
    (requires  sign_resp_pre st req_size resp_size req resp #tr0)
    (ensures fun res -> 
               (exists* p_req b_req p_resp b_resp.
                         sign_resp_post_pts_to req_size resp_size req resp p_req p_resp b_req b_resp **

                         (let measurement_blocks = res.measurement_block_vector in
                          let measurement_block_count = res.measurement_block_count in
                          let result = res.status in
                          
                          (match result with
                          | Parse_error -> pure (u8_v measurement_block_count == 0) //zero out the measurement blocks
                          | Signature_verification_error -> pure (u8_v measurement_block_count == 0)
                          | Success -> 
                                sign_resp_post_result_success st resp #tr0 p_req p_resp b_req b_resp ))))



//
//Reset function
//
assume val reset
  (st:state)
  (#tr0:trace {has_transcript (current_state tr0) })
  : stt unit
    (requires (inv st trace_ref tr0 **
                          pure (G_Recv_no_sign_resp? (current_state tr0))
                          ))
    (ensures fun res -> init_client_perm st)

