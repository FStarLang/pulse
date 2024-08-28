module SPDM

#lang-pulse

open Pulse.Lib.Pervasives
open PulseCore.Preorder

module G = FStar.Ghost

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

module V = Pulse.Lib.Vec
module FP = Pulse.Lib.PCM.FractionalPreorder
module L = FStar.List.Tot
module E = FStar.Endianness
module O = Pulse.Lib.OnRange
module R = Pulse.Lib.Reference


type u8 = FStar.UInt8.t
type u16 = FStar.UInt16.t
type u32 = FStar.UInt32.t

type u8_v = FStar.UInt8.v
type u16_v = FStar.UInt16.v
type u32_v = FStar.UInt32.v

open FStar.Mul

[@@CMacro]
let spdm_req_context_size = 8

//TODO this should not be hard coded. Based on the base asymmetric algorithm, the signature size should be selected.
[@@CMacro]
let signature_size = 256

//
// TODO: A configurable parameter that initializes the state machine without signature and transcript and key.
//

let spdm_nonce_size = 32

let max_measurement_record_size = 0x1000

let max_asym_key_size = (48 * 2)

let max_opaque_data_size = 1024

let max_transcript_message_buffer_size = 
  63 + spdm_nonce_size  +  max_measurement_record_size  + max_asym_key_size + max_opaque_data_size

let max_transcript_message_buffer_size_u32 = U32.uint_to_t max_transcript_message_buffer_size

type g_transcript = Ghost.erased (Seq.seq u8)

// Ghost repr
//

let hash_size = 256

let hash_algo = 256ul

let hash_spec
  (algo:u32)
  (ts_digest: Seq.seq u8{Seq.length ts_digest == hash_size})
  (msg: Seq.seq u8)
  : GTot (t:(Seq.seq u8){Seq.length t== hash_size})  = admit()

  val hash (hash_algo: u32)
         (ts_digest: V.vec u8{V.length ts_digest == hash_size})
         (msg_size: u32{u32_v msg_size > 0})
         (msg: V.vec u8{V.length msg == u32_v msg_size})
         (#ts_seq: (G.erased (Seq.seq u8)){Seq.length ts_seq == hash_size})
         (#msg_seq: (G.erased (Seq.seq u8)))
         (#p_msg:perm)
  : stt unit
        (requires V.pts_to ts_digest ts_seq **
                  V.pts_to msg #p_msg msg_seq)
        (ensures fun _ -> V.pts_to msg #p_msg msg_seq **
                          V.pts_to ts_digest (hash_spec hash_algo ts_seq msg_seq))

let hash_of (hash_algo: u32)
            (s0:Seq.seq u8{Seq.length s0 == hash_size })
            (req:Seq.seq u8)
            (resp:Seq.seq u8)
            (s1:Seq.seq u8{Seq.length s1 == hash_size})
                  : prop =
  Seq.equal s1 (hash_spec hash_algo (hash_spec hash_algo s0 req)  resp)

[@@ erasable]
noeq
type repr = {
  key_size_repr : u32;
  signing_pub_key_repr : Seq.seq u8;
  transcript : g:g_transcript{Seq.length g == hash_size};
}

let byte_seq = Seq.seq u8


[@@ erasable]
noeq
type g_state : Type u#1 =
  | G_UnInitialized : g_state
  | G_Initialized :  repr:repr -> g_state
  | G_Recv_no_sign_resp : repr:repr -> byte_seq -> byte_seq -> g_state
  | G_Recv_sign_resp : repr:repr -> byte_seq -> byte_seq -> g_state

//Transition function
let next (s0 s1:g_state) : prop =
  match s0, s1 with
  //Uninit ---> initial (upon init call)
  | G_UnInitialized, G_Initialized _ -> True

  //initial ---> no_sign (upon no_sign call)
  | G_Initialized k , G_Recv_no_sign_resp r req resp
  // initial ---> sign (upon sign call)
  | G_Initialized k, G_Recv_sign_resp r req resp->
    k.signing_pub_key_repr == r.signing_pub_key_repr /\
    k.key_size_repr == r.key_size_repr /\
     hash_of hash_algo k.transcript req resp r.transcript


  // no_sign --> no_sign (upon no_sign call)
  | G_Recv_no_sign_resp r0 req0 resp0,  G_Recv_no_sign_resp r1 req1 resp1
  //no_sign ---> sign (upon sign call)
  | G_Recv_no_sign_resp r0 req0 resp0, G_Recv_sign_resp r1 req1 resp1  ->
    r0.signing_pub_key_repr == r1.signing_pub_key_repr /\
    r0.key_size_repr = r1.key_size_repr /\
    hash_of hash_algo r0.transcript req1 resp1 r1.transcript
        
  //sign ---> initial (no call is needed)
  | G_Recv_sign_resp r req resp, G_Initialized k
  //no_sign --> initial (upon reset call)
  | G_Recv_no_sign_resp r req resp, G_Initialized k ->
    r.signing_pub_key_repr == k.signing_pub_key_repr /\
    r.key_size_repr == k.key_size_repr 

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
type pcm_t : Type u#1 = trace_pcm_t

noextract
type gref = ghost_pcm_ref trace_pcm

let pcm_elt (p:perm) (t:trace) : pcm_t = Some p, t

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
  | []
  | []::_
  | [_]::_ -> G_UnInitialized 
  | (_::t::_)::_ -> t

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

noextract
let emp_trace : trace = []

noextract
let emp_trace_pcm  (p:perm) (t:trace) : GTot pcm_t =
   (None, emp_trace)

//
// A frame preserving update in the trace PCM,
//   given a valid transition
//
noextract
let mk_frame_preserving_upd
  (t:trace)
  (s:g_state { valid_transition t s})
  : FStar.PCM.frame_preserving_upd trace_pcm (Some 1.0R, t) (Some 1.0R, next_trace t s) =
  fun _ -> Some 1.0R, next_trace t s

  noeq
type st = {
  key_size : u32;
  signing_pub_key : v:V.vec u8 { V.length v == U32.v key_size };
  session_transcript : v:V.vec u8{V.is_full_vec v /\ V.length v == hash_size};
  g_trace_ref:gref
}

//
// States of the state machine
//

let byte_vec = V.vec u8

noeq
type state =
  | Initialized : st -> state
  | Recv_no_sign_resp : st -> byte_vec -> byte_vec -> state



// noextract
// let singleton (p:perm) (t:trace) : GTot pcm_t =
//   Map.upd (Map.const (None, emp_trace)) (Some p, t)

let session_state_related (s:state) (gs:g_state) : slprop =
  match s, gs with
  | Initialized st, G_Initialized repr ->
    V.pts_to st.signing_pub_key repr.signing_pub_key_repr **
    V.pts_to st.session_transcript repr.transcript **
    pure (st.key_size == repr.key_size_repr)

  | Recv_no_sign_resp st vreq vresp, G_Recv_no_sign_resp repr sreq sresp ->
    V.pts_to st.signing_pub_key repr.signing_pub_key_repr **
    V.pts_to st.session_transcript repr.transcript **
    V.pts_to vreq sreq **
    V.pts_to vresp sresp **
    pure (st.key_size == repr.key_size_repr) 

  | _ -> pure False

//
// The main invariant
// The session_state_related connects the concrete state with the current ghost state of the trace.
// r is the trace pointer with permission
//

//r is the ghost ptr to trace t with full permission.
// state s and current state of trace t are session_state_related.

let spdm_inv (s:state) (r:gref) (t:trace) : slprop =
  ghost_pcm_pts_to r (Some 1.0R, t) **
  session_state_related s (current_state t)

let has_full_state_info (s:g_state) :prop =
  G_Recv_no_sign_resp? s \/ G_Recv_sign_resp? s \/ G_Initialized?s

  let g_transcript_of_gst (s:g_state {has_full_state_info s})
  : GTot g_transcript =
  match s with
  | G_Initialized r
  | G_Recv_no_sign_resp r _ _
  | G_Recv_sign_resp r _ _ -> r.transcript

  let g_key_of_gst (s:g_state {has_full_state_info s})
  : GTot (Seq.seq u8) =
  match s with
  | G_Initialized r
  | G_Recv_no_sign_resp r _ _
  | G_Recv_sign_resp r _ _ -> r.signing_pub_key_repr

let g_key_len_of_gst (s:g_state {has_full_state_info s})
  : GTot u32 =
  match s with
  | G_Initialized r
  | G_Recv_no_sign_resp r _ _
  | G_Recv_sign_resp r _ _ -> r.key_size_repr

let current_transcript (t:trace {has_full_state_info (current_state t) }) : GTot g_transcript =
  g_transcript_of_gst (current_state t)

let current_key (t:trace { has_full_state_info (current_state t) }) : GTot (Ghost.erased(Seq.seq u8)) =
  g_key_of_gst (current_state t)

let current_key_size (t:trace { has_full_state_info (current_state t) }) : GTot (Ghost.erased u32) =
  g_key_len_of_gst (current_state t)

let get_state_data (c:state) : st =
 match c with
 | Initialized s -> s
 | Recv_no_sign_resp s _ _ -> s

let init_inv (key_len:u32) (b:Seq.seq u8) (s:state) : slprop =
  exists* (t:trace).
    spdm_inv s (get_state_data s).g_trace_ref t ** 
    pure (G_Initialized? (current_state t) /\
          g_key_of_gst (current_state t) == b /\
          g_key_len_of_gst (current_state t) == key_len)

 val init0 (key_size:u32) (signing_pub_key:V.vec u8 { V.length signing_pub_key == U32.v key_size }) (#s:Seq.seq u8)
   : stt (state)
    (requires V.pts_to signing_pub_key s)
    (ensures fun res -> init_inv key_size s res)
noeq
type parser_context = {
  req_param1 : u8;
  req_param2 : u8;
  resp_size : u32;
  req_context : s:Seq.seq u8{Seq.length s == 8};
  resp : v:V.vec u8 { V.length v == u32_v resp_size};
  m_spec : u8
}

let measurement_size_select (measurement_specification:u8) (measurement_size:u16) (dmtf_spec_measurement_value_size:u16)
        : u16 =
  let last_bit_m = U8.logand measurement_specification 1uy in
  if (u8_v last_bit_m = 1) then
    dmtf_spec_measurement_value_size
  else
    measurement_size

    noeq
type spdm_measurement_block_t  = {
  index : u8 ;
  measurement_specification : u8;
  measurement_size : u16;
  dmtf_spec_measurement_value_type : u8;
  dmtf_spec_measurement_value_size : u16;
  measurement : v:V.vec u8{V.length v == 
                                u16_v(measurement_size_select measurement_specification 
                                                                      measurement_size 
                                                                      dmtf_spec_measurement_value_size) }
}

let index_req_param2_relation (i:u8) (r:u8) : prop =
  if (u8_v r = 0x1 || u8_v r = 0xFE) then
   (i == r)
  else
   True

type measurement_block_repr (ctx:parser_context) = {
  index : i:u8 {index_req_param2_relation i ctx.req_param2};
  measurement_specification : m:u8{m == ctx.m_spec} ;
  measurement_size : u16;
  dmtf_spec_measurement_value_type : u8;
  dmtf_spec_measurement_value_size : u16;
  measurement : s:Seq.seq u8{Seq.length s == 
                                u16_v(measurement_size_select measurement_specification 
                                                                      measurement_size 
                                                                      dmtf_spec_measurement_value_size) }
}

let measurement_block_repr_related (ctx:parser_context) 
                                   (s:spdm_measurement_block_t) 
                                   (r:measurement_block_repr ctx) : slprop =
 V.pts_to s.measurement r.measurement

let read_measurement_record_length_seq (l:Seq.seq u8{Seq.length l == 3})
      : (u32) =  // TODO: this is a spec only function, why don't return just nat here
  let index0 = Seq.index l 0 in
  let index1 = Seq.index l 1 in
  let index2 = Seq.index l 2 in
  let index_0_nat = u8_v index0 in
  let index_1_nat = u8_v index1 in
  let index_2_nat = u8_v index2 in
  let index_0_uint32 = U32.uint_to_t index_0_nat in
  let index_1_uint32 = U32.uint_to_t index_1_nat in
  let index_2_uint32 = U32.uint_to_t index_2_nat in
  
  let l2 = U32.shift_left index_2_uint32 16ul in
  let l1 = U32.shift_left index_2_uint32 8ul in
  let length = U32.logor (U32.logor index_0_uint32 l1) l2 in
  length

let num_blocks_param2_relation (n:u8) (r:u8): u8 =
  if r = 0uy then 0uy else n

let measurement_record_length_param2_relation (l:u32) (r:u8): u32 =
  if r = 0uy then 0ul else l

let signature_length_param1_relation (l:nat) (r:u8): nat =
  if r = 0uy then 0 else l

noeq
type resp_repr (ctx:parser_context) = {
  spdm_version : u8;
  request_response_code : r:u8{u8_v r == 0x60};
  param1 : u8;
  param2 : u8;//TODO param2 relation to be added
  number_of_blocks : n:u8{n == num_blocks_param2_relation n ctx.req_param2}; 
  measurement_record_length: m:Seq.seq u8{Seq.length m == 3 /\
                                          read_measurement_record_length_seq m == 
                                          measurement_record_length_param2_relation (read_measurement_record_length_seq m) ctx.req_param2}; 
  measurement_record : v:Seq.seq (measurement_block_repr ctx)
                       {Seq.length v == u32_v (read_measurement_record_length_seq measurement_record_length)};
  nonce: n:Seq.seq u8 {Seq.length n == 32};
  opaque_data_length : o:u16{u16_v o <= 1024}; 
  opaque_data : o:Seq.seq u8 { Seq.length o == u16_v opaque_data_length};
  requester_context : r:Seq.seq u8 { Seq.length r == spdm_req_context_size /\ r == ctx.req_context};
  signature : s:Seq.seq u8 {Seq.length s == signature_size /\
                            Seq.length s == signature_length_param1_relation (Seq.length s) ctx.req_param1}  // TODO: relation to param1
}

val b_resp_resp_repr_relation (ctx:parser_context)
                              (r:resp_repr ctx) 
                              (s:Seq.seq u8) : prop
  

//
// Related to parser
//
let valid_resp (ctx:parser_context)
               (repr:resp_repr ctx)  : slprop =
 exists* p_resp b_resp.
   V.pts_to ctx.resp #p_resp b_resp **
   pure (b_resp_resp_repr_relation ctx repr b_resp) 

type result =
  | Success
  | Parse_error
  

//
//Measurement block structure
//

let res_err_no_measurement (count:u8) (status:result) =
  match status with
  | Success -> true
  | Parse_error -> u8_v count = 0
  

//
//result structure
//
noeq
type spdm_measurement_result_t  = {
  measurement_block_count : u8;
  measurement_block_vector : v:V.vec spdm_measurement_block_t {
    V.length v == u8_v measurement_block_count
  };
  sign: s:V.vec u8{V.length s == signature_size};
  status : r:result{res_err_no_measurement measurement_block_count r}
}

noeq
type spdm_measurement_result_repr = {
  measurement_block_count : u8;
  measurement_block_seq : v:Seq.seq spdm_measurement_block_t {
    Seq.length v == u8_v measurement_block_count
  };
  sign_repr: s:Seq.seq u8{Seq.length s == signature_size};
  status : r:result{res_err_no_measurement measurement_block_count r}

}

let spdm_measurement_result_related (s:spdm_measurement_result_t) 
                                    (r:spdm_measurement_result_repr) : slprop =
  V.pts_to s.sign r.sign_repr


let valid_measurement_block_repr (ctx:parser_context)
                                 (blk:spdm_measurement_block_t) 
                                 (repr:measurement_block_repr ctx) : slprop =
  measurement_block_repr_related ctx blk repr **
  pure (blk.index ==  repr.index /\
        blk. measurement_specification == repr.measurement_specification /\
        blk.dmtf_spec_measurement_value_type == repr.dmtf_spec_measurement_value_type /\
        blk.dmtf_spec_measurement_value_size == repr.dmtf_spec_measurement_value_size)

module SZ = FStar.SizeT

let aux (ctx:parser_context)
        (blk:Seq.seq spdm_measurement_block_t) 
        (repr:Seq.seq (measurement_block_repr ctx))
        (i:nat)  : slprop =
 if (i < Seq.length blk && i < Seq.length repr) then
   valid_measurement_block_repr ctx (Seq.index blk i) (Seq.index repr i)
 else
  emp

let valid_measurement_blocks (ctx:parser_context)
                             (blks:V.vec spdm_measurement_block_t) 
                             (repr:Seq.seq (measurement_block_repr ctx))
                      : slprop =
  pure(V.length blks == Seq.length repr) **
  (exists* s. V.pts_to blks s **
  (O.on_range (aux ctx s repr) 0 (V.length blks))) 


module C = Pulse.Lib.Core 
//
//Signature for parser
//

let parser_post (ctx:parser_context) (res:spdm_measurement_result_t)
                 (#b_resp: G.erased (Seq.seq u8)) =
  match res.status with
  | Parse_error -> pure True
  | Success ->
    exists* resp_repr. valid_resp ctx resp_repr **
                       valid_measurement_blocks ctx res.measurement_block_vector resp_repr.measurement_record

let parser_success_post (ctx:parser_context) (res:spdm_measurement_result_t)
                       (is_sign_resp:bool) =
   if is_sign_resp then 
    (
      exists* resp_repr. valid_resp ctx resp_repr **
              valid_measurement_blocks ctx 
              res.measurement_block_vector 
              resp_repr.measurement_record **
              V.pts_to res.sign resp_repr.signature **
              pure (V.length res.sign == signature_size /\
                     V.length res.sign <> 0) 
                                                           
    )
    else
    (
      exists* resp_repr. valid_resp ctx resp_repr **
                         valid_measurement_blocks ctx (res.measurement_block_vector) (resp_repr.measurement_record)
    )

let parser_post1 (ctx:parser_context) (res:spdm_measurement_result_t)
                 (is_sign_resp:bool) =
  match res.status with
  | Parse_error -> pure True
  
  | Success ->     parser_success_post ctx res is_sign_resp                 
                               
val parser 
(ctx:parser_context)
(#p:perm)
(#b_resp: G.erased (Seq.seq u8))
(with_sign:bool)
  : stt (spdm_measurement_result_t)
    (requires V.pts_to ctx.resp #p b_resp)
    (ensures fun res -> V.pts_to ctx.resp #p b_resp **
                        parser_post1 ctx res with_sign)

let state_change_success_no_sign (tr0:trace)
                                 (tr1:trace)
                     : prop =
   (G_Recv_no_sign_resp? (current_state tr1)) /\
   (valid_transition tr0 (current_state tr1)) /\ (tr1 == next_trace tr0 (current_state tr1)) /\
   (G_Recv_no_sign_resp? (current_state tr1))

let hash_result_success_no_sign (tr0:trace{has_full_state_info (current_state tr0)}) 
                                (tr1:trace{has_full_state_info (current_state tr1) /\
                                        has_full_state_info (previous_current_state tr1)})
                                (#b_resp: Seq.seq u8{Seq.length b_resp > 0 /\ (UInt.fits (Seq.length b_resp) U32.n)})
                                (#b_req: Seq.seq u8{Seq.length b_req > 0 /\ (UInt.fits (Seq.length b_req) U32.n)}) 
                     : prop =
  (exists hash_algo. 
                  hash_of hash_algo (current_transcript tr0)  
                  b_req 
                  b_resp 
                  (current_transcript tr1))

fn no_sign_resp1
  (ctx:parser_context)
  (req_size: u32{u32_v req_size > 0})
  (req:V.vec u8 { V.length req == u32_v req_size })
  (c:state)
  (#tr0:trace{has_full_state_info (current_state tr0)})
  (#b_resp: G.erased (Seq.seq u8){u32_v ctx.resp_size > 0 /\ Seq.length b_resp == u32_v ctx.resp_size})
  (#b_req: G.erased (Seq.seq u8){Seq.length b_req == u32_v req_size})
  (#p_req : perm)
  (#p_resp:perm)
  
  requires (V.pts_to req #p_req b_req **
             V.pts_to ctx.resp #p_resp b_resp) **
             spdm_inv c ((get_state_data c).g_trace_ref) tr0 **
             pure (G_Recv_no_sign_resp? (current_state tr0) \/ G_Initialized? (current_state tr0))
   
   returns res: (spdm_measurement_result_t & state)

   ensures V.pts_to req #p_req b_req **
            V.pts_to ctx.resp #p_resp b_resp **

            //parser related post-conditions
            parser_post1 ctx (fst res) false  **
           
            //state change related post-condition 
            (exists* tr1.
                  spdm_inv (snd res) (get_state_data (snd res)).g_trace_ref tr1 **
                  pure ((fst res).status == Success ==>
                                      state_change_success_no_sign tr0 tr1 /\
                                      hash_result_success_no_sign tr0 tr1 #b_resp #b_req ))


val reset
  (c:state)
  (#tr0:trace {has_full_state_info(current_state tr0) })
   : stt state
  (requires (spdm_inv c ((get_state_data c).g_trace_ref) tr0 **
           pure (G_Recv_no_sign_resp? (current_state tr0))))
                      
  (ensures fun r -> init_inv (get_state_data c).key_size (current_key tr0) r)

  let valid_signature (signature msg key:Seq.seq u8):prop = admit()

val 
 verify_sign 
         (ts_digest: V.vec u8{V.length ts_digest == hash_size})
         (sg: V.vec u8{V.length sg == signature_size})
         (pub_key:V.vec u8)
         (#ts_seq: (G.erased (Seq.seq u8)){Seq.length ts_seq == hash_size})
         (#sg_seq:(G.erased (Seq.seq u8)){Seq.length sg_seq == signature_size})
         (#p_seq:(G.erased (Seq.seq u8)))
  : stt bool
    (requires V.pts_to ts_digest ts_seq **
             V.pts_to sg sg_seq **
             V.pts_to pub_key p_seq)
    
    (ensures fun res -> (V.pts_to ts_digest ts_seq **
             V.pts_to sg sg_seq **
             V.pts_to pub_key p_seq **
             pure( res == true ==> valid_signature sg_seq ts_seq p_seq)))

noextract
let next_next_trace (t:trace) 
                    (s1:g_state { valid_transition t s1 }) 
                    (s2:g_state { valid_transition ((next_trace t s1)) s2 }) : trace =
 next_trace (next_trace t s1) s2

let g_seq_transcript : g_transcript =
  Seq.create hash_size 0uy

let hash_result_success_sign1 (tr0:trace{has_full_state_info (current_state tr0)}) 
                             (tr1:trace{has_full_state_info (current_state tr1) /\
                                        has_full_state_info (previous_current_state tr1)})
                             (#b_resp: Seq.seq u8{Seq.length b_resp > 0 /\ (UInt.fits (Seq.length b_resp) U32.n)})
                             (#b_req: Seq.seq u8{Seq.length b_req > 0 /\ (UInt.fits (Seq.length b_req) U32.n)}) 
                     : prop =
  (exists hash_algo. 
                hash_of hash_algo (current_transcript tr0) 
                 b_req 
                 b_resp 
                (g_transcript_of_gst (previous_current_state tr1))) 


let transition_related_sign_success (tr0:trace{has_full_state_info (current_state tr0)}) 
                                    (tr1:trace{has_full_state_info (current_state tr1)})
                  : prop =
  valid_transition tr0 (previous_current_state tr1 ) /\
  tr1 == next_next_trace tr0 (previous_current_state tr1 ) (current_state tr1)


#restart-solver

noeq
type sign_resp_result  = {
  parser_result: spdm_measurement_result_t ;
  curr_state : state;
  sign_status : bool
}

let valid_signature_exists 
 (ctx:parser_context)
 (tr1:trace{has_full_state_info (current_state tr1) /\
            has_full_state_info (previous_current_state tr1)}) : prop =
    (exists (resp_rep:resp_repr ctx).
        valid_signature resp_rep.signature 
        (g_transcript_of_gst (previous_current_state tr1)) 
        (g_key_of_gst (previous_current_state tr1)))

let state_change_success_sign1 (tr1:trace)
                     : prop =
   ((G_Initialized? (current_state tr1)) /\
    (current_transcript tr1 == g_seq_transcript) /\
    G_Recv_sign_resp?(previous_current_state tr1))

fn
sign_resp1
  (ctx:parser_context)
  (req_size: u32{u32_v req_size > 0})
  (req:V.vec u8 { V.length req == u32_v req_size })
  (c:state)
  (#tr0:trace {has_full_state_info (current_state tr0) })
  (#b_resp: Seq.seq u8{Seq.length b_resp > 0 /\ Seq.length b_resp == u32_v ctx.resp_size /\
                       (UInt.fits (Seq.length b_resp) U32.n)})
  (#b_req: Seq.seq u8{Seq.length b_req > 0 /\ Seq.length b_req == u32_v req_size /\
                      (UInt.fits (Seq.length b_req) U32.n)}) 
  (#p_req : perm)
  (#p_resp:perm)

   requires (V.pts_to req #p_req b_req **
             V.pts_to ctx.resp #p_resp b_resp) **
             spdm_inv c ((get_state_data c).g_trace_ref) tr0 **
             pure (G_Recv_no_sign_resp? (current_state tr0) \/ G_Initialized? (current_state tr0))
   returns res: sign_resp_result
   
   ensures (V.pts_to req #p_req b_req **
            V.pts_to ctx.resp #p_resp b_resp **
            parser_post1 ctx res.parser_result true **
            (exists* tr1.
                  spdm_inv res.curr_state (get_state_data (res.curr_state)).g_trace_ref tr1 **
                  pure (res.parser_result.status == Success ==>
                                  state_change_success_sign1 tr1 /\ 
                                  hash_result_success_sign1 tr0 tr1 #b_resp #b_req /\
                                  transition_related_sign_success tr0 tr1 /\
                                  (res.sign_status == true ==> valid_signature_exists ctx tr1)
              )))
