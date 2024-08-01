module SPDM3
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

open FStar.Mul
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

let trace_ref = admit ()

let pcm_elt (p:perm) (t:trace) : pcm_t = Some p, t

fn init0 (key_size:u32) (signing_pub_key:V.vec u8 { V.length signing_pub_key == U32.v key_size })
  (#s:Seq.seq u8)
  requires V.pts_to signing_pub_key s
  returns r:state & gref
  ensures init_inv key_size s (fst r) (snd r)
{
  //creation of session_transcript
  let session_transcript = V.alloc 0uy 0sz;
  
  //creation of the session data storage
  let st = { key_size; signing_pub_key; session_transcript };
  
  //creation of the ghost session data storage
  let repr = {key_size_repr = key_size; signing_pub_key_repr = s; transcript = Seq.empty};
  
  //creation of the trace
  let trace = next_trace emp_trace (G_Initialized repr);
  
  //creation of the ghost trace ref
  let r = ghost_alloc #_ #trace_pcm (pcm_elt 1.0R trace);
 
  (*Current context:
    ghost_pcm_pts_to r (G.reveal (G.hide (pcm_elt 1.0R trace))) **
    V.pts_to session_transcript (Seq.Base.create (SZ.v 0sz) 0uy) **
    V.pts_to signing_pub_key s*)
  
  (*We get, V.pts_to signing_pub_key s from the pre-condition. To prove session_related, we need to rewrite signing_pub_key as 
    st.signing_pub_key and s as repr.signing_pub_key_repr, where rewrite works as these entities are equal*)
  rewrite each
    signing_pub_key as st.signing_pub_key,
    s as repr.signing_pub_key_repr;

   (*Current context:
    ghost_pcm_pts_to r (G.reveal (G.hide (pcm_elt 1.0R trace))) **
    V.pts_to session_transcript (Seq.Base.create (SZ.v 0sz) 0uy) **
    V.pts_to st.signing_pub_key repr.signing_pub_key_repr*)

  (*pure things are asserted with assert_*)
  assert_ (pure (Seq.equal (Seq.create (SZ.v 0sz) 0uy) Seq.empty));

  (*Here, rewrite is for entire V.pts_to, hence use with _v., where _v indicates the seq equivalent of the vector*)
  with _v. rewrite (V.pts_to session_transcript _v) as
                   (V.pts_to st.session_transcript Seq.empty);

   (*Current context:
    ghost_pcm_pts_to r (pcm_elt 1.0R trace) **
    V.pts_to st.session_transcript Seq.Base.empty **
    V.pts_to st.signing_pub_key repr.signing_pub_key_repr*)
  
  (*fold with exact values. Otherwise a match block might need to be invoked.*)
  fold (session_state_related (Initialized st) (G_Initialized repr));

  (*Current context:
    ghost_pcm_pts_to r (pcm_elt 1.0R trace) **
    session_state_related (Initialized st) (G_Initialized repr)*)
  
  (*Since all the conditions for spdm_inv are in the context now, fold spdm_inv*)
  fold (spdm_inv (Initialized st) r trace);

   (*Current context:
    spdm_inv (Initialized st) r trace*)

  let res = (Initialized st, r);

  (*Current context:
    pure (res == (Initialized st, r)) ** spdm_inv (Initialized st) r trace*)

  fold (init_inv key_size s (fst res) (snd res));

  (*Current context:
    init_inv key_size s (fst res) (snd res)*)

  res
}

let b_resp_resp_repr_relation (req_param1: u8)
                              (req_param2:u8) (measurementspecification: u8) 
                              (req_context: Seq.seq u8{Seq.length req_context == 8})
                              (r:resp_repr req_param1 req_param2 measurementspecification req_context) (s:Seq.seq u8) =

admit()

let valid_resp_bytes (req_param1: u8)
                            (req_param2:u8) (measurementspecification: u8) 
                            (req_context: Seq.seq u8{Seq.length req_context == 8})
                            (b:Seq.seq u8) 
                            (r:resp_repr req_param1 req_param2 measurementspecification req_context) =
admit()

type parser_context = {
  req_param1 : u8;
  req_param2 : u8;
  req_context0 : u8;
  req_context1 : u8;
  req_context2 : u8;
  m_spec : u8
}

assume val resp_repr0 (ctx:parser_context) : Type0
assume val valid_resp_bytes0 (ctx:parser_context) (s:Seq.seq u8) (r:resp_repr0 ctx) : slprop
assume val blocks_of_resp_repr (#ctx:parser_context) (r:resp_repr0 ctx)
  : GTot (Seq.seq (measurement_block_repr ctx.req_param2 ctx.m_spec))
assume val valid_measurement_blocks0
  (ctx:parser_context)
  (s:Seq.seq (measurement_block_repr ctx.req_param2 ctx.m_spec)) : slprop

let parser_post (ctx:parser_context) (s:Seq.seq u8) (res:spdm_measurement_result_t) =
  match res.status with
  | Parse_error -> pure True
  | Signature_verification_error -> pure False
  | Success ->
    exists* (r:resp_repr0 ctx).
    valid_resp_bytes0 ctx s r **
    valid_measurement_blocks0 ctx (blocks_of_resp_repr r)

fn parser0
  (ctx:parser_context)
  (resp_size: u32)
  (resp:V.vec u8 { V.length resp == u32_v resp_size })
  (#p:perm)
  (#s:Ghost.erased (Seq.seq u8))
    
  requires V.pts_to resp #p s
  returns res:spdm_measurement_result_t
  ensures 
    V.pts_to resp #p s **
    parser_post ctx s res
{
  admit ()
}


let get_state_data (c:state) =
  match c with
  | Initialized s -> s
  | Recv_no_sign_resp s -> s

let get_state_data_transcript (s_data:st) = s_data.session_transcript

let get_state_data_signing_pub_key (s_data:st) = s_data.signing_pub_key

let get_state_data_key_size (s_data:st) = s_data.key_size

//We have taken permissions on v1 and v2 and if we are not returning v1 nad v2, then the client losts this permission and then
//the client will not be able to deallocate v1 and v2. Read permissions.
fn append_vec
  (#a:Type0)
  (v1: V.vec a)
  (v2: V.vec a)
  (#p1:perm)
  (#p2:perm)
  (#v1_seq: Ghost.erased (Seq.seq a)) //put G.erased
  (#v2_seq: Ghost.erased (Seq.seq a))
  
  requires V.pts_to v1 #p1 v1_seq **
           V.pts_to v2 #p2 v2_seq
  returns v:V.vec a
  ensures V.pts_to v (Seq.append v1_seq v2_seq) **
          V.pts_to v1 #p1 v1_seq **
          V.pts_to v2 #p2 v2_seq
  {
    admit()
  }      

#push-options "--query_stats"

// (pure ((G_Recv_no_sign_resp? (current_state tr1) /\
//                                                  valid_transition tr0 (current_state tr1) /\ tr1 == next_trace tr0 (current_state tr1)) /\
//                                                  (G_Recv_no_sign_resp? (current_state tr1) /\
                                               
//                                                   g_transcript_current_session_grows_by (current_transcript tr0 ) 
//                                                                                      (current_transcript tr1) 
//                                                                                      (Seq.append b_req b_resp))))
assume val valid_trace_for_no_sign_resp (tr0 tr1:trace) : prop

fn no_sign_resp1
  (ctx:parser_context)
  (req_size: u32)
  (resp_size: u32)
  (req:V.vec u8 { V.length req == u32_v req_size })
  (resp:V.vec u8 { V.length resp == u32_v resp_size })
  (c:state)
  (#tr0:trace{has_full_state_info (current_state tr0)})
  (#p_req:perm)
  (#p_resp:perm)
  (#b_resp:G.erased (Seq.seq u8))
  (#b_req:G.erased (Seq.seq u8))
  
  requires V.pts_to req #p_req b_req **
           V.pts_to resp #p_resp b_resp **
           spdm_inv c trace_ref tr0 **
           pure (G_Recv_no_sign_resp? (current_state tr0) \/ G_Initialized? (current_state tr0))
  
  returns res:spdm_measurement_result_t & state
    
  ensures V.pts_to req #p_req b_req **
          V.pts_to resp #p_resp b_resp **
          (match (fst res).status with
           | Parse_error -> pure True
           | Signature_verification_error -> pure False
           | Success ->
             //parser post-condition 
             (exists* r. valid_resp_bytes0 ctx b_resp r **
                         valid_measurement_blocks0 ctx (blocks_of_resp_repr r)) **
                              
             //state change related post-condition 
             (exists* tr1. spdm_inv c trace_ref tr1 **
                           pure (valid_trace_for_no_sign_resp tr0 tr1)))
                                         

{
  let res = parser0 ctx resp_size resp;

  match res.status {
    Parse_error -> {
      admit ()
    }
    Signature_verification_error -> {
      rewrite (parser_post ctx b_resp res) as
              (pure False);
      unreachable ()
    }
    Success -> {
      admit ()
    }
  }

  // //current state transcript
  // let curr_state_data = get_state_data c;
  // let curr_state_transcript = get_state_data_transcript curr_state_data;
  // let curr_state_signing_pub_key = get_state_data_signing_pub_key curr_state_data;
  // let curr_state_key_size = get_state_data_key_size curr_state_data;

  
  // //append req and resp
  // let append_req_resp = append_vec req resp #b_req #b_resp #p_req #p_resp;
  
  // //get the ghost transcript
  // let curr_g_transcript = current_transcript tr0;
  // let curr_g_key = current_key tr0;
  // let curr_g_key_size = current_key_size tr0;
  // //unfold (spdm_inv c trace_ref tr0);
  
  // //unfold (session_state_related c (current_state tr0));

  // assume_(V.pts_to curr_state_transcript (G.reveal curr_g_transcript));
  // //append req/resp to the current trascript
  // let new_transcript = append_vec curr_state_transcript append_req_resp #curr_g_transcript #(Seq.append b_req b_resp);
  // let new_g_transcript = g_append curr_g_transcript (Seq.append b_req b_resp);
  // //create a new state data record with the new transcript
  // assume_ (pure (V.length curr_state_signing_pub_key == u32_v curr_state_key_size));

  // let new_st = {key_size = curr_state_key_size; signing_pub_key = curr_state_signing_pub_key; session_transcript = new_transcript };
  
  // ////creation of the ghost session data storage
  // let repr = {key_size_repr = curr_g_key_size; signing_pub_key_repr = curr_g_key; transcript = new_g_transcript};

  // //Do the state change
  // let new_state = (Recv_no_sign_resp new_st);
  
  // assume_ (pure (g_transcript_non_empty repr.transcript));
  // assume_ (pure (valid_transition tr0 (G_Recv_no_sign_resp repr)));
  // let tr1 = next_trace tr0 (G_Recv_no_sign_resp repr);
  
  // assert (pure (G_Recv_no_sign_resp? (current_state tr1)));
  // assert (pure (valid_transition tr0 (current_state tr1)));
  // assert (pure (tr1 == next_trace tr0 (current_state tr1)));
  // assert (pure(g_transcript_current_session_grows_by (current_transcript tr0 ) 
  //                                               (current_transcript tr1) 
  //                                               (Seq.append b_req b_resp)));
  // //Call parser to parse and get the measurement blocks.

  // let parser_res = parser req_param1 req_param2 resp_size m_spec req_context resp;

  // let parser_res_result = parser_res.status;
  // let parser_res_measurement_block_count = parser_res.measurement_block_count;
  // let parser_res_measurement_block_vector = parser_res.measurement_block_vector;
  // match parser_res_result {
  //   Parse_error -> {
      
  //     admit() //(parser_res,new_state)
  //   }
  //   Signature_verification_error -> {
     
  //     admit()//unreachable ()
  //   }
  //   Success -> {
  //     admit()
  //   }
  
  // }
}

fn no_sign_resp3
  (req_param1: u8)
  (req_param2 : u8)
  (m_spec: u8) 
  (req_context: Seq.seq u8{Seq.length req_context == 8})
  (req_size: u32)
  (resp_size: u32)
  (req:V.vec u8 { V.length req == u32_v req_size })
  (resp:V.vec u8 { V.length resp == u32_v resp_size })
  (c:state)
  (#tr0:trace{has_full_state_info (current_state tr0)})
  (#b_resp: Seq.seq u8)
  (#b_req: Seq.seq u8)
  (#p_req : perm)
  (#p_resp:perm)
   requires (V.pts_to req #p_req b_req **
             V.pts_to resp #p_resp b_resp) **
             spdm_inv c trace_ref tr0 **
             pure (G_Recv_no_sign_resp? (current_state tr0) \/ G_Initialized? (current_state tr0))
    returns res: spdm_measurement_result_t & state
    
    ensures V.pts_to req #p_req b_req **
            V.pts_to resp #p_resp b_resp **
            (let measurement_block_count = (fst res).measurement_block_count in
            let result = (fst res).status in
                  (match result with
                    | Parse_error -> pure True
                    | Signature_verification_error -> pure False
                    | Success ->
                              //parser post-condition 
                              (exists* resp_repr. valid_resp_bytes req_param1 req_param2 m_spec req_context b_resp resp_repr **
                                       valid_measurement_blocks req_param2 m_spec (fst res).measurement_block_vector resp_repr.measurement_record) **
                              
                              //state change related post-condition 
                              (exists* r tr1. valid_resp req_param1 req_param2 m_spec req_context resp r **
                                        spdm_inv c trace_ref tr1 **
                                         (pure ((G_Recv_no_sign_resp? (current_state tr1) /\
                                                 valid_transition tr0 (current_state tr1) /\ tr1 == next_trace tr0 (current_state tr1)) /\
                                                 (G_Recv_no_sign_resp? (current_state tr1) /\
                                               
                                                  g_transcript_current_session_grows_by (current_transcript tr0 ) 
                                                                                     (current_transcript tr1) 
                                                                                     (Seq.append b_req b_resp))))
)))
{
  
  assert_ (V.pts_to resp #p_resp b_resp);

  let parser_res = parser req_param1 req_param2 resp_size m_spec req_context resp;

  assert_ (V.pts_to resp #p_resp b_resp);

  let parser_res_result = parser_res.status;
  let parser_res_measurement_block_count = parser_res.measurement_block_count;
  let parser_res_measurement_block_vector = parser_res.measurement_block_vector;
  match parser_res_result {
    Parse_error -> {
      
      admit() //(parser_res,new_state)
    }
    Signature_verification_error -> {
     
      admit()
    }
    Success -> {
      //current state transcript
      let curr_state_data = get_state_data c;
      let curr_state_transcript = get_state_data_transcript curr_state_data;
      let curr_state_signing_pub_key = get_state_data_signing_pub_key curr_state_data;
      let curr_state_key_size = get_state_data_key_size curr_state_data;


      
      (*current context here, 
       Current context:
         V.pts_to req b_req **
         V.pts_to resp (G.reveal b_resp) **
         spdm_inv c trace_ref tr0 ***)
      
      (*In the original pre-condition, 
          V.pts_to resp #p_resp b_resp*)
      
      (*in the parser post-condition,
         V.pts_to resp #p_resp b_resp*)

      (*The assert is failing as well as why the parser post condition is not holding?*)
      //assert_ (V.pts_to resp #p_resp b_resp);
      
      //append req and resp
      (*let append_req_resp = append_vec req resp #b_req #b_resp #p_req #p_resp;
  
      //get the ghost transcript
      let curr_g_transcript = current_transcript tr0;
      let curr_g_key = current_key tr0;
      let curr_g_key_size = current_key_size tr0;
      //unfold (spdm_inv c trace_ref tr0);
  
      //unfold (session_state_related c (current_state tr0));

      assume_(V.pts_to curr_state_transcript (G.reveal curr_g_transcript));
      //append req/resp to the current trascript
      let new_transcript = append_vec curr_state_transcript append_req_resp #curr_g_transcript #(Seq.append b_req b_resp);
      let new_g_transcript = g_append curr_g_transcript (Seq.append b_req b_resp);
      //create a new state data record with the new transcript
      assume_ (pure (V.length curr_state_signing_pub_key == u32_v curr_state_key_size));

      let new_st = {key_size = curr_state_key_size; signing_pub_key = curr_state_signing_pub_key; session_transcript = new_transcript };
  
      ////creation of the ghost session data storage
      let repr = {key_size_repr = curr_g_key_size; signing_pub_key_repr = curr_g_key; transcript = new_g_transcript};

      //Do the state change
      let new_state = (Recv_no_sign_resp new_st);
  
      assume_ (pure (g_transcript_non_empty repr.transcript));
      assume_ (pure (valid_transition tr0 (G_Recv_no_sign_resp repr)));
      let tr1 = next_trace tr0 (G_Recv_no_sign_resp repr);
  
      assert (pure (G_Recv_no_sign_resp? (current_state tr1)));
      assert (pure (valid_transition tr0 (current_state tr1)));
      assert (pure (tr1 == next_trace tr0 (current_state tr1)));
      assert (pure(g_transcript_current_session_grows_by (current_transcript tr0 ) 
                                                (current_transcript tr1) 
                                                (Seq.append b_req b_resp)));*)
  
      admit()
    }
  
  }
}


