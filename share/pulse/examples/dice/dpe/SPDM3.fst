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


let pcm_elt (p:perm) (t:trace) : pcm_t = Some p, t

fn init0 (key_size:u32) (signing_pub_key:V.vec u8 { V.length signing_pub_key == U32.v key_size })
  (#s:Seq.seq u8)
  requires V.pts_to signing_pub_key s
  returns r:state 
  ensures init_inv key_size s r
{
  //creation of session_transcript
  let session_transcript = V.alloc 0uy 0sz;
  
  //creation of the ghost session data storage
  let repr = {key_size_repr = key_size; signing_pub_key_repr = s; transcript = Seq.empty};

  //creation of the trace
  let trace = next_trace emp_trace (G_Initialized repr);

  //creation of the ghost trace ref
  let r = ghost_alloc #_ #trace_pcm (pcm_elt 1.0R trace);

  //creation of the session data storage
  let st = { key_size; signing_pub_key; session_transcript;g_trace_ref = r };
  
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

  let res = Initialized st;

  (*Current context:
    pure (res == (Initialized st, r)) ** spdm_inv (Initialized st) r trace*)

  fold (init_inv key_size s (Initialized st));

  (*Current context:
    init_inv key_size s (fst res) (snd res)*)

  res
}

let b_resp_resp_repr_relation (ctx:parser_context)
                              (r:resp_repr ctx) 
                              (s:Seq.seq u8) =

admit()

let valid_resp_bytes (ctx:parser_context)
                     (b:Seq.seq u8) 
                     (r:resp_repr ctx) =
admit()

fn parser0 
  (ctx:parser_context)
  (#p:perm)
  (#b_resp: G.erased (Seq.seq u8))

requires V.pts_to ctx.resp #p b_resp
returns res: spdm_measurement_result_t 
ensures 
         V.pts_to ctx.resp #p b_resp **
         parser_post ctx res #b_resp
{
  admit()
}

let get_state_data_transcript (s_data:st) : V.vec u8 = s_data.session_transcript

let get_state_data_signing_pub_key (s_data:st) : V.vec u8 = s_data.signing_pub_key

let get_state_data_key_size (s_data:st) : u32 = s_data.key_size


//We have taken permissions on v1 and v2 and if we are not returning v1 nad v2, then the client losts this permission and then
//the client will not be able to deallocate v1 and v2. Read permissions.
fn append_vec
  (#a:Type0)
  (v1: V.vec a)
  (v2: V.vec a)
  (#v1_seq: Ghost.erased (Seq.seq a)) //put G.erased
  (#v2_seq: Ghost.erased (Seq.seq a))
  (#p1:perm)
  (#p2:perm)
  
  requires V.pts_to v1 #p1 v1_seq **
           V.pts_to v2 #p2 v2_seq

  returns v:V.vec a
  ensures V.pts_to v (Seq.append v1_seq v2_seq) **
          V.pts_to v1 #p1 v1_seq **
          V.pts_to v2 #p2 v2_seq
  {
    admit()
  }      

fn parser 
(ctx:parser_context)
(#p:perm)
(#b_resp: G.erased (Seq.seq u8))  
requires V.pts_to ctx.resp #p b_resp
 returns res: spdm_measurement_result_t 
ensures V.pts_to ctx.resp #p b_resp **
                        parser_post ctx res #b_resp

{
  admit()
}

let no_sign_resp_state_related_post_conditions 
  (ctx:parser_context)
  (tr0:trace)
  (tr1:trace)
  (c:state)
  (res_state:state) 
  (#b_resp: Seq.seq u8)
  (#b_req: Seq.seq u8) 
  (res:spdm_measurement_result_t) :slprop =


pure (res.status == Success ==> (G_Recv_no_sign_resp? (current_state tr1) /\
valid_transition tr0 (current_state tr1) /\ tr1 == next_trace tr0 (current_state tr1)) /\
(G_Recv_no_sign_resp? (current_state tr1) /\
g_transcript_current_session_grows_by (current_transcript tr0 ) 
                                      (current_transcript tr1) 
                                      (Seq.append b_req b_resp)))

//
(*NOTES:*)
(*When we get an error, expected a function, check whether any of the function has insufficient number of arguments*)
(*only pure slprops are in smt context, no other slprop. This means smt needs additional rewrites to bring in the other slprop context*)
(*Whenever a vector is passed with explicit permission, ensure to return that vector with the passed in permission*)
//
#push-options "--print_implicits"

fn no_sign_resp1
  (ctx:parser_context)
  (req_size: u32)
  (req:V.vec u8 { V.length req == u32_v req_size })
  (c:state)
  (#tr0:trace{has_full_state_info (current_state tr0)})
  (#b_resp: G.erased (Seq.seq u8))
  (#b_req: Seq.seq u8)
  (#p_req : perm)
  (#p_resp:perm)
   requires (V.pts_to req #p_req b_req **
             V.pts_to ctx.resp #p_resp b_resp) **
             spdm_inv c ((get_state_data c).g_trace_ref) tr0 **
             pure (G_Recv_no_sign_resp? (current_state tr0) \/ G_Initialized? (current_state tr0))
    returns res: spdm_measurement_result_t & state
    
    ensures V.pts_to req #p_req b_req **
            V.pts_to ctx.resp #p_resp b_resp **

            //parser related post-conditions
            parser_post ctx (fst res) #b_resp **
           
            //state change related post-condition 
            (exists* tr1.
                     spdm_inv c (get_state_data (snd res)).g_trace_ref tr1 **
                     (*no_sign_resp_state_related_post_conditions ctx tr0 tr1 c (snd res) #b_resp #b_req (fst res)*)
                     pure ((fst res).status == Success ==> (G_Recv_no_sign_resp? (current_state tr1) /\
                            valid_transition tr0 (current_state tr1) /\ tr1 == next_trace tr0 (current_state tr1)) /\
                           (G_Recv_no_sign_resp? (current_state tr1) /\
                           g_transcript_current_session_grows_by (current_transcript tr0 ) 
                                      (current_transcript tr1) 
                                      (Seq.append b_req b_resp))))
{
  let res = parser0 ctx #p_resp #b_resp;
  match res.status {
    Parse_error -> {
      (*rewrite (parser_post ctx res #b_resp) as
              (pure True);*)
      
      let tr1 = tr0;
      let r = (get_state_data c).g_trace_ref;
      assert (spdm_inv c ((get_state_data c).g_trace_ref) tr0);
      assert (spdm_inv c (get_state_data c).g_trace_ref tr1);

      rewrite 
        (spdm_inv c ((get_state_data c).g_trace_ref) tr0) as
        (spdm_inv c (get_state_data c).g_trace_ref tr1);
      
      assert_ (pure (res.status == Success ==> (G_Recv_no_sign_resp? (current_state tr1) /\
               valid_transition tr0 (current_state tr1) /\ tr1 == next_trace tr0 (current_state tr1)) /\
              (G_Recv_no_sign_resp? (current_state tr1) /\
               g_transcript_current_session_grows_by (current_transcript tr0 ) 
                                      (current_transcript tr1) 
                                      (Seq.append b_req b_resp))));
      
      (*Comment*)
      (*If I write the condition explicitly, assert passes. How can I abstract the above conditions using 
            no_sign_resp_state_related_post_conditions*)
      //assert_ (no_sign_resp_state_related_post_conditions ctx tr0 tr1 c c #b_resp #b_req res);
     
      (*parser_post ctx res #b_resp is rewritten as pure True, then why the assert for parser_post ctx res #b_resp is not holding? *)
      rewrite (parser_post ctx res #b_resp) as
              (pure True);

      //show_proof_state;
      assert_ (parser_post ctx res #b_resp);
      (res,c)
    }
    (*spdm_inv c (get_state_data c).g_trace_ref tr0*)
    Signature_verification_error -> {
      rewrite (parser_post ctx res #b_resp) as
              (pure False);
      unreachable ()
    }
    Success -> {
      //Grow the transcript
      //---------------------------------------------------------------------------------------------------------------------------
      //current state transcript
      let curr_state_data = get_state_data c;
      let curr_state_transcript = get_state_data_transcript curr_state_data;
      let curr_state_signing_pub_key = get_state_data_signing_pub_key curr_state_data;
      let curr_state_key_size = get_state_data_key_size curr_state_data;
      
      //append req and resp
      let append_req_resp = append_vec req ctx.resp #b_req #b_resp #p_req #p_resp;
  
      //get the ghost transcript
      let curr_g_transcript = current_transcript tr0;
      let curr_g_key = current_key tr0;
      let curr_g_key_size = current_key_size tr0;
      
      assume_(V.pts_to curr_state_transcript (G.reveal curr_g_transcript));
      //append req/resp to the current trascript
      let new_transcript = append_vec curr_state_transcript append_req_resp #curr_g_transcript #(Seq.append b_req b_resp);
      
      let new_g_transcript = g_append curr_g_transcript (Seq.append b_req b_resp);
      //create a new state data record with the new transcript
      assume_ (pure (V.length curr_state_signing_pub_key == u32_v curr_state_key_size));
      
      //creation of the ghost session data storage
      let repr = {key_size_repr = curr_g_key_size; signing_pub_key_repr = curr_g_key; transcript = new_g_transcript};
      
      assume_ (pure(g_transcript_non_empty repr.transcript));
      assume_ (pure (valid_transition tr0 (G_Recv_no_sign_resp repr)));
      
      
      //Trace ref creation-----------------------------------------------------------------------------------------------------------
      //creation of the trace
      let trace = next_trace tr0 (G_Recv_no_sign_resp repr);
      
      //creation of the ghost trace ref
      let r = ghost_alloc #_ #trace_pcm (pcm_elt 1.0R trace);
      
      //New state data record creation
      //----------------------------------------------------------------------------------------------------------------------------
      let new_st = {key_size = curr_state_key_size; 
                    signing_pub_key = curr_state_signing_pub_key; 
                    session_transcript = new_transcript;
                    g_trace_ref = r};

      //Do the state change---------------------------------------------------------------------------------------------------------
      let new_state = (Recv_no_sign_resp new_st);
  
      assume_ (pure (g_transcript_non_empty repr.transcript));
      assume_ (pure (valid_transition tr0 (G_Recv_no_sign_resp repr)));
      
      //new trace----------------------------------------------------------------------------------------------------------------
      let tr1 = next_trace tr0 (G_Recv_no_sign_resp repr);
  
      assert (pure (G_Recv_no_sign_resp? (current_state tr1)));
      assert (pure (valid_transition tr0 (current_state tr1)));
      assert (pure (tr1 == next_trace tr0 (current_state tr1)));
      assert (pure(g_transcript_current_session_grows_by (current_transcript tr0 ) 
                                                (current_transcript tr1) 
                                                (Seq.append b_req b_resp)));

      admit ()
    }
}
}
(* (*assume_ (exists* r tr1. no_sign_resp_state_related_post_conditions ctx r tr0 tr1 c c #b_resp #b_req **
                              valid_resp0 ctx r **
                              spdm_inv c (get_state_data c).g_trace_ref tr1);
      *)