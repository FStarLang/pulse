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

open FStar.Mul
open Pulse.Lib.Pervasives

module G = FStar.Ghost
module PCM = FStar.PCM
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module PP = PulseCore.Preorder
module PM = Pulse.Lib.PCMMap

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference


open PulseCore.Preorder
open Pulse.Lib.OnRange

fn
hash (hash_algo: u32)
         (ts_digest: V.vec u8{V.length ts_digest == hash_size})
         (msg_size: u32{u32_v msg_size > 0})
         (msg: V.vec u8{V.length msg == u32_v msg_size})
         (#ts_seq: (G.erased (Seq.seq u8))(*{Seq.length ts_seq == hash_size}*))
         (#msg_seq: (G.erased (Seq.seq u8)))
         (#p_msg:perm)
        
requires V.pts_to ts_digest ts_seq **
                  V.pts_to msg #p_msg msg_seq

ensures V.pts_to msg #p_msg msg_seq **
        V.pts_to ts_digest (hash_spec hash_algo ts_seq msg_seq) 
{
  admit()
}

fn init0 (key_size:u32) (signing_pub_key:V.vec u8 { V.length signing_pub_key == U32.v key_size })
  (#s:Seq.seq u8)
  requires V.pts_to signing_pub_key s
  returns r:state 
  ensures init_inv key_size s r
{
  //creation of session_transcript
  let session_transcript = V.alloc 0uy (SZ.uint_to_t hash_size);


  let ts = Seq.create hash_size 0uy;
  
  //creation of the ghost session data storage
  let repr = {key_size_repr = key_size; signing_pub_key_repr = s; transcript = ts};

  //creation of the trace
  let trace = next_trace emp_trace (G_Initialized repr);

  //creation of the ghost trace ref
  let r = ghost_alloc #_ #trace_pcm (pcm_elt 1.0R trace);



  //creation of the session data storage
  let st = { key_size;signing_pub_key; session_transcript;g_trace_ref = r };
  
  rewrite each
    signing_pub_key as st.signing_pub_key,
    s as repr.signing_pub_key_repr;

 
  with _v. rewrite (V.pts_to session_transcript _v) as
                   (V.pts_to st.session_transcript ts);

  fold (session_state_related (Initialized st) (G_Initialized repr));

  fold (spdm_inv (Initialized st) r trace);

  let res = Initialized st;

  fold (init_inv key_size s (Initialized st));

  res
}
   
let b_resp_resp_repr_relation (ctx:parser_context)
                              (r:resp_repr ctx) 
                              (s:Seq.seq u8) =

admit()


let get_state_data_transcript (s_data:st) : V.vec u8 = s_data.session_transcript

let get_state_data_signing_pub_key (s_data:st) : V.vec u8 = s_data.signing_pub_key

let get_state_data_key_size (s_data:st) : u32 = s_data.key_size

fn parser 
(ctx:parser_context)
(#p:perm)
(#b_resp: G.erased (Seq.seq u8))  
(with_sign:bool)
requires V.pts_to ctx.resp #p b_resp
 returns res: spdm_measurement_result_t
ensures V.pts_to ctx.resp #p b_resp **
        parser_post1 ctx res with_sign

{
  admit()
}

let get_gstate_data (c:g_state{has_full_state_info c}) : repr =
 match c with
 |G_Initialized s -> s
 |G_Recv_no_sign_resp s _ _ -> s
 |G_Recv_sign_resp s _ _ -> s

let session_state_tag_related (s:state) (gs:g_state) : GTot bool =
  match s, gs with
   | Initialized st, G_Initialized repr
   
   | Recv_no_sign_resp st, G_Recv_no_sign_resp repr _ _ ->
    true
   
   | _ -> false

ghost
fn intro_session_state_tag_related (s:state) (gs:g_state)
  requires session_state_related s gs
  ensures session_state_related s gs **
          pure (session_state_tag_related s gs)
{
  let b = session_state_tag_related s gs;
  if b {
    ()
  } else {
    rewrite (session_state_related s gs) as
            (pure False);
    unreachable ()
  }
}

noextract
let full (t0:trace) = Some #perm 1.0R, t0

noextract
let half (t0:trace) = Some #perm 0.5R, t0


#push-options "--print_implicits"

ghost
fn extend_trace (gr: gref) (tr0: trace) (gs:g_state{valid_transition tr0 gs})
  requires C.ghost_pcm_pts_to gr (full tr0)
  ensures  C.ghost_pcm_pts_to gr (full (next_trace tr0 gs))
  {
     ghost_write 
      gr
      (full tr0)
      (full (next_trace tr0 gs))
      (mk_frame_preserving_upd tr0 gs)
     
  }

let valid_transition_lemma
  (tr0:trace{has_full_state_info (current_state tr0)})
  (rep:repr)
  (rep_new:repr)
  (#b_req: G.erased (Seq.seq u8))
  (#b_resp: G.erased (Seq.seq u8))
  : Lemma
    (requires  (G_Initialized? (current_state tr0) \/ G_Recv_no_sign_resp? (current_state tr0)) /\
               (G_Initialized? (current_state tr0) ==>
                          (G_Initialized rep == current_state tr0) /\
                          (rep.signing_pub_key_repr == rep_new.signing_pub_key_repr /\
                           rep.key_size_repr = rep_new.key_size_repr  /\
                          hash_of hash_algo rep.transcript b_req b_resp rep_new.transcript)) /\
                
               (G_Recv_no_sign_resp? (current_state tr0) ==>
                          (exists req resp. G_Recv_no_sign_resp rep req resp == current_state tr0) /\
                          (rep.signing_pub_key_repr == rep_new.signing_pub_key_repr /\
                           rep.key_size_repr = rep_new.key_size_repr /\
                           hash_of hash_algo rep.transcript b_req b_resp rep_new.transcript))
    )
    (ensures valid_transition tr0 (G_Recv_no_sign_resp rep_new b_req b_resp)) = ()

let valid_transition_lemma1
  (tr0:trace{has_full_state_info (current_state tr0)})
  (rep:repr)
  (rep_new:repr)
  (#b_req: G.erased (Seq.seq u8))
  (#b_resp: G.erased (Seq.seq u8))
  : Lemma
    (requires  (G_Initialized? (current_state tr0) \/ G_Recv_no_sign_resp? (current_state tr0)) /\
               (G_Initialized? (current_state tr0) ==>
                          (G_Initialized rep == current_state tr0) /\
                          (rep.signing_pub_key_repr == rep_new.signing_pub_key_repr /\
                           rep.key_size_repr = rep_new.key_size_repr /\
                           hash_of hash_algo rep.transcript b_req b_resp rep_new.transcript)) /\
                
               (G_Recv_no_sign_resp? (current_state tr0) ==>
                          (exists req resp. G_Recv_no_sign_resp rep req resp == current_state tr0) /\
                          (rep.signing_pub_key_repr == rep_new.signing_pub_key_repr /\
                           rep.key_size_repr = rep_new.key_size_repr /\
                           hash_of hash_algo rep.transcript b_req b_resp rep_new.transcript))
    )
    (ensures valid_transition tr0 (G_Recv_sign_resp rep_new b_req b_resp)) = ()

fn
no_sign_resp_aux
  (ctx:parser_context{u32_v ctx.resp_size > 0})
  (req_size: u32{u32_v req_size > 0})
  (req:V.vec u8 { V.length req == u32_v req_size })
  (c:state)
  (st:st)
  (rep:repr)
  (res:spdm_measurement_result_t)
  (#tr0:trace{has_full_state_info (current_state tr0)})
  (#b_req: G.erased (Seq.seq u8))
  (#b_resp: G.erased (Seq.seq u8))
  (#p_req : perm)
  (#p_resp:perm)
  requires parser_post1 ctx res false **
           V.pts_to req #p_req b_req **
           V.pts_to ctx.resp #p_resp b_resp **
           V.pts_to st.session_transcript rep.transcript **
           V.pts_to st.signing_pub_key rep.signing_pub_key_repr **
           pure (st.key_size == rep.key_size_repr /\
                (c == Initialized st \/ c == Recv_no_sign_resp st) /\
                (rep.transcript == (current_transcript tr0)) /\
                (rep.signing_pub_key_repr == (current_key tr0)) /\
                (rep.key_size_repr == (current_key_size tr0)) /\
                (G_Recv_no_sign_resp? (current_state tr0) \/ G_Initialized? (current_state tr0)) /\
                (G_Initialized? (current_state tr0) ==>
                          (G_Initialized rep == current_state tr0)) /\
                (G_Recv_no_sign_resp? (current_state tr0) ==>
                          (exists b_req' b_resp'. G_Recv_no_sign_resp rep b_req' b_resp' == current_state tr0)) /\
                res.status == Success) **
           C.ghost_pcm_pts_to 
                  (get_state_data c).g_trace_ref
                  (Some #perm 1.0R, tr0)

           
  returns ret: spdm_measurement_result_t & state
   
   ensures  V.pts_to req #p_req b_req **
            V.pts_to ctx.resp #p_resp b_resp **
            parser_post1 ctx (fst ret) false **
             (exists* tr1.
                  spdm_inv (snd ret) (get_state_data (snd ret)).g_trace_ref tr1 **
                  pure ((fst ret).status == Success ==>
                                      state_change_success_no_sign tr0 tr1 /\
                                      hash_result_success_no_sign tr0 tr1 #b_req #b_resp))
{
  let curr_state_data = get_state_data c;
    let curr_state_transcript:V.vec u8 = curr_state_data.session_transcript;
    let curr_state_signing_pub_key = curr_state_data.signing_pub_key;
    let curr_state_key_size = curr_state_data.key_size;
      //get the ghost transcript
    let curr_g_transcript = current_transcript tr0;
      
    let curr_g_key = current_key tr0;
    let curr_g_key_size = current_key_size tr0;
    
    rewrite (V.pts_to st.session_transcript rep.transcript) as
                  (V.pts_to curr_state_transcript rep.transcript);
        
    rewrite (V.pts_to curr_state_transcript rep.transcript) as
                (V.pts_to curr_state_transcript curr_g_transcript);
    
    assert_ (pure(Seq.length curr_g_transcript == hash_size));
    let new_g_transcript' = hash_spec hash_algo curr_g_transcript b_req;
    let new_g_transcript = hash_spec hash_algo new_g_transcript' b_resp;

    assert_ (pure(V.length curr_state_transcript == hash_size /\
                  u32_v req_size > 0 /\
                  V.length req == u32_v req_size)); 
    
    assert_ (V.pts_to curr_state_transcript curr_g_transcript);
    assert_ (V.pts_to req #p_req b_req);

    hash hash_algo curr_state_transcript req_size req #curr_g_transcript #b_req #p_req;

    assert_ (pure(V.length curr_state_transcript == hash_size /\
                  u32_v ctx.resp_size > 0 /\
                  V.length ctx.resp == u32_v ctx.resp_size)); 

    hash hash_algo curr_state_transcript ctx.resp_size ctx.resp #new_g_transcript' #b_resp #p_resp;

    let rep_new = {key_size_repr = curr_g_key_size; signing_pub_key_repr = curr_g_key; transcript = new_g_transcript};

    //Trace ref creation-----------------------------------------------------------------------------------------------------------
    //new trace----------------------------------------------------------------------------------------------------------------
    //bring in a lemma to prove this
    valid_transition_lemma tr0 rep rep_new;
    assert_ (pure(valid_transition tr0 (G_Recv_no_sign_resp rep_new b_req b_resp)));

    let tr1 = next_trace tr0 (G_Recv_no_sign_resp rep_new b_req b_resp);

    extend_trace ((get_state_data c).g_trace_ref) tr0 ((G_Recv_no_sign_resp rep_new b_req b_resp));

     //New state data record creation
    //----------------------------------------------------------------------------------------------------------------------------
    let new_st = {key_size = curr_state_key_size; 
                    signing_pub_key = curr_state_signing_pub_key; 
                    session_transcript = curr_state_transcript;
                    g_trace_ref = curr_state_data.g_trace_ref};


    //Do the state change---------------------------------------------------------------------------------------------------------
    let new_state = (Recv_no_sign_resp new_st);

    with _v. rewrite (V.pts_to curr_state_transcript _v) as
                         (V.pts_to curr_state_transcript new_g_transcript);

    rewrite (V.pts_to curr_state_transcript new_g_transcript) as
                (V.pts_to new_st.session_transcript rep_new.transcript);
    
     rewrite (V.pts_to st.signing_pub_key rep.signing_pub_key_repr) as
                (V.pts_to curr_state_signing_pub_key rep.signing_pub_key_repr);
        
     rewrite (V.pts_to curr_state_signing_pub_key rep.signing_pub_key_repr) as
                (V.pts_to curr_state_signing_pub_key curr_g_key);

     rewrite (V.pts_to curr_state_signing_pub_key curr_g_key) as
                (V.pts_to new_st.signing_pub_key rep_new.signing_pub_key_repr);

     assert_ ( V.pts_to new_st.signing_pub_key rep_new.signing_pub_key_repr **
                  V.pts_to new_st.session_transcript rep_new.transcript **
                  pure (new_st.key_size == rep_new.key_size_repr));
    
    fold (session_state_related (Recv_no_sign_resp new_st) (G_Recv_no_sign_resp rep_new b_req b_resp));

    with _v. rewrite (C.ghost_pcm_pts_to #trace_pcm_t #trace_pcm _v (pcm_elt 1.0R tr1)) as
                         (C.ghost_pcm_pts_to (get_state_data (Recv_no_sign_resp new_st)).g_trace_ref (pcm_elt 1.0R tr1));
    

   fold (spdm_inv (Recv_no_sign_resp new_st) (get_state_data (Recv_no_sign_resp new_st)).g_trace_ref tr1);

   let fin = (res, new_state);
   fin
}


fn no_sign_resp1
  (ctx:parser_context)
  (req_size: u32{u32_v req_size > 0})
  (req:V.vec u8 { V.length req == u32_v req_size })
  (c:state)
  (#tr0:trace{has_full_state_info (current_state tr0)})
  (#b_resp: G.erased (Seq.seq u8)(*{u32_v ctx.resp_size > 0 /\ Seq.length b_resp == u32_v ctx.resp_size}*))
  (#b_req: G.erased (Seq.seq u8)(*{Seq.length b_req == u32_v req_size}*))
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
{
  admit()
}