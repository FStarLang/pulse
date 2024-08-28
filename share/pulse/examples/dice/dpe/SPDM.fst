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
         (#ts_seq: (G.erased (Seq.seq u8)){Seq.length ts_seq == hash_size})
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
   
   | Recv_no_sign_resp st _ _, G_Recv_no_sign_resp repr _ _ ->
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
  (rep_new:repr{~(all_zeros_hash_transcript rep_new.transcript)})
  : Lemma
    (requires  (G_Initialized? (current_state tr0) \/ G_Recv_no_sign_resp? (current_state tr0)) /\
               (G_Initialized? (current_state tr0) ==>
                          (all_zeros_hash_transcript rep.transcript) /\
                          (G_Initialized rep == current_state tr0) /\
                          (rep.signing_pub_key_repr == rep_new.signing_pub_key_repr /\
                           rep.key_size_repr = rep_new.key_size_repr )) /\
                
               (G_Recv_no_sign_resp? (current_state tr0) ==>
                          ~(all_zeros_hash_transcript rep.transcript) /\
                          (G_Recv_no_sign_resp rep == current_state tr0) /\
                          (rep.signing_pub_key_repr == rep_new.signing_pub_key_repr /\
                           rep.key_size_repr = rep_new.key_size_repr /\
                          (exists req_size req resp_size resp hash_algo. 
                             hash_of hash_algo rep.transcript req_size req resp_size resp rep_new.transcript)))
    )
    (ensures valid_transition tr0 (G_Recv_no_sign_resp rep_new)) = ()