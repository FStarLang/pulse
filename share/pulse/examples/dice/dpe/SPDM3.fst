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
  let st = { key_size; (*session_transcript_size = 0ul;*)signing_pub_key; session_transcript;g_trace_ref = r };
  
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
          V.pts_to v2 #p2 v2_seq **
          pure (V.is_full_vec v)
  {
    admit()
  } 

fn write_req_resp_to_transcript
  (#a:Type0)
  (v_req: V.vec a)
  (v_resp: V.vec a)
  (v_tx: V.vec a)
  (req_size: u32)
  (resp_size: u32)
  (tx_size: u32{u32_v tx_size <=  max_transcript_message_buffer_size})
  
  (#s_req: Ghost.erased (Seq.seq a)) 
  (#s_resp: Ghost.erased (Seq.seq a))
  (#s_tx: Ghost.erased (Seq.seq a))
  (#p1:perm)
  (#p2:perm)
  
  requires V.pts_to v_req #p1 s_req **
           V.pts_to v_resp #p2 s_resp **
           V.pts_to v_tx s_tx
  returns b:bool
  ensures V.pts_to v_tx (if b then Seq.append (Seq.append s_tx s_req) s_resp else s_tx) **
          V.pts_to v_req #p1 s_req **
          V.pts_to v_resp #p2 s_resp (***
          pure (V.is_full_vec v_tx)*)
  {
    let rem_size = U32.sub (U32.uint_to_t max_transcript_message_buffer_size) tx_size;

    //req_size and resp_size cannot be more than some bytes.
    //Assume that their sum always fits within U32.t
    assume_ (pure(UInt.fits (u32_v req_size + u32_v resp_size) U32.n)); 
    let size_to_add = U32.add req_size resp_size;

    if(u32_v size_to_add >= u32_v rem_size)
    {
      admit()
    }
    else
    {
      
      //split v_tx 
      admit()
    }
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

let get_gstate_data (c:g_state{has_full_state_info c}) : repr =
 match c with
 |G_Initialized s -> s
 |G_Recv_no_sign_resp s -> s
 |G_Recv_sign_resp s -> s

let session_state_tag_related (s:state) (gs:g_state) : GTot bool =
  match s, gs with
   | Initialized st, G_Initialized repr
   
   | Recv_no_sign_resp st, G_Recv_no_sign_resp repr ->
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

(*let g_append_lemma (t0:g_transcript) (s:Seq.seq u8{Seq.length s > 0}) 
    : Lemma
      (ensures Seq.length (g_append t0 s) > 0) =
()*)


(* assume_ (pure (G_Initialized? (current_state tr0)));
  assert (pure(g_transcript_empty rep.transcript));*)
noextract
let full (t0:trace) = Some #perm 1.0R, t0

noextract
let half (t0:trace) = Some #perm 0.5R, t0


#push-options "--print_implicits"

ghost
fn extend_trace (gr: gref) (tr0: trace) (gs:g_state{valid_transition tr0 gs})
  requires C.ghost_pcm_pts_to gr (Some #perm 1.0R, tr0)
  ensures  C.ghost_pcm_pts_to gr (Some #perm 1.0R, next_trace tr0 gs)
  {
     ghost_write 
      gr
      (Some #perm 1.0R, tr0)
      (Some #perm 1.0R, (next_trace tr0 gs))
      (mk_frame_preserving_upd tr0 gs)
     
  }


(*noextract
let mk_frame_preserving_upd
  (t:trace)
  (s:g_state { valid_transition t s})
  : FStar.PCM.frame_preserving_upd trace_pcm (Some 1.0R, t) (Some 1.0R, next_trace t s) =
  fun _ -> Some 1.0R, next_trace t s*)


fn no_sign_resp1
  (ctx:parser_context)
  (req_size: u32)
  (req:V.vec u8 { V.length req == u32_v req_size })
  (c:state)
  (#tr0:trace{has_full_state_info (current_state tr0)})
  (#b_resp: G.erased (Seq.seq u8){Seq.length b_resp > 0})
  (#b_req: G.erased (Seq.seq u8){Seq.length b_req > 0})
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
                     spdm_inv (snd res) (get_state_data (snd res)).g_trace_ref tr1 **
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
      (*rewrite (parser_post ctx res #b_resp) as
              (pure True);*)

      // rewrite  (pure True) as
      //           (parser_post ctx res #b_resp);
      //show_proof_state;
      //assume_ (parser_post ctx res #b_resp);
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
      let curr_state_transcript:V.vec u8 = curr_state_data.session_transcript;
      let curr_state_signing_pub_key = curr_state_data.signing_pub_key;
      let curr_state_key_size = curr_state_data.key_size;
      
      //append req and resp
      let append_req_resp = append_vec req ctx.resp #b_req #b_resp #p_req #p_resp;
  
      //get the ghost transcript
      let curr_g_transcript = current_transcript tr0;
      
      let curr_g_key = current_key tr0;
      let curr_g_key_size = current_key_size tr0;
      
      //assert (spdm_inv c ((get_state_data c).g_trace_ref) tr0);
      unfold (spdm_inv c ((get_state_data c).g_trace_ref) tr0);
      
      //assert (session_state_related c (current_state tr0));
      unfold (session_state_related c (current_state tr0));
      
      let rep = get_gstate_data (current_state tr0);
      match c {
        Initialized st -> {
        
        intro_session_state_tag_related (Initialized st) (current_state tr0);
        rewrite (session_state_related (Initialized st) (current_state tr0)) as
                 (session_state_related (Initialized st) (G_Initialized rep));

        
        unfold (session_state_related (Initialized st) (G_Initialized rep));
        
        
        rewrite (V.pts_to st.session_transcript rep.transcript) as
                (V.pts_to curr_state_transcript rep.transcript);
        
        

        rewrite (V.pts_to curr_state_transcript rep.transcript) as
                (V.pts_to curr_state_transcript curr_g_transcript);
        
        let new_transcript = append_vec curr_state_transcript append_req_resp #curr_g_transcript #(Seq.append b_req b_resp);
        
        let new_g_transcript = g_append curr_g_transcript (Seq.append b_req b_resp);
       
       //create a new state data record with the new transcript
       //creation of the ghost session data storage
        let rep_new = {key_size_repr = curr_g_key_size; signing_pub_key_repr = curr_g_key; transcript = new_g_transcript};
        
        //Trace ref creation-----------------------------------------------------------------------------------------------------------
        //creation of the trace
        //let trace = next_trace tr0 (G_Recv_no_sign_resp rep_new);

         //new trace----------------------------------------------------------------------------------------------------------------
        let tr1 = next_trace tr0 (G_Recv_no_sign_resp rep_new);
  
        assert (pure(g_transcript_current_session_grows_by (current_transcript tr0 ) 
                                                (current_transcript tr1) 
                                                (Seq.append b_req b_resp)));
        
        //creation of the ghost trace ref
        //let r = ghost_alloc #_ #trace_pcm (pcm_elt 1.0R tr1);
        //assert_ (pure(rep.transcript == Seq.slice rep_new.transcript 0 (Seq.length rep.transcript)));
        assert_ (pure (valid_transition tr0 (G_Recv_no_sign_resp rep_new)));
        extend_trace ((get_state_data (Initialized st)).g_trace_ref) tr0 ((G_Recv_no_sign_resp rep_new)); 
        
        

        //New state data record creation
        //----------------------------------------------------------------------------------------------------------------------------
        let new_st = {key_size = curr_state_key_size; 
                    signing_pub_key = curr_state_signing_pub_key; 
                    session_transcript = new_transcript;
                    g_trace_ref = curr_state_data.g_trace_ref(*r*)};
        
        //Do the state change---------------------------------------------------------------------------------------------------------
        let new_state = (Recv_no_sign_resp new_st);
        
        assert_ (pure (res.status == Success ==> (G_Recv_no_sign_resp? (current_state tr1) /\
                            valid_transition tr0 (current_state tr1) /\ tr1 == next_trace tr0 (current_state tr1)) /\
                           (G_Recv_no_sign_resp? (current_state tr1) /\
                           g_transcript_current_session_grows_by (current_transcript tr0 ) 
                                      (current_transcript tr1) 
                                      (Seq.append b_req b_resp))));
        
        
        with _v. rewrite (V.pts_to new_transcript _v) as
                         (V.pts_to new_transcript new_g_transcript);

        rewrite (V.pts_to new_transcript new_g_transcript) as
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
        
        fold (session_state_related (Recv_no_sign_resp new_st) (G_Recv_no_sign_resp rep_new));
        
        with _v. rewrite (C.ghost_pcm_pts_to #trace_pcm_t #trace_pcm _v (pcm_elt 1.0R tr1)) as
                         (C.ghost_pcm_pts_to (get_state_data (Recv_no_sign_resp new_st)).g_trace_ref (pcm_elt 1.0R tr1));
        
        
        fold (spdm_inv (Recv_no_sign_resp new_st) (get_state_data (Recv_no_sign_resp new_st)).g_trace_ref tr1);
        
        let fin = (res, new_state);

        assert_ (V.pts_to req #p_req b_req **
                 V.pts_to ctx.resp #p_resp b_resp **

                //parser related post-conditions
                parser_post ctx (fst fin) #b_resp **
           
                //state change related post-condition 
                (exists* tr1.
                     spdm_inv (snd fin) (get_state_data (snd fin)).g_trace_ref tr1 **
                     (*no_sign_resp_state_related_post_conditions ctx tr0 tr1 c (snd res) #b_resp #b_req (fst res)*)
                     pure ((fst fin).status == Success ==> (G_Recv_no_sign_resp? (current_state tr1) /\
                            valid_transition tr0 (current_state tr1) /\ tr1 == next_trace tr0 (current_state tr1)) /\
                           (G_Recv_no_sign_resp? (current_state tr1) /\
                           g_transcript_current_session_grows_by (current_transcript tr0 ) 
                                      (current_transcript tr1) 
                                      (Seq.append b_req b_resp)))));
        
        
        
        V.free curr_state_transcript;

        
        V.free append_req_resp;

         fin
        }
        
        Recv_no_sign_resp st -> {
          intro_session_state_tag_related (Recv_no_sign_resp st ) (current_state tr0);
          rewrite (session_state_related (Recv_no_sign_resp st) (current_state tr0)) as
                 (session_state_related (Recv_no_sign_resp st) (G_Recv_no_sign_resp rep));
          
          unfold (session_state_related (Recv_no_sign_resp st) (G_Recv_no_sign_resp rep));
        
        
          rewrite (V.pts_to st.session_transcript rep.transcript) as
                (V.pts_to curr_state_transcript rep.transcript);

          rewrite (V.pts_to curr_state_transcript rep.transcript) as
                  (V.pts_to curr_state_transcript curr_g_transcript);
          
          let new_transcript = append_vec curr_state_transcript append_req_resp #curr_g_transcript #(Seq.append b_req b_resp);
        
          let new_g_transcript = g_append curr_g_transcript (Seq.append b_req b_resp);
          
          //create a new state data record with the new transcript
          //creation of the ghost session data storage
          let rep_new = {key_size_repr = curr_g_key_size; signing_pub_key_repr = curr_g_key; transcript = new_g_transcript};
          assert_ (pure(current_state tr0 == G_Recv_no_sign_resp rep));
          assert_ (pure (rep_new.signing_pub_key_repr == rep.signing_pub_key_repr)); 
          assert_ (pure(rep_new.key_size_repr == rep.key_size_repr));

          assert_ (pure(Seq.length rep.transcript < Seq.length rep_new.transcript));

          assert_ (pure(rep.transcript `FStar.Seq.equal` Seq.slice rep_new.transcript 0 (Seq.length rep.transcript)));

          assert_ (pure (is_prefix_of rep.transcript rep_new.transcript));

          assert_ (pure(next (current_state tr0) (G_Recv_no_sign_resp rep_new)));
          assert_ (pure (valid_transition tr0 (G_Recv_no_sign_resp rep_new)));
          //extending the trace
          //assert_ (pure(valid_transition tr0 ((G_Recv_no_sign_resp rep_new))));
          extend_trace ((get_state_data (Recv_no_sign_resp st)).g_trace_ref) tr0 ((G_Recv_no_sign_resp rep_new)); 

           //New state data record creation
        //----------------------------------------------------------------------------------------------------------------------------
        let new_st = {key_size = curr_state_key_size; 
                      signing_pub_key = curr_state_signing_pub_key; 
                      session_transcript = new_transcript;
                      g_trace_ref = curr_state_data.g_trace_ref(*r*)};
        
        //Do the state change---------------------------------------------------------------------------------------------------------
        let new_state = (Recv_no_sign_resp new_st);
        
        assert_ (pure (res.status == Success ==> (G_Recv_no_sign_resp? (current_state (next_trace tr0 (G_Recv_no_sign_resp rep_new))) /\
                            valid_transition tr0 (current_state (next_trace tr0 (G_Recv_no_sign_resp rep_new))) /\ 
                            (next_trace tr0 (G_Recv_no_sign_resp rep_new)) == next_trace tr0 (current_state (next_trace tr0 (G_Recv_no_sign_resp rep_new)))) /\
                           (G_Recv_no_sign_resp? (current_state (next_trace tr0 (G_Recv_no_sign_resp rep_new))) /\
                           g_transcript_current_session_grows_by (current_transcript tr0 ) 
                                      (current_transcript (next_trace tr0 (G_Recv_no_sign_resp rep_new))) 
                                      (Seq.append b_req b_resp))));
        with _v. rewrite (V.pts_to new_transcript _v) as
                         (V.pts_to new_transcript new_g_transcript);

        rewrite (V.pts_to new_transcript new_g_transcript) as
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
        fold (session_state_related (Recv_no_sign_resp new_st) (G_Recv_no_sign_resp rep_new));
        with _v. rewrite (C.ghost_pcm_pts_to #trace_pcm_t #trace_pcm _v (pcm_elt 1.0R (next_trace tr0 (G_Recv_no_sign_resp rep_new)))) as
                         (C.ghost_pcm_pts_to (get_state_data (Recv_no_sign_resp new_st)).g_trace_ref (pcm_elt 1.0R (next_trace tr0 (G_Recv_no_sign_resp rep_new))));
        
        
        fold (spdm_inv (Recv_no_sign_resp new_st) (get_state_data (Recv_no_sign_resp new_st)).g_trace_ref (next_trace tr0 (G_Recv_no_sign_resp rep_new)));

        let fin = (res, new_state);

        V.free curr_state_transcript;

        V.free append_req_resp;

        fin
        }
      }
}
}
}

fn reset
  (c:state)
  (#tr0:trace {has_full_state_info(current_state tr0) })
  requires (spdm_inv c ((get_state_data c).g_trace_ref) tr0 **
           pure (G_Recv_no_sign_resp? (current_state tr0))
                          )
  returns r:state
  ensures init_inv (get_state_data c).key_size (current_key tr0) r
  {
    //get the ghost transcript
      
      let curr_g_key = current_key tr0;
      let curr_g_key_size = current_key_size tr0;
      let curr_g_transcript = current_transcript tr0;
    
    //creation of the ghost session data storage
    let rep_new = {key_size_repr = curr_g_key_size; signing_pub_key_repr = curr_g_key; transcript = Seq.empty};
    
    let curr_state_data = get_state_data c;
    let curr_state_transcript:V.vec u8 = curr_state_data.session_transcript;
    let curr_state_signing_pub_key = curr_state_data.signing_pub_key;
    let curr_state_key_size = curr_state_data.key_size;
    
    let curr_state_gref = curr_state_data.g_trace_ref;

    assert_ (pure (valid_transition tr0 (G_Initialized rep_new)));
    
    unfold (spdm_inv c ((get_state_data c).g_trace_ref) tr0);
      
    //assert (session_state_related c (current_state tr0));
    unfold (session_state_related c (current_state tr0));
    
    let rep = get_gstate_data (current_state tr0);

    match c {
        Initialized st -> {
         intro_session_state_tag_related (Initialized st) (current_state tr0);
         assert_ (pure (session_state_tag_related (Initialized st) (current_state tr0)));
         assert_ (pure false);
         unreachable()
        }
        Recv_no_sign_resp st -> {
           intro_session_state_tag_related (Recv_no_sign_resp st ) (current_state tr0);
           assert_ (pure (session_state_tag_related (Recv_no_sign_resp st) (current_state tr0)));
           rewrite (session_state_related (Recv_no_sign_resp st) (current_state tr0)) as
                 (session_state_related (Recv_no_sign_resp st) (G_Recv_no_sign_resp rep));
           unfold (session_state_related (Recv_no_sign_resp st) (G_Recv_no_sign_resp rep));
           rewrite (V.pts_to st.session_transcript rep.transcript) as
                   (V.pts_to curr_state_transcript rep.transcript);

           rewrite (V.pts_to curr_state_transcript rep.transcript) as
                   (V.pts_to curr_state_transcript curr_g_transcript);
          admit()
        }
    }
  }

(*ghost
fn intro_session_state_tag_related (s:state) (gs:g_state)
  requires session_state_related s gs
  ensures session_state_related s gs **
          pure (session_state_tag_related s gs)*)


(*fn init0 (key_size:u32) (signing_pub_key:V.vec u8 { V.length signing_pub_key == U32.v key_size })
  (#s:Seq.seq u8)
  requires V.pts_to signing_pub_key s
  returns r:state 
  ensures init_inv key_size s r*)

  (*let init_inv (key_len:u32) (b:Seq.seq u8) (s:state) : slprop =
  exists* (t:trace).
    spdm_inv s (get_state_data s).g_trace_ref t ** 
    pure (G_Initialized? (current_state t) /\
          g_key_of_gst (current_state t) == b /\
          g_key_len_of_gst (current_state t) == key_len)*)

(*assume in Recv_No_Sign branch
  st should contain the size of the transcript
  new signature for write_to_transcript based on buffer overflow condition
  The transcript vector points to the Seq.slice of the some seq upto transcript_buffer_size*)

  (*Abstract the two branches*)