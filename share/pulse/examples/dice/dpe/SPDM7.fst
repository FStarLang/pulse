module SPDM7
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
         (#msg_seq:(G.erased (Seq.seq u8)){Seq.length msg_seq == u32_v msg_size})
         (#p_msg:perm)
    requires V.pts_to ts_digest ts_seq **
              V.pts_to msg #p_msg msg_seq
    ensures (exists* new_ts_seq. V.pts_to ts_digest new_ts_seq **
                                           V.pts_to msg #p_msg msg_seq **
                                           pure (Seq.equal new_ts_seq (hash_seq hash_algo ts_seq msg_size msg_seq))) 
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
  
  assert_ (pure (all_zeros_hash_transcript ts));
  //creation of the ghost session data storage
  let repr = {key_size_repr = key_size; signing_pub_key_repr = s; transcript = ts};

  //creation of the trace
  let trace = next_trace emp_trace (G_Initialized repr);

  //creation of the ghost trace ref
  let r = ghost_alloc #_ #trace_pcm (pcm_elt 1.0R trace);



  //creation of the session data storage
  let st = { key_size;signing_pub_key; session_transcript;g_trace_ref = r };
  
  
  
  (*We get, V.pts_to signing_pub_key s from the pre-condition. To prove session_related, we need to rewrite signing_pub_key as 
    st.signing_pub_key and s as repr.signing_pub_key_repr, where rewrite works as these entities are equal*)
  rewrite each
    signing_pub_key as st.signing_pub_key,
    s as repr.signing_pub_key_repr;

 (*pure things are asserted with assert_*)
   //assert_ (pure (Seq.equal (Seq.create (SZ.v 0sz) 0uy) Seq.empty));

  (*Here, rewrite is for entire V.pts_to, hence use with _v., where _v indicates the seq equivalent of the vector*)
   with _v. rewrite (V.pts_to session_transcript _v) as
                   (V.pts_to st.session_transcript ts);

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
  (with_sign: bool)

requires V.pts_to ctx.resp #p b_resp
returns res: spdm_measurement_result_t
ensures 
         V.pts_to ctx.resp #p b_resp **
         parser_post1 ctx res with_sign
{
  admit()
}

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

let no_sign_resp_state_related_post_conditions 
  (ctx:parser_context)
  (tr0:trace)
  (tr1:trace)
  (c:state)
  (res_state:state) 
  (#b_resp: Seq.seq u8{Seq.length b_resp > 0 /\ (UInt.fits (Seq.length b_resp) U32.n)})
  (#b_req: Seq.seq u8{Seq.length b_req > 0 /\ (UInt.fits (Seq.length b_req) U32.n)}) 
  (res:spdm_measurement_result_t) :slprop =

pure (res.status == Success ==> (G_Recv_no_sign_resp? (current_state tr1)/\
valid_transition tr0 (current_state tr1) /\ tr1 == next_trace tr0 (current_state tr1)) /\
(G_Recv_no_sign_resp? (current_state tr1) /\
(exists hash_algo. 
         hash_of hash_algo (current_transcript tr0 ) 
                           (U32.uint_to_t(Seq.length b_req)) 
                           b_req 
                           (U32.uint_to_t (Seq.length b_resp)) 
                           b_resp 
                           (current_transcript tr1))))

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
    returns res: spdm_measurement_result_t & state
    
    ensures V.pts_to req #p_req b_req **
            V.pts_to ctx.resp #p_resp b_resp **

            //parser related post-conditions
            parser_post1 ctx (fst res) false  **
           
            //state change related post-condition 
             (exists* tr1.
                     spdm_inv (snd res) (get_state_data (snd res)).g_trace_ref tr1 **
                     (*no_sign_resp_state_related_post_conditions ctx tr0 tr1 c (snd res) #b_resp #b_req (fst res)*)
                     pure ((fst res).status == Success ==> (G_Recv_no_sign_resp? (current_state tr1)) /\
                            (valid_transition tr0 (current_state tr1)) /\ (tr1 == next_trace tr0 (current_state tr1)) /\
                           (G_Recv_no_sign_resp? (current_state tr1)) /\

                           (exists hash_algo. 
                                   hash_of hash_algo (current_transcript tr0 ) 
                                  (U32.uint_to_t(Seq.length b_req)) 
                                  b_req 
                                  (U32.uint_to_t (Seq.length b_resp)) 
                                  b_resp 
                                 (current_transcript tr1))))

            
{
  let res = parser0 ctx #p_resp #b_resp false;
  match res.status {
    Parse_error -> {
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
              (exists hash_algo. 
                                   hash_of hash_algo (current_transcript tr0 ) 
                                  (U32.uint_to_t(Seq.length b_req)) 
                                  b_req 
                                  (U32.uint_to_t (Seq.length b_resp)) 
                                  b_resp 
                                 (current_transcript tr1))
              )));
       (res,c)
    }
    Success -> {
       //current state transcript
      let curr_state_data = get_state_data c;
      let curr_state_transcript:V.vec u8 = curr_state_data.session_transcript;
      let curr_state_signing_pub_key = curr_state_data.signing_pub_key;
      let curr_state_key_size = curr_state_data.key_size;
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
          
          assert_ (pure(Seq.length curr_g_transcript == hash_size));
          let new_g_transcript' = hash_seq hash_algo curr_g_transcript req_size b_req;
          let new_g_transcript = hash_seq hash_algo new_g_transcript' ctx.resp_size b_resp;
          
          assert_ (pure(V.length curr_state_transcript == hash_size));
          assert_ (V.pts_to curr_state_transcript curr_g_transcript);
          assert_ (V.pts_to req #p_req b_req);
          
          hash hash_algo curr_state_transcript req_size req #curr_g_transcript #b_req #p_req;
          assert_ (pure (Seq.equal new_g_transcript' (hash_seq hash_algo curr_g_transcript req_size b_req)));
          assert_ (V.pts_to curr_state_transcript new_g_transcript');
          hash hash_algo curr_state_transcript ctx.resp_size ctx.resp #new_g_transcript' #b_resp #p_resp;
          assert_ (V.pts_to curr_state_transcript new_g_transcript);

          //create a new state data record with the new transcript
         //creation of the ghost session data storage
         let rep_new = {key_size_repr = curr_g_key_size; signing_pub_key_repr = curr_g_key; transcript = new_g_transcript};
         
         //Trace ref creation-----------------------------------------------------------------------------------------------------------
        //creation of the trace
        //let trace = next_trace tr0 (G_Recv_no_sign_resp rep_new);

         //new trace----------------------------------------------------------------------------------------------------------------
        let tr1 = next_trace tr0 (G_Recv_no_sign_resp rep_new);

        assert (pure(exists hash_algo. 
                                   hash_of hash_algo (current_transcript tr0 ) 
                                  (U32.uint_to_t(Seq.length b_req)) 
                                  b_req 
                                  (U32.uint_to_t (Seq.length b_resp)) 
                                  b_resp 
                                 (current_transcript tr1)));
          
        //creation of the ghost trace ref
        //let r = ghost_alloc #_ #trace_pcm (pcm_elt 1.0R tr1);
        //assert_ (pure(rep.transcript == Seq.slice rep_new.transcript 0 (Seq.length rep.transcript)));
        assert_ (pure (valid_transition tr0 (G_Recv_no_sign_resp rep_new)));
        extend_trace ((get_state_data (Initialized st)).g_trace_ref) tr0 ((G_Recv_no_sign_resp rep_new));
        
        //New state data record creation
        //----------------------------------------------------------------------------------------------------------------------------
        let new_st = {key_size = curr_state_key_size; 
                    signing_pub_key = curr_state_signing_pub_key; 
                    session_transcript = curr_state_transcript;
                    g_trace_ref = curr_state_data.g_trace_ref};

        
        //Do the state change---------------------------------------------------------------------------------------------------------
        let new_state = (Recv_no_sign_resp new_st);

        assert_ (pure (res.status == Success ==> (G_Recv_no_sign_resp? (current_state tr1) /\
                            valid_transition tr0 (current_state tr1) /\ tr1 == next_trace tr0 (current_state tr1)) /\
                           (G_Recv_no_sign_resp? (current_state tr1) /\
                           (exists hash_algo. 
                                   hash_of hash_algo (current_transcript tr0 ) 
                                  (U32.uint_to_t(Seq.length b_req)) 
                                  b_req 
                                  (U32.uint_to_t (Seq.length b_resp)) 
                                  b_resp 
                                 (current_transcript tr1)))));

        
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
        
        fold (session_state_related (Recv_no_sign_resp new_st) (G_Recv_no_sign_resp rep_new));

        with _v. rewrite (C.ghost_pcm_pts_to #trace_pcm_t #trace_pcm _v (pcm_elt 1.0R tr1)) as
                         (C.ghost_pcm_pts_to (get_state_data (Recv_no_sign_resp new_st)).g_trace_ref (pcm_elt 1.0R tr1));

        fold (spdm_inv (Recv_no_sign_resp new_st) (get_state_data (Recv_no_sign_resp new_st)).g_trace_ref tr1);
        
        let fin = (res, new_state);
        
        fin
        }
         Recv_no_sign_resp st ->{
          intro_session_state_tag_related (Recv_no_sign_resp st ) (current_state tr0);
          rewrite (session_state_related (Recv_no_sign_resp st) (current_state tr0)) as
                 (session_state_related (Recv_no_sign_resp st) (G_Recv_no_sign_resp rep));
          
          unfold (session_state_related (Recv_no_sign_resp st) (G_Recv_no_sign_resp rep));
        
        
          rewrite (V.pts_to st.session_transcript rep.transcript) as
                (V.pts_to curr_state_transcript rep.transcript);

          rewrite (V.pts_to curr_state_transcript rep.transcript) as
                  (V.pts_to curr_state_transcript curr_g_transcript);
          
           assert_ (pure(Seq.length curr_g_transcript == hash_size));
          let new_g_transcript' = hash_seq hash_algo curr_g_transcript req_size b_req;
          let new_g_transcript = hash_seq hash_algo new_g_transcript' ctx.resp_size b_resp;
          
          assert_ (pure(V.length curr_state_transcript == hash_size));
          assert_ (V.pts_to curr_state_transcript curr_g_transcript);
          assert_ (V.pts_to req #p_req b_req);
          
          hash hash_algo curr_state_transcript req_size req #curr_g_transcript #b_req #p_req;
          assert_ (pure (Seq.equal new_g_transcript' (hash_seq hash_algo curr_g_transcript req_size b_req)));
          assert_ (V.pts_to curr_state_transcript new_g_transcript');
          hash hash_algo curr_state_transcript ctx.resp_size ctx.resp #new_g_transcript' #b_resp #p_resp;
          assert_ (V.pts_to curr_state_transcript new_g_transcript);

          //create a new state data record with the new transcript
         //creation of the ghost session data storage
         let rep_new = {key_size_repr = curr_g_key_size; signing_pub_key_repr = curr_g_key; transcript = new_g_transcript};
         
         //Trace ref creation-----------------------------------------------------------------------------------------------------------
        //creation of the trace
        //let trace = next_trace tr0 (G_Recv_no_sign_resp rep_new);

         //new trace----------------------------------------------------------------------------------------------------------------
        
        assert_ (pure(rep.signing_pub_key_repr == rep_new.signing_pub_key_repr));
        assert_ (pure(rep.key_size_repr = rep_new.key_size_repr));

        assert_ (pure (current_transcript tr0 == rep.transcript));
        assert_ (pure(req_size == U32.uint_to_t(Seq.length b_req)));
        assert_ (pure(ctx.resp_size == U32.uint_to_t(Seq.length b_resp)));
        assert_ (pure (rep_new.transcript == new_g_transcript));
        assert_ (pure(hash_of hash_algo rep.transcript req_size b_req ctx.resp_size b_resp rep_new.transcript));
        assert_ (pure (exists req_size req resp_size resp hash_algo. 
                         hash_of hash_algo rep.transcript req_size req resp_size resp rep_new.transcript));

        let tr1 = next_trace tr0 (G_Recv_no_sign_resp rep_new);
        assert_ (pure (valid_transition tr0 (G_Recv_no_sign_resp rep_new)));
        assert_ (pure(next (current_state tr0) (G_Recv_no_sign_resp rep_new)));
        
        extend_trace ((get_state_data (Recv_no_sign_resp st)).g_trace_ref) tr0 ((G_Recv_no_sign_resp rep_new)); 
        
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
        fold (session_state_related (Recv_no_sign_resp new_st) (G_Recv_no_sign_resp rep_new));
        with _v. rewrite (C.ghost_pcm_pts_to #trace_pcm_t #trace_pcm _v (pcm_elt 1.0R (next_trace tr0 (G_Recv_no_sign_resp rep_new)))) as
                         (C.ghost_pcm_pts_to (get_state_data (Recv_no_sign_resp new_st)).g_trace_ref (pcm_elt 1.0R (next_trace tr0 (G_Recv_no_sign_resp rep_new))));
        
        
        fold (spdm_inv (Recv_no_sign_resp new_st) (get_state_data (Recv_no_sign_resp new_st)).g_trace_ref (next_trace tr0 (G_Recv_no_sign_resp rep_new)));

        let fin = (res, new_state);

        fin
         }
      }
    }
  }
}

module US = FStar.SizeT

fn
zeroize_vector
(v:V.vec u8{V.length v == hash_size})
requires V.pts_to v 's
ensures exists* (s:Seq.seq U8.t).
        V.pts_to v s **
        pure (Seq.length s == hash_size /\ (s `Seq.equal` Seq.create (Seq.length s) 0uy))
{
  assert_ (pure(US.fits hash_size));
  let l = US.uint_to_t hash_size;
  V.to_array_pts_to v;
  A.zeroize l (V.vec_to_array v);
  V.to_vec_pts_to v;
  assert_ (exists* (s:Seq.seq U8.t).
           V.pts_to v s **
          pure (Seq.length s == hash_size /\ (s `Seq.equal` Seq.create (Seq.length s) 0uy)));
  ()
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
      
      let ts = Seq.create hash_size 0uy;
      //creation of the ghost session data storage
     let rep_new = {key_size_repr = curr_g_key_size; signing_pub_key_repr = curr_g_key; transcript = ts};
     
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

        zeroize_vector curr_state_transcript;
        
        assert_ (pure(current_state tr0 == G_Recv_no_sign_resp rep));
          
        assert_ (pure (rep_new.signing_pub_key_repr == rep.signing_pub_key_repr)); 
        assert_ (pure(rep_new.key_size_repr == rep.key_size_repr));

        assert_ (pure(next (current_state tr0) (G_Initialized rep_new)));
        assert_ (pure (valid_transition tr0 (G_Initialized rep_new)));
        
        extend_trace ((get_state_data (Recv_no_sign_resp st)).g_trace_ref) tr0 (G_Initialized rep_new); 

        let new_st = {key_size = curr_state_key_size; 
                        signing_pub_key = curr_state_signing_pub_key; 
                        session_transcript = curr_state_transcript;
                        g_trace_ref = curr_state_data.g_trace_ref};
          

        let new_state = (Initialized new_st);
          
        let tr1 = next_trace tr0 (G_Initialized rep_new);

        assert_ (pure (G_Initialized? (current_state tr1)));
          assert_ (pure(g_key_of_gst (current_state tr1) ==  (current_key tr0)));

          assert_ (pure (g_key_len_of_gst (current_state tr1) == (get_state_data c).key_size));

          rewrite each
           curr_state_signing_pub_key as new_st.signing_pub_key,
           curr_g_key as rep_new.signing_pub_key_repr;

          with _v. rewrite (V.pts_to curr_state_transcript _v) as
                           (V.pts_to new_st.session_transcript ts);
          
          assert_ (pure(st.signing_pub_key == new_st.signing_pub_key));
          assert_ (pure (rep.signing_pub_key_repr == rep_new.signing_pub_key_repr));

          assert_ (V.pts_to st.signing_pub_key rep.signing_pub_key_repr);

          rewrite (V.pts_to st.signing_pub_key rep.signing_pub_key_repr) as
                  (V.pts_to new_st.signing_pub_key rep_new.signing_pub_key_repr);
          
          assert_ (V.pts_to #u8 new_st.signing_pub_key #1.0R rep_new.signing_pub_key_repr);
          
          fold (session_state_related (Initialized new_st) (G_Initialized rep_new));
          
          with _v. rewrite (C.ghost_pcm_pts_to #trace_pcm_t #trace_pcm _v (pcm_elt 1.0R tr1)) as
                           (C.ghost_pcm_pts_to (get_state_data (Initialized new_st)).g_trace_ref (pcm_elt 1.0R tr1));

          fold (spdm_inv (Initialized new_st) (get_state_data (Initialized new_st)).g_trace_ref tr1);
          
          assert_ (spdm_inv (Initialized new_st) (get_state_data (Initialized new_st)).g_trace_ref tr1 ** 
                   pure (G_Initialized? (current_state tr1) /\
                         g_key_of_gst (current_state tr1) == (current_key tr0) /\
                         g_key_len_of_gst (current_state tr1) == (get_state_data c).key_size));
          
          assert_ ( exists* (t:trace).
                    spdm_inv (Initialized new_st) (get_state_data (Initialized new_st)).g_trace_ref t ** 
                    pure (G_Initialized? (current_state t) /\
                    g_key_of_gst (current_state t) ==  (current_key tr0) /\
                    g_key_len_of_gst (current_state t) == (get_state_data c).key_size));

          fold (init_inv (get_state_data c).key_size (current_key tr0) (Initialized new_st));

          assert_ (init_inv (get_state_data c).key_size (current_key tr0) (Initialized new_st));
          
          new_state
        }
    }
  }


let valid_signature (signature msg key:Seq.seq u8):prop = admit()

fn 
 verify_sign 
         (ts_digest: V.vec u8{V.length ts_digest == hash_size})
         (sg: V.vec u8{V.length sg == signature_size})
         (pub_key:V.vec u8)
         (#ts_seq: (G.erased (Seq.seq u8)){Seq.length ts_seq == hash_size})
         (#sg_seq:(G.erased (Seq.seq u8)){Seq.length sg_seq == signature_size})
         (#p_seq:(G.erased (Seq.seq u8)))
    requires V.pts_to ts_digest ts_seq **
             V.pts_to sg sg_seq **
             V.pts_to pub_key p_seq
    returns res: bool
    ensures (V.pts_to ts_digest ts_seq **
             V.pts_to sg sg_seq **
             V.pts_to pub_key p_seq **
             pure( res == true ==> valid_signature sg_seq ts_seq p_seq))
{
  admit()
}

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
                hash_of hash_algo (current_transcript tr0 ) 
                (U32.uint_to_t(Seq.length b_req)) 
                 b_req 
                (U32.uint_to_t (Seq.length b_resp)) 
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
sign_resp_aux
  (ctx:parser_context)
  (req_size: u32{u32_v req_size > 0})
  (req:V.vec u8 { V.length req == u32_v req_size })
  (c:state)
  (st:st)
  (rep:repr)
  (res:spdm_measurement_result_t)
  (#tr0:trace {has_full_state_info (current_state tr0) })
  (#b_resp: Seq.seq u8{Seq.length b_resp > 0 /\ Seq.length b_resp == u32_v ctx.resp_size /\
                       (UInt.fits (Seq.length b_resp) U32.n)})
  (#b_req: Seq.seq u8{Seq.length b_req > 0 /\ Seq.length b_req == u32_v req_size /\
                      (UInt.fits (Seq.length b_req) U32.n)}) 
  (#p_req : perm)
  (#p_resp:perm)
  requires parser_post1 ctx res true **
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
                res.status == Success) **
           C.ghost_pcm_pts_to 
                  (get_state_data c).g_trace_ref
                  (Some #perm 1.0R, tr0)
           
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

    assert_ (pure(Seq.length curr_g_transcript == hash_size /\
                        u32_v req_size > 0 /\
                        Seq.length b_req == u32_v req_size));

    let new_g_transcript' = hash_seq hash_algo curr_g_transcript req_size b_req;
    let new_g_transcript = hash_seq hash_algo new_g_transcript' ctx.resp_size b_resp;
    
    assert_ (pure(V.length curr_state_transcript == hash_size));
    assert_ (V.pts_to curr_state_transcript curr_g_transcript);
    assert_ (V.pts_to req #p_req b_req);
    
    //hash update
    hash hash_algo curr_state_transcript req_size req #curr_g_transcript #b_req #p_req;
    assert_ (pure (Seq.equal new_g_transcript' (hash_seq hash_algo curr_g_transcript req_size b_req)));
    assert_ (V.pts_to curr_state_transcript new_g_transcript');
    hash hash_algo curr_state_transcript ctx.resp_size ctx.resp #new_g_transcript' #b_resp #p_resp;
    assert_ (V.pts_to curr_state_transcript new_g_transcript);
    //
    //Do the changes required for transitioning to G_Sign state and extend the trace
    let rep_new = {key_size_repr = curr_g_key_size; signing_pub_key_repr = curr_g_key; transcript = new_g_transcript};
   
    //bring in a lemma to prove this
    assume_ (pure(valid_transition tr0 (G_Recv_sign_resp rep_new)));
    let tr1 = next_trace tr0 (G_Recv_sign_resp rep_new);
    assert_ (pure (valid_transition tr0 (G_Recv_sign_resp rep_new)));
    extend_trace ((get_state_data c).g_trace_ref) tr0 ((G_Recv_sign_resp rep_new));
    assert_ (pure(G_Recv_sign_resp? (current_state tr1)));
    let new_st = {key_size = curr_state_key_size; 
                  signing_pub_key = curr_state_signing_pub_key; 
                  session_transcript = curr_state_transcript;
                  g_trace_ref = curr_state_data.g_trace_ref};

    //unfold parser post condition for SUCCESS result to bring the existence of sign coming out of the response
    assert_ (parser_post1 ctx res true);
    unfold (parser_post1 ctx res true);
    unfold (parser_success_post ctx res true);
    assert_ (exists* resp_repr. valid_resp0 ctx resp_repr **
                         valid_measurement_blocks ctx 
                         res.measurement_block_vector 
                         resp_repr.measurement_record **
                         V.pts_to res.sign resp_repr.signature **
                         pure (V.length res.sign == signature_size /\
                               V.length res.sign <> 0) );

    rewrite (V.pts_to st.signing_pub_key rep.signing_pub_key_repr) as
            (V.pts_to curr_state_signing_pub_key rep.signing_pub_key_repr);

    rewrite (V.pts_to curr_state_signing_pub_key rep.signing_pub_key_repr) as
            (V.pts_to curr_state_signing_pub_key curr_g_key);
    
    //with will help to bind the existential in the context. resp_repr.signature is in the context as an existential.
    with sg_seq. assert (V.pts_to res.sign sg_seq);

    //verify the signature
    let ret = verify_sign curr_state_transcript res.sign curr_state_signing_pub_key;
          
    assert_ (pure(ret == true ==> valid_signature sg_seq new_g_transcript curr_g_key));

    //fold back the parser post condition
    fold (parser_success_post ctx res true);
    fold (parser_post1 ctx res true);
    assert_ (pure(G_Recv_sign_resp? (current_state tr1)));
    assert_ (V.pts_to curr_state_signing_pub_key curr_g_key);
    
    //Do the changes required for transitioning to Initialized state and extend the trace
    let ts = Seq.create hash_size 0uy;
    let rep_new1 = {key_size_repr = curr_g_key_size; signing_pub_key_repr = curr_g_key; transcript = ts};
    let tr2 = next_trace tr1 (G_Initialized rep_new1);
    assert_ (pure (valid_transition tr1 (G_Initialized rep_new1)));
    extend_trace ((get_state_data c).g_trace_ref) tr1 ((G_Initialized rep_new1));
    assert_ (pure(G_Initialized? (current_state tr2)));
    assert_ (pure(G_Recv_sign_resp?(previous_current_state tr2)));
    assert_ (pure(exists hash_algo.  
                         hash_of hash_algo (current_transcript tr0 ) 
                        (U32.uint_to_t(Seq.length b_req)) 
                         b_req 
                        (U32.uint_to_t (Seq.length b_resp)) 
                        b_resp 
                        (g_transcript_of_gst (previous_current_state tr2 ))));

     assert_ (pure(valid_transition tr0 (previous_current_state tr2)));
     assert_ (pure(tr2 == next_next_trace tr0 (previous_current_state tr2 ) (current_state tr2)));

    //zero mem the current_transcript to transition to concrete Initialized state
    zeroize_vector curr_state_transcript;
    assert_ (exists* (s:Seq.seq U8.t).
                      V.pts_to curr_state_transcript s **
                      pure (Seq.length s == hash_size /\ (s `Seq.equal` Seq.create (Seq.length s) 0uy)));
             
    assert_ (pure(Seq.equal ts (Seq.create hash_size 0uy)));

    assert_ (V.pts_to curr_state_transcript ts);

    let new_st1 = {key_size = curr_state_key_size; 
                   signing_pub_key = curr_state_signing_pub_key; 
                   session_transcript = curr_state_transcript;
                   g_trace_ref = curr_state_data.g_trace_ref};
            
    //start folding back spdm_inv
    rewrite each
        curr_state_signing_pub_key as new_st1.signing_pub_key,
        curr_g_key as rep_new1.signing_pub_key_repr;
            
    with _v. rewrite (V.pts_to curr_state_transcript _v) as
                     (V.pts_to new_st1.session_transcript ts);

    assert_ (pure(st.signing_pub_key == new_st1.signing_pub_key));
    assert_ (pure (rep.signing_pub_key_repr == rep_new1.signing_pub_key_repr));
    
    
    assert_ (pure (new_st1.key_size == rep_new1.key_size_repr));

    assert_ ( V.pts_to new_st1.session_transcript rep_new1.transcript **
              V.pts_to new_st1.signing_pub_key rep_new1.signing_pub_key_repr **
              pure (new_st1.key_size == rep_new1.key_size_repr));
    fold (session_state_related (Initialized new_st1) (G_Initialized rep_new1));
    
    with _v. rewrite (C.ghost_pcm_pts_to #trace_pcm_t #trace_pcm _v (pcm_elt 1.0R tr2)) as
                     (C.ghost_pcm_pts_to (get_state_data (Initialized new_st1)).g_trace_ref (pcm_elt 1.0R tr2));

    fold (spdm_inv (Initialized new_st1) (get_state_data (Initialized new_st1)).g_trace_ref tr2);

    assert_ (pure (valid_transition tr0 (previous_current_state tr2) /\
                           tr2 == next_next_trace tr0 (previous_current_state tr2 ) (current_state tr2)));
            
    assert_ (pure (transition_related_sign_success tr0 tr2));
            
    assert_ (pure (previous_current_state tr2 == G_Recv_sign_resp rep_new));
           
    assert_ (pure(hash_result_success_sign1 tr0 tr2 #b_resp #b_req));
           
    assert_ (pure ((G_Initialized? (current_state tr2)) /\
                     (current_transcript tr2 == Seq.create hash_size 0uy) /\
                     G_Recv_sign_resp?(previous_current_state tr2)));
    
    assert_ (pure(ret == true ==> valid_signature sg_seq new_g_transcript curr_g_key));
    assert_ (pure(ret == true ==> valid_signature sg_seq new_g_transcript (g_key_of_gst (previous_current_state tr2))));
    assert_ (pure(ret == true ==> valid_signature sg_seq (g_transcript_of_gst  (previous_current_state tr2)) (g_key_of_gst (previous_current_state tr2))));
            
    assert_ (pure(ret == true ==> (exists (resp_rep:resp_repr ctx).
                                           valid_signature resp_rep.signature 
                                          (g_transcript_of_gst (previous_current_state tr2)) 
                                          (g_key_of_gst (previous_current_state tr2)))));

    if ret
           {
              let final_ret = {parser_result = res; curr_state = Initialized new_st1; sign_status = true};
              assert_ (pure(res.status == Success /\ ret == true ==> (exists (resp_rep:resp_repr ctx).
                                                           valid_signature resp_rep.signature 
                                                           (g_transcript_of_gst (previous_current_state tr2)) 
                                                           (g_key_of_gst (previous_current_state tr2)))));
              
              assert_ (pure(res.status == Success /\ ret == true ==> valid_signature_exists ctx tr2));
              assert_ (pure(res.status == Success ==> hash_result_success_sign1 tr0 tr2 #b_resp #b_req));
              assert_ (pure (res.status == Success ==> transition_related_sign_success tr0 tr2));
              assert_ (pure (res.status == Success ==> state_change_success_sign1 tr2));

              assert_ (pure (res.status == Success ==> 
                                  hash_result_success_sign1 tr0 tr2 #b_resp #b_req /\
                                  transition_related_sign_success tr0 tr2 /\
                                  state_change_success_sign1 tr2 /\
                                  (ret == true ==> valid_signature_exists ctx tr2)
              ));
              assert_ (pure (final_ret.parser_result.status == Success ==> 
                                  hash_result_success_sign1 tr0 tr2 #b_resp #b_req /\
                                  transition_related_sign_success tr0 tr2 /\
                                  state_change_success_sign1 tr2 /\
                                  (final_ret.sign_status == true ==> valid_signature_exists ctx tr2)
              ));

              assert_ (V.pts_to req #p_req b_req **
                       V.pts_to ctx.resp #p_resp b_resp **
                       parser_post1 ctx final_ret.parser_result true **
                       (exists* tr2.
                                spdm_inv final_ret.curr_state (get_state_data (final_ret.curr_state)).g_trace_ref tr2 **
                                pure (final_ret.parser_result.status == Success ==>
                                  state_change_success_sign1 tr2 /\ 
                                  hash_result_success_sign1 tr0 tr2 #b_resp #b_req /\
                                  transition_related_sign_success tr0 tr2 /\
                                  (final_ret.sign_status == true ==> valid_signature_exists ctx tr2))));

              final_ret
           }
           else
           {
              let final_ret = {parser_result = res; curr_state = Initialized new_st1; sign_status = false};
              assert_ (pure(res.status == Success /\ ret == true ==> (exists (resp_rep:resp_repr ctx).
                                                           valid_signature resp_rep.signature 
                                                           (g_transcript_of_gst (previous_current_state tr2)) 
                                                           (g_key_of_gst (previous_current_state tr2)))));
              
              assert_ (pure(res.status == Success /\ ret == true ==> valid_signature_exists ctx tr2));
              assert_ (pure(res.status == Success ==> hash_result_success_sign1 tr0 tr2 #b_resp #b_req));
              assert_ (pure (res.status == Success ==> transition_related_sign_success tr0 tr2));
              assert_ (pure (res.status == Success ==> state_change_success_sign1 tr2));
              assert_ (pure (res.status == Success ==> 
                                  hash_result_success_sign1 tr0 tr2 #b_resp #b_req /\
                                  transition_related_sign_success tr0 tr2 /\
                                  state_change_success_sign1 tr2 /\
                                  (ret == true ==> valid_signature_exists ctx tr2)));
              assert_ (pure (final_ret.parser_result.status == Success ==> 
                                  hash_result_success_sign1 tr0 tr2 #b_resp #b_req /\
                                  transition_related_sign_success tr0 tr2 /\
                                  state_change_success_sign1 tr2 /\
                                  (final_ret.sign_status == true ==> valid_signature_exists ctx tr2)
              ));
              final_ret
           } 

  }

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
    {
    let res = parser0 ctx #p_resp #b_resp true;
    match res.status {
      Parse_error -> {
        let tr1 = tr0;
        let r = (get_state_data c).g_trace_ref;
        assert_ (spdm_inv c ((get_state_data c).g_trace_ref) tr0);
        assert_ (spdm_inv c (get_state_data c).g_trace_ref tr1);
       rewrite 
        (spdm_inv c ((get_state_data c).g_trace_ref) tr0) as
        (spdm_inv c (get_state_data c).g_trace_ref tr1);
      
       assert_ (V.pts_to req #p_req b_req **
               V.pts_to ctx.resp #p_resp b_resp);

       assert_ (parser_post1 ctx res true);

       assert_ (V.pts_to req #p_req b_req **
               V.pts_to ctx.resp #p_resp b_resp **
               parser_post1 ctx res true);
       let ret = {parser_result = res; curr_state = c; sign_status = true};
       (*(res,c)*)
       ret
      }
      Success -> {
         //assert (spdm_inv c ((get_state_data c).g_trace_ref) tr0);
         unfold (spdm_inv c ((get_state_data c).g_trace_ref) tr0);
      
        //assert (session_state_related c (current_state tr0));
        unfold (session_state_related c (current_state tr0));

        let rep = get_gstate_data (current_state tr0);
      
        assert_ (pure (G_Recv_no_sign_resp? (current_state tr0) \/ G_Initialized? (current_state tr0)));
         match c {
        Initialized st -> {
           intro_session_state_tag_related (Initialized st) (current_state tr0);
           rewrite (session_state_related (Initialized st) (current_state tr0)) as
                   (session_state_related (Initialized st) (G_Initialized rep));
           
           unfold (session_state_related (Initialized st) (G_Initialized rep));
           
           assert_ (C.ghost_pcm_pts_to (get_state_data (Initialized st)).g_trace_ref (Some #perm 1.0R, tr0));
           
           assert_ (pure(c == Initialized st));
           rewrite (C.ghost_pcm_pts_to (get_state_data (Initialized st)).g_trace_ref (Some #perm 1.0R, tr0)) as
                   (C.ghost_pcm_pts_to (get_state_data c).g_trace_ref (Some #perm 1.0R, tr0));
           
           let ret = sign_resp_aux ctx req_size req c st rep res #tr0 #b_resp #b_req #p_req #p_resp;
           
           assert_ (pure(current_state tr0 == G_Initialized rep));
           

           assert_ ((V.pts_to req #p_req b_req **
                     V.pts_to ctx.resp #p_resp b_resp **
                     parser_post1 ctx ret.parser_result true **
                     (exists* (tr1:trace).
                           spdm_inv ret.curr_state (get_state_data (ret.curr_state)).g_trace_ref tr1 **
                           pure (ret.parser_result.status == Success ==>
                                  state_change_success_sign1 tr1 /\ 
                                  hash_result_success_sign1 tr0 tr1 #b_resp #b_req /\
                                  transition_related_sign_success tr0 tr1 /\
                                  (ret.sign_status == true ==> valid_signature_exists ctx tr1)
              ))) );
           ret
      }
      Recv_no_sign_resp st -> {
          intro_session_state_tag_related (Recv_no_sign_resp st) (current_state tr0);
           rewrite (session_state_related (Recv_no_sign_resp st) (current_state tr0)) as
                   (session_state_related (Recv_no_sign_resp st) (G_Recv_no_sign_resp rep));
           
           unfold (session_state_related (Recv_no_sign_resp st) (G_Recv_no_sign_resp rep));

           assert_ (C.ghost_pcm_pts_to (get_state_data (Recv_no_sign_resp st)).g_trace_ref (Some #perm 1.0R, tr0));
           
           assert_ (pure(c == Recv_no_sign_resp st));
           rewrite (C.ghost_pcm_pts_to (get_state_data (Recv_no_sign_resp st)).g_trace_ref (Some #perm 1.0R, tr0)) as
                   (C.ghost_pcm_pts_to (get_state_data c).g_trace_ref (Some #perm 1.0R, tr0));
           let ret = sign_resp_aux ctx req_size req c st rep res #tr0 #b_resp #b_req #p_req #p_resp;
           assert_ (pure(current_state tr0 == G_Recv_no_sign_resp rep));
           

           assert_ ((V.pts_to req #p_req b_req **
                     V.pts_to ctx.resp #p_resp b_resp **
                     parser_post1 ctx ret.parser_result true **
                     (exists* (tr1:trace).
                           spdm_inv ret.curr_state (get_state_data (ret.curr_state)).g_trace_ref tr1 **
                           pure (ret.parser_result.status == Success ==>
                                  state_change_success_sign1 tr1 /\ 
                                  hash_result_success_sign1 tr0 tr1 #b_resp #b_req /\
                                  transition_related_sign_success tr0 tr1 /\
                                  (ret.sign_status == true ==> valid_signature_exists ctx tr1)
              ))) );
           ret
        }

    }
    }
  }
}

