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

// We assume a combinator to run pulse computations for initialization of top-level state, it gets primitive support in extraction
assume val run_stt (#a:Type) (#post:a -> slprop) (f:stt a emp post) : a

// We assume this code will be executed on a machine where u32 fits the word size
assume SZ_fits_u32 : SZ.fits_u32

let trace_ref : gref = admit()

fn __init (s:state) (t:trace) (key_len:u32) (signing_key:V.vec u8 { V.length signing_key == U32.v key_len})
  requires spdm_inv s trace_ref t
  returns r:(st & state)
  ensures spdm_inv (snd r) trace_ref t **
          (exists* p b. V.pts_to signing_key #p b **
                   init_client_perm (snd r) b key_len)



assume val emptyVector : v:V.vec u8{V.length v = 0}
 
 //since the pre-condition has V.pts_to signing_key #p b. post-condition also has that
 //how to bring in init_client_perm r b key_len?
 //how to bring in b? That is the seq version of signing_key

fn init  (key_len:u32) (signing_key:V.vec u8 { V.length signing_key == U32.v key_len })
  requires (exists* p b. V.pts_to signing_key #p b)
  returns r:(state)
  ensures (exists* p b. V.pts_to signing_key #p b ** 
                                        init_client_perm r b key_len)
{
   let st =  { key_size = key_len; signing_pub_key = signing_key; session_transcript = emptyVector};
   Initialized st;
   _assume (valid_transition emp_trace G_UnInitialized);
   ghost_write trace_ref (None, emp_trace);
   ghost_write trace_ref (None, emp_trace) 
                         (Some 1.0R, (next_trace emp_trace G_UnInitialized));
   ghost_write trace_ref (Some 1.0R, (next_trace emp_trace G_UnInitialized))
                         (Some 1.0R, (next_trace emp_trace G_Initialized));
   admit()
} 


(*noextract
let next_trace (t:trace) (s:g_state { valid_transition t s }) : trace =
  match t with
  | [] -> [[s]]
  | hd::tl ->
    match hd with
    | [] -> [s]::t
    | l -> (s::l)::t //t == l::tl
*)



//Figure out the trace
//Write that trace to trace_ref using ghost_write
//assume the post condition of ghost_write and see if the invaraint can be proved.


(*let init_client_perm (s:state) (b:Seq.seq u8) (key_len:u32): slprop =
  exists* (t:trace). spdm_inv s trace_ref t ** 
                                   pure (G_Initialized? (current_state t) /\
                                        g_key_of_gst (current_state t) == b /\
                                        g_key_len_of_gst (current_state t) == key_len
                                        )
*)







