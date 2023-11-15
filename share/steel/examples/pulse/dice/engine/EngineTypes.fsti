module EngineTypes
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
open HACL

val uds_is_enabled : vprop

val uds_len : hashable_len 

type dice_return_code = | DICE_SUCCESS | DICE_ERROR

let cdi_t = A.larray U8.t (US.v (digest_len dice_hash_alg))

(* Engine Record *)
noeq
type engine_record_t = {
  l0_image_header_size : signable_len;
  l0_image_header      : A.larray U8.t (US.v l0_image_header_size);
  l0_image_header_sig  : A.larray U8.t 64; (* secret bytes *)
  l0_binary_size       : hashable_len;
  l0_binary            : A.larray U8.t (US.v l0_binary_size);
  l0_binary_hash       : A.larray U8.t (US.v dice_digest_len); (*secret bytes *)
  l0_image_auth_pubkey : A.larray U8.t 32; (* secret bytes *)
}

type engine_record_repr = {
    l0_image_header      : Seq.seq U8.t;
    l0_image_header_sig  : Seq.seq U8.t;
    l0_binary            : Seq.seq U8.t;
    l0_binary_hash       : Seq.seq U8.t;
    l0_image_auth_pubkey : Seq.seq U8.t;
}

let mk_engine_repr  l0_image_header_size l0_image_header l0_image_header_sig
                    l0_binary_size l0_binary l0_binary_hash l0_image_auth_pubkey
  = {l0_image_header_size; l0_image_header; l0_image_header_sig;
     l0_binary_size; l0_binary; l0_binary_hash; l0_image_auth_pubkey}

let engine_record_perm (record:engine_record_t) (p:perm) (repr:engine_record_repr)
  : vprop = 
  A.pts_to record.l0_image_header #p repr.l0_image_header **
  A.pts_to record.l0_image_header_sig #p repr.l0_image_header_sig **
  A.pts_to record.l0_binary #p repr.l0_binary **
  A.pts_to record.l0_binary_hash #p repr.l0_binary_hash **
  A.pts_to record.l0_image_auth_pubkey #p repr.l0_image_auth_pubkey
