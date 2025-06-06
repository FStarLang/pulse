module EverCrypt.Hash.Incremental
include Spec.Hash.Definitions
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module U8 = FStar.UInt8
module U32 = FStar.UInt32

/// From EverCrypt.Hash.Incremental.hash_len
val hash_len : a:hash_alg -> v:U32.t { a == sha2_256 ==> v == 32ul}

noextract [@@noextract_to "krml"]
let hash_length (a: hash_alg) : Tot nat = U32.v (hash_len a)

/// From Spec.Hash.Definitions.less_than_max_input_length
noextract [@@noextract_to "krml"]
val less_than_max_input_length: nat -> hash_alg -> bool
val less_than_max_input_length_intro // needed by EverCrypt.HMAC.compute_st_spec_hmac_intro
  (x: nat)
  (a: hash_alg)
: Lemma
  (requires
    x < pow2 61
  )
  (ensures
    x `less_than_max_input_length` a
  )
  [SMTPat (x `less_than_max_input_length` a)]

/// From Spec.Agile.Hash.hash
noextract [@@noextract_to "krml"]
val spec_hash 
  (a:hash_alg) 
  (s:Seq.seq U8.t) 
  : (s:Seq.seq U8.t{ Seq.length s = hash_length a })

/// From EverCrypt.Hash.Incremental.hash
val hash : 
  a:hash_alg ->
  output:A.array U8.t {A.length output == hash_length a} ->
  input:A.array U8.t ->
  p_input: perm ->
  v_input: Ghost.erased (Seq.seq U8.t) ->
  input_len:U32.t {A.length input = U32.v input_len /\ U32.v input_len `less_than_max_input_length` a} ->
  stt unit
  (requires
    EverCrypt.AutoConfig2.initialized ** // see https://github.com/hacl-star/hacl-star/blob/59723f7dde13bd7b7eb90491f1385b4e3ee2904f/providers/evercrypt/fst/EverCrypt.Hash.Incremental.fst#L292-L294
    pts_to input #p_input v_input **
      (exists* v_output . pts_to output v_output)
  )
  (ensures fun _ ->
    EverCrypt.AutoConfig2.initialized **
    pts_to input #p_input v_input **
      pts_to output (spec_hash a v_input))
