module Pulse.Lib.CircularBuffer

#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Vec
open FStar.SizeT
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module B = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module R = Pulse.Lib.Reference
module Spec = Pulse.Lib.CircularBuffer.Spec
open Pulse.Lib.CircularBuffer.Spec
module Pow2 = Pulse.Lib.CircularBuffer.Pow2
module GT = Pulse.Lib.CircularBuffer.GapTrack
module Mod = Pulse.Lib.CircularBuffer.Modular
module A = Pulse.Lib.Array

type byte = Spec.byte

/// Prove pow2_63 equals Prims.pow2 63 (checked by normalization, not Z3)
private let _pow2_63_eq : squash (pow2_63 = Prims.pow2 63) =
  assert_norm (pow2_63 = Prims.pow2 63)

/// Pre-compute pow2 64 so Z3 doesn't evaluate it for SZ.fits_u64_implies_fits
private let _pow2_64_val : squash (Prims.pow2 64 = 0x10000000000000000) =
  assert_norm (Prims.pow2 64 = 0x10000000000000000)

let lemma_nones_coherent (al:pos) (phys:Seq.seq byte{Seq.length phys == al}) (rs:nat{rs < al})
  : Lemma (Spec.phys_log_coherent al phys (GT.create_nones al) rs)
  = let aux (i:nat{i < al})
      : Lemma (Spec.coherent_at al phys (GT.create_nones al) rs i)
      = GT.create_nones_all_none al i
    in
    FStar.Classical.forall_intro aux

/// Platform assumption: SZ.t is at least 64 bits (true on all MsQuic targets).
assume val platform_fits_u64 : squash SZ.fits_u64

let lemma_idx_sum_fits (al: SZ.t) (a b: SZ.t)
  : Lemma (requires SZ.v a < SZ.v al /\ SZ.v b <= SZ.v al /\
                    SZ.v al > 0 /\ SZ.v al <= pow2_63)
          (ensures SZ.fits (SZ.v a + SZ.v b))
  = SZ.fits_u64_implies_fits (SZ.v a + SZ.v b)

let lemma_inc_fits (x: SZ.t) (bound: SZ.t)
  : Lemma (requires SZ.v x < SZ.v bound)
          (ensures SZ.fits (SZ.v x + 1))
  = SZ.fits_lte (SZ.v x + 1) (SZ.v bound)

/// Bridge: SZ.mod_spec equals Prims.op_Modulus for non-negative values
let lemma_mod_spec_eq (a: nat{SZ.fits a}) (b: pos{SZ.fits b})
  : Lemma (SZ.mod_spec a b == a % b)
  = FStar.Math.Lemmas.euclidean_division_definition a b

/// Prove that the copy loop produces exactly linearized_phys
let lemma_loop_is_linearized
  (old_al: pos) (new_al: pos)
  (old_phys: Seq.seq byte{Seq.length old_phys == old_al})
  (old_rs: nat{old_rs < old_al})
  (new_data: Seq.seq byte{Seq.length new_data == new_al})
  : Lemma
    (requires
      new_al >= old_al /\
      (forall (j:nat). j < old_al ==>
        Seq.index new_data j == Seq.index old_phys ((old_rs + j) % old_al)) /\
      (forall (j:nat). (old_al <= j /\ j < new_al) ==>
        Seq.index new_data j == 0uy))
    (ensures new_data == Spec.linearized_phys old_al new_al old_phys old_rs)
  = let expected = Spec.linearized_phys old_al new_al old_phys old_rs in
    let aux (j:nat{j < new_al})
      : Lemma (Seq.index new_data j == Seq.index expected j)
      = Mod.circular_index_in_bounds old_rs j old_al
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro new_data expected

/// Helper lemma: prove that Seq.upd maintains the resize loop invariant
let lemma_resize_invariant_step
  (old_al: pos) (new_al: pos)
  (old_phys: Seq.seq byte{Seq.length old_phys == old_al})
  (old_rs: nat{old_rs < old_al})
  (new_seq: Seq.seq byte{Seq.length new_seq == new_al})
  (vi: nat{vi < old_al /\ vi < new_al})
  (byte_val: byte)
  : Lemma
    (requires
      (forall (j:nat). j < vi ==>
        Seq.index new_seq j == Seq.index old_phys ((old_rs + j) % old_al)) /\
      (forall (j:nat). (vi <= j /\ j < new_al) ==>
        Seq.index new_seq j == 0uy) /\
      byte_val == Seq.index old_phys ((old_rs + vi) % old_al))
    (ensures (
      let new_seq' = Seq.upd new_seq vi byte_val in
      (forall (j:nat). j < vi + 1 ==>
        Seq.index new_seq' j == Seq.index old_phys ((old_rs + j) % old_al)) /\
      (forall (j:nat). (vi + 1 <= j /\ j < new_al) ==>
        Seq.index new_seq' j == 0uy)))
  = let new_seq' = Seq.upd new_seq vi byte_val in
    let aux (j:nat{j < new_al})
      : Lemma (
        (j < vi + 1 ==> Seq.index new_seq' j == Seq.index old_phys ((old_rs + j) % old_al)) /\
        (vi + 1 <= j ==> Seq.index new_seq' j == 0uy))
      = if j = vi then
          Seq.lemma_index_upd1 new_seq vi byte_val
        else
          Seq.lemma_index_upd2 new_seq vi byte_val j
    in
    FStar.Classical.forall_intro aux

noeq
type cb_internal = {
  buf: vec byte;        // Physical array (mutable via box for resize)
  rs: SZ.t;             // read_start (mutable)
  al: SZ.t;             // alloc_length (mutable, changes on resize)
  pl: SZ.t;             // prefix_length (mutable, tracks contiguous readable data)
  vl: SZ.t;             // virtual_length (constant)
  // base_offset is ghost-only (tracked via cb_state parameter)
}

type circular_buffer = box cb_internal

let is_circular_buffer ([@@@mkey]cb: circular_buffer) (st: Spec.cb_state) : slprop =
  exists* (cbi: cb_internal) (buf_data: Seq.seq byte).
    B.pts_to cb cbi **
    Vec.pts_to cbi.buf buf_data **
    pure (
      SZ.v cbi.al > 0 /\
      SZ.v cbi.al == st.alloc_length /\
      SZ.v cbi.vl == st.virtual_length /\
      SZ.v cbi.rs == st.read_start /\
      SZ.v cbi.pl == GT.contiguous_prefix_length st.contents /\
      Seq.length buf_data == SZ.v cbi.al /\
      is_full_vec cbi.buf /\
      Spec.cb_wf st /\
      SZ.v cbi.al <= pow2_63 /\
      st.virtual_length <= pow2_63 /\
      Spec.phys_log_coherent st.alloc_length buf_data st.contents st.read_start
    )

fn create
  (alloc_len: SZ.t{SZ.v alloc_len > 0})
  (virt_len: SZ.t{SZ.v virt_len > 0})
  requires pure (
    Pow2.is_pow2 (SZ.v alloc_len) /\
    Pow2.is_pow2 (SZ.v virt_len) /\
    SZ.v alloc_len <= SZ.v virt_len /\
    SZ.v virt_len <= pow2_63)
  returns cb : circular_buffer
  ensures exists* st.
    is_circular_buffer cb st **
    pure (Spec.cb_wf st /\
          st.base_offset == 0 /\
          st.alloc_length == SZ.v alloc_len /\
          st.virtual_length == SZ.v virt_len /\
          GT.contiguous_prefix_length st.contents == 0)
{
  let buf_vec : vec byte = alloc #byte 0uy alloc_len;
  let al_v : SZ.t = alloc_len;
  let vl_v : SZ.t = virt_len;
  
  let vi = Mkcb_internal buf_vec 0sz al_v 0sz vl_v;
  let cb = B.alloc vi;

  with buf_data. assert (Vec.pts_to buf_vec buf_data);
  lemma_nones_coherent (SZ.v alloc_len) buf_data 0;
  GT.prefix_of_nones (SZ.v alloc_len);
  
  rewrite (Vec.pts_to buf_vec buf_data) as (Vec.pts_to vi.buf buf_data);

  fold (is_circular_buffer cb {
    base_offset = 0; read_start = 0;
    alloc_length = SZ.v alloc_len; virtual_length = SZ.v virt_len;
    contents = GT.create_nones (SZ.v alloc_len)
  });
  cb
}

fn read_length
  (cb: circular_buffer) (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st ** pure (Spec.cb_wf st)
  returns n : SZ.t
  ensures is_circular_buffer cb st ** pure (SZ.v n == GT.contiguous_prefix_length st.contents)
{
  unfold (is_circular_buffer cb st);
  with cbi buf_data. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  let n = cb_val.pl;
  rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to cbi.buf buf_data);
  fold (is_circular_buffer cb st);
  n
}

fn write_byte
  (cb: circular_buffer) (offset: SZ.t) (b: byte) (new_pl: SZ.t)
  (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st **
    pure (Spec.cb_wf st /\ SZ.v offset < st.alloc_length /\
          SZ.v new_pl == GT.contiguous_prefix_length (Seq.upd st.contents (SZ.v offset) (Some b)))
  ensures is_circular_buffer cb (Spec.write_result st (SZ.v offset) b)
{
  unfold (is_circular_buffer cb st);
  with cbi buf_data. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  
  lemma_idx_sum_fits cb_val.al cb_val.rs offset;
  let sum = SZ.add cb_val.rs offset;
  let pidx = SZ.rem sum cb_val.al;
  cb_val.buf.(pidx) <- b;
  with buf_data'. assert (Vec.pts_to cb_val.buf buf_data');
  Spec.write_preserves_coherence st.alloc_length buf_data st.contents st.read_start (SZ.v offset) b;
  
  let new_cbi = Mkcb_internal cb_val.buf cb_val.rs cb_val.al new_pl cb_val.vl;
  ( := ) cb new_cbi;
  rewrite (Vec.pts_to cb_val.buf buf_data') as (Vec.pts_to new_cbi.buf buf_data');
  
  fold (is_circular_buffer cb (Spec.write_result st (SZ.v offset) b));
}

fn read_byte
  (cb: circular_buffer) (offset: SZ.t) (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st **
    pure (Spec.cb_wf st /\
          SZ.v offset < GT.contiguous_prefix_length st.contents /\
          SZ.v offset < Seq.length st.contents)
  returns b: byte
  ensures is_circular_buffer cb st **
    pure (SZ.v offset < Seq.length st.contents /\
          Some? (Seq.index st.contents (SZ.v offset)) /\
          b == Some?.v (Seq.index st.contents (SZ.v offset)))
{
  unfold (is_circular_buffer cb st);
  with cbi buf_data. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  
  lemma_idx_sum_fits cb_val.al cb_val.rs offset;
  let pidx = SZ.rem (SZ.add cb_val.rs offset) cb_val.al;
  lemma_mod_spec_eq (SZ.v (SZ.add cb_val.rs offset)) (SZ.v cb_val.al);
  GT.prefix_elements_are_some st.contents (SZ.v offset);
  assert (pure (Spec.coherent_at st.alloc_length buf_data st.contents st.read_start (SZ.v offset)));
  let b = cb_val.buf.(pidx);
  
  rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to cbi.buf buf_data);
  fold (is_circular_buffer cb st);
  b
}

fn drain
  (cb: circular_buffer) (n: SZ.t) (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st **
    pure (Spec.cb_wf st /\ SZ.v n <= st.alloc_length /\
          SZ.v n <= GT.contiguous_prefix_length st.contents)
  ensures is_circular_buffer cb (Spec.drain_result st (SZ.v n))
{
  unfold (is_circular_buffer cb st);
  with cbi buf_data. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  
  lemma_idx_sum_fits cb_val.al cb_val.rs n;
  let temp = SZ.add cb_val.rs n;
  let new_rs = SZ.rem temp cb_val.al;
  let new_pl = SZ.sub cb_val.pl n;
  
  let new_cbi = Mkcb_internal cb_val.buf new_rs cb_val.al new_pl cb_val.vl;
  ( := ) cb new_cbi;
  rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to new_cbi.buf buf_data);
  
  Spec.drain_preserves_coherence st.alloc_length buf_data st.contents st.read_start (SZ.v n);
  Spec.drain_prefix_length st.alloc_length st.contents (SZ.v n);
  fold (is_circular_buffer cb (Spec.drain_result st (SZ.v n)));
}

fn resize
  (cb: circular_buffer) (new_al: SZ.t{SZ.v new_al > 0})
  (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st **
    pure (Spec.cb_wf st /\ Pow2.is_pow2 (SZ.v new_al) /\
          SZ.v new_al >= st.alloc_length /\
          SZ.v new_al <= st.virtual_length /\
          SZ.v new_al <= pow2_63)
  ensures is_circular_buffer cb (Spec.resize_result st (SZ.v new_al))
{
  unfold (is_circular_buffer cb st);
  with cbi buf_data. _;

  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);

  let new_vec : vec byte = alloc #byte 0uy new_al;
  let mut i : SZ.t = 0sz;
  while (let vi = R.read i; SZ.lt vi cb_val.al)
  invariant exists* vi new_v.
    B.pts_to cb cbi ** Vec.pts_to cb_val.buf buf_data **
    R.pts_to i vi ** Vec.pts_to new_vec new_v **
    pure (SZ.v vi <= SZ.v cb_val.al /\
      Seq.length new_v == SZ.v new_al /\
      Seq.length buf_data == SZ.v cb_val.al /\
      is_full_vec cb_val.buf /\
      SZ.v cb_val.al <= pow2_63 /\
      SZ.v cb_val.al > 0 /\
      SZ.v cb_val.rs == st.read_start /\
      SZ.v cb_val.al == st.alloc_length /\
      (forall (j:nat). j < SZ.v vi ==>
        Seq.index new_v j == Seq.index buf_data ((st.read_start + j) % st.alloc_length)) /\
      (forall (j:nat). (SZ.v vi <= j /\ j < SZ.v new_al) ==>
        Seq.index new_v j == 0uy))
  {
    let vi = R.read i;
    with new_v. assert (Vec.pts_to new_vec new_v);
    lemma_idx_sum_fits cb_val.al cb_val.rs vi;
    let temp = SZ.add cb_val.rs vi;
    let src_idx = SZ.rem temp cb_val.al;
    lemma_mod_spec_eq (SZ.v temp) (SZ.v cb_val.al);
    
    assert (pure (SZ.v src_idx < Seq.length buf_data));
    let byte_val = cb_val.buf.(src_idx);
    assert (pure (byte_val == Seq.index buf_data ((st.read_start + SZ.v vi) % st.alloc_length)));
    new_vec.(vi) <- byte_val;
    with new_v'. assert (Vec.pts_to new_vec new_v');
    lemma_resize_invariant_step st.alloc_length (SZ.v new_al) buf_data st.read_start new_v (SZ.v vi) byte_val;
    lemma_inc_fits vi cb_val.al;
    R.write i (SZ.add vi 1sz);
  };
  with _vi _new_v. _;
  lemma_loop_is_linearized st.alloc_length (SZ.v new_al) buf_data st.read_start _new_v;
  assert (pure (_new_v == Spec.linearized_phys st.alloc_length (SZ.v new_al) buf_data st.read_start));
  Vec.free cb_val.buf;
  
  let new_cbi = Mkcb_internal new_vec 0sz new_al cb_val.pl cb_val.vl;
  ( := ) cb new_cbi;
  
  with new_buf_data. assert (Vec.pts_to new_vec new_buf_data);
  assert (pure (new_buf_data == _new_v));
  rewrite (Vec.pts_to new_vec new_buf_data) as (Vec.pts_to new_cbi.buf new_buf_data);
  
  Spec.linearize_preserves_coherence st.alloc_length (SZ.v new_al) buf_data st.contents st.read_start;
  Spec.resize_prefix_length st.alloc_length (SZ.v new_al) st.contents;
  fold (is_circular_buffer cb (Spec.resize_result st (SZ.v new_al)));
}

fn free
  (cb: circular_buffer) (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st
  ensures emp
{
  unfold (is_circular_buffer cb st);
  with cbi buf_data. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  Vec.free cb_val.buf;
  B.free cb;
}

fn get_alloc_length
  (cb: circular_buffer) (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st ** pure (Spec.cb_wf st)
  returns n : SZ.t
  ensures is_circular_buffer cb st ** pure (SZ.v n == st.alloc_length)
{
  unfold (is_circular_buffer cb st);
  with cbi buf_data. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  let n = cb_val.al;
  rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to cbi.buf buf_data);
  fold (is_circular_buffer cb st);
  n
}

#push-options "--z3rlimit_factor 64 --fuel 2 --ifuel 1"
fn write_buffer
  (cb: circular_buffer)
  (src: A.array byte)
  (write_len: SZ.t)
  (#p: perm)
  (#src_data: erased (Seq.seq byte))
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer cb st **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st /\
          Spec.gapless st /\
          SZ.v write_len == Seq.length src_data /\
          SZ.v write_len == A.length src /\
          GT.contiguous_prefix_length st.contents + SZ.v write_len <= st.virtual_length)
  returns new_data_ready: bool
  ensures exists* st'.
    is_circular_buffer cb st' **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st' /\
          Spec.gapless st' /\
          st'.base_offset == st.base_offset /\
          st'.virtual_length == st.virtual_length /\
          st'.alloc_length >= st.alloc_length /\
          GT.contiguous_prefix_length st'.contents ==
            GT.contiguous_prefix_length st.contents + SZ.v write_len /\
          new_data_ready == (SZ.v write_len > 0))
{
  // Step 1: Unfold and read current state
  unfold (is_circular_buffer cb st);
  with cbi buf_data. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);

  let needed = SZ.add cb_val.pl write_len;

  if SZ.gt needed cb_val.al
  {
    // --- RESIZE BRANCH ---
    // Compute new_al by doubling
    let mut nal_ref : SZ.t = cb_val.al;
    Pow2.next_pow2_ge_le_bound (SZ.v cb_val.al) (SZ.v needed) st.virtual_length;
    while (
      let cur = R.read nal_ref;
      SZ.lt cur needed
    )
    invariant exists* (nal_v: SZ.t).
      B.pts_to cb cbi ** Vec.pts_to cb_val.buf buf_data **
      A.pts_to src #p src_data **
      R.pts_to nal_ref nal_v **
      pure (
        SZ.v nal_v >= SZ.v cb_val.al /\
        Pow2.is_pow2 (SZ.v nal_v) /\
        SZ.v nal_v <= st.virtual_length /\
        SZ.v cb_val.al > 0 /\
        SZ.v cb_val.al == st.alloc_length /\
        SZ.v cb_val.rs == st.read_start /\
        SZ.v cb_val.pl == GT.contiguous_prefix_length st.contents /\
        Seq.length buf_data == SZ.v cb_val.al /\
        is_full_vec cb_val.buf /\
        SZ.v cb_val.al <= pow2_63 /\
        Pow2.is_pow2 st.virtual_length /\
        SZ.v needed <= st.virtual_length)
    {
      let cur = R.read nal_ref;
      Pow2.pow2_double_le (SZ.v cur) st.virtual_length;
      SZ.fits_lte (SZ.v cur + SZ.v cur) st.virtual_length;
      Pow2.doubling_stays_pow2 (SZ.v cur);
      R.write nal_ref (SZ.add cur cur);
    };

    let new_al = R.read nal_ref;

    // Now do the resize: allocate, copy (linearize), free old
    let new_vec : vec byte = alloc #byte 0uy new_al;
    let mut i : SZ.t = 0sz;
    while (let vi = R.read i; SZ.lt vi cb_val.al)
    invariant exists* vi new_v.
      B.pts_to cb cbi ** Vec.pts_to cb_val.buf buf_data **
      A.pts_to src #p src_data **
      R.pts_to i vi ** Vec.pts_to new_vec new_v **
      pure (SZ.v vi <= SZ.v cb_val.al /\
        Seq.length new_v == SZ.v new_al /\
        Seq.length buf_data == SZ.v cb_val.al /\
        is_full_vec cb_val.buf /\
        SZ.v cb_val.al <= pow2_63 /\
        SZ.v cb_val.al > 0 /\
        SZ.v cb_val.rs == st.read_start /\
        SZ.v cb_val.al == st.alloc_length /\
        SZ.v cb_val.pl == GT.contiguous_prefix_length st.contents /\
        SZ.v write_len == Seq.length src_data /\
        SZ.v write_len == A.length src /\
        (forall (j:nat). j < SZ.v vi ==>
          Seq.index new_v j == Seq.index buf_data ((st.read_start + j) % st.alloc_length)) /\
        (forall (j:nat). (SZ.v vi <= j /\ j < SZ.v new_al) ==>
          Seq.index new_v j == 0uy))
    {
      let vi = R.read i;
      with new_v. assert (Vec.pts_to new_vec new_v);
      lemma_idx_sum_fits cb_val.al cb_val.rs vi;
      let temp = SZ.add cb_val.rs vi;
      let src_idx = SZ.rem temp cb_val.al;
      lemma_mod_spec_eq (SZ.v temp) (SZ.v cb_val.al);
      
      assert (pure (SZ.v src_idx < Seq.length buf_data));
      let byte_val = cb_val.buf.(src_idx);
      assert (pure (byte_val == Seq.index buf_data ((st.read_start + SZ.v vi) % st.alloc_length)));
      new_vec.(vi) <- byte_val;
      with new_v'. assert (Vec.pts_to new_vec new_v');
      lemma_resize_invariant_step st.alloc_length (SZ.v new_al) buf_data st.read_start new_v (SZ.v vi) byte_val;
      lemma_inc_fits vi cb_val.al;
      R.write i (SZ.add vi 1sz);
    };
    with _vi _new_v. _;
    lemma_loop_is_linearized st.alloc_length (SZ.v new_al) buf_data st.read_start _new_v;
    assert (pure (_new_v == Spec.linearized_phys st.alloc_length (SZ.v new_al) buf_data st.read_start));
    Vec.free cb_val.buf;
    
    let new_cbi = Mkcb_internal new_vec 0sz new_al cb_val.pl cb_val.vl;
    ( := ) cb new_cbi;

    // After resize: rs=0, al=new_al, data linearized
    with new_buf_data. assert (Vec.pts_to new_vec new_buf_data);
    Spec.linearize_preserves_coherence st.alloc_length (SZ.v new_al) buf_data st.contents st.read_start;
    Spec.resize_prefix_length st.alloc_length (SZ.v new_al) st.contents;
    Spec.gapless_preserved_by_resize st (SZ.v new_al);

    // Now write the data using new_vec (rs=0, al=new_al)
    let cb_val2 = !cb;
    rewrite (Vec.pts_to new_vec new_buf_data) as (Vec.pts_to cb_val2.buf new_buf_data);

    let mut wi : SZ.t = 0sz;
    let mut pcont = SZ.lt 0sz write_len;
    while (let c = R.read pcont; c)
    invariant b. exists* (vi: SZ.t) (cur_phys: Seq.seq byte).
      R.pts_to pcont b **
      B.pts_to cb (hide new_cbi) ** Vec.pts_to cb_val2.buf cur_phys **
      A.pts_to src #p src_data **
      R.pts_to wi vi **
      pure (
        SZ.v vi <= SZ.v write_len /\
        b == (SZ.v vi < SZ.v write_len) /\
        Seq.length cur_phys == SZ.v new_al /\
        is_full_vec cb_val2.buf /\
        SZ.v new_al > 0 /\
        SZ.v new_al <= pow2_63 /\
        SZ.v new_al >= SZ.v needed /\
        SZ.v cb_val.pl == GT.contiguous_prefix_length st.contents /\
        SZ.v write_len == Seq.length src_data /\
        SZ.v write_len == A.length src /\
        SZ.v cb_val.pl + SZ.v write_len <= SZ.v new_al /\
        Pow2.is_pow2 (SZ.v new_al) /\
        Pow2.is_pow2 st.virtual_length /\
        SZ.v new_al <= st.virtual_length /\
        Spec.phys_log_coherent (SZ.v new_al) cur_phys
          (GT.write_range_contents
            (Spec.resized_contents st.alloc_length (SZ.v new_al) st.contents)
            (SZ.v cb_val.pl) (Seq.slice (reveal src_data) 0 (SZ.v vi)))
          0)
    {
      let vi = R.read wi;
      with cur_phys. assert (Vec.pts_to cb_val2.buf cur_phys);
      A.pts_to_len src;
      let byte_val = A.op_Array_Access src vi;
      let off = SZ.add cb_val.pl vi;
      SZ.fits_lte (SZ.v off) st.virtual_length;
      let pidx = SZ.rem off new_al;
      lemma_mod_spec_eq (SZ.v off) (SZ.v new_al);
      cb_val2.buf.(pidx) <- byte_val;
      Spec.write_step_coherence (SZ.v new_al) cur_phys
        (Spec.resized_contents st.alloc_length (SZ.v new_al) st.contents)
        0 (SZ.v cb_val.pl) (reveal src_data) (SZ.v vi);
      lemma_inc_fits vi write_len;
      let next_vi = SZ.add vi 1sz;
      R.write wi next_vi;
      R.write pcont (SZ.lt next_vi write_len);
    };

    with _vi _cur_phys. _;
    // Transfer coherence from loop's Seq.slice to full src_data via Spec lemma
    Spec.write_buffer_resize_coherence_transfer
      (SZ.v new_al) _cur_phys st.alloc_length st.contents
      (SZ.v cb_val.pl) (reveal src_data) (SZ.v _vi) (SZ.v write_len);
    let new_pl = SZ.add cb_val.pl write_len;
    
    let new_cbi2 = Mkcb_internal cb_val2.buf 0sz new_al new_pl cb_val.vl;
    ( := ) cb new_cbi2;
    rewrite (Vec.pts_to cb_val2.buf _cur_phys) as (Vec.pts_to new_cbi2.buf _cur_phys);

    // Prove fold conjuncts via standalone lemmas
    Spec.resize_prefix_length st.alloc_length (SZ.v new_al) st.contents;
    Spec.write_range_sequential_prefix (SZ.v new_al)
      (Spec.resized_contents st.alloc_length (SZ.v new_al) st.contents)
      (reveal src_data) (SZ.v cb_val.pl);
    Spec.write_buffer_resize_wf st (SZ.v new_al) (reveal src_data);
    Spec.write_buffer_resize_prefix st (SZ.v new_al) (reveal src_data);

    // Assert each fold conjunct separately so Z3 handles them as individual queries
    // (a) new alloc_length is positive
    assert (pure (SZ.v new_al > 0));
    // (b) al_v matches target alloc_length
    assert (pure (SZ.v new_al == SZ.v new_al));
    // (c) vl unchanged
    assert (pure (SZ.v cb_val.vl == st.virtual_length));
    // (d) rs matches target read_start
    assert (pure (SZ.v new_cbi2.rs == 0));
    // (e) prefix length — uses write_buffer_resize_prefix ensures
    assert (pure (
      SZ.v new_pl ==
      GT.contiguous_prefix_length
        (GT.write_range_contents
          (Spec.resized_contents st.alloc_length (SZ.v new_al) st.contents)
          (SZ.v cb_val.pl) (reveal src_data))));
    // (f) physical data length
    assert (pure (Seq.length _cur_phys == SZ.v new_al));
    // (g) vec is full
    assert (pure (is_full_vec new_cbi2.buf));
    // (h) cb_wf — uses write_buffer_resize_wf ensures
    assert (pure (
      Spec.cb_wf { st with
        read_start = 0;
        alloc_length = SZ.v new_al;
        contents = GT.write_range_contents
          (Spec.resized_contents st.alloc_length (SZ.v new_al) st.contents)
          (SZ.v cb_val.pl) (reveal src_data) }));
    // (i) alloc <= pow2_63
    assert (pure (SZ.v new_al <= pow2_63));
    // (j) virtual_length <= pow2_63
    assert (pure (st.virtual_length <= pow2_63));
    // (k) physical-logical coherence
    assert (pure (
      Spec.phys_log_coherent (SZ.v new_al) _cur_phys
        (GT.write_range_contents
          (Spec.resized_contents st.alloc_length (SZ.v new_al) st.contents)
          (SZ.v cb_val.pl) (reveal src_data))
        0));

    fold (is_circular_buffer cb
      { st with
          read_start = 0;
          alloc_length = SZ.v new_al;
          contents = GT.write_range_contents
            (Spec.resized_contents st.alloc_length (SZ.v new_al) st.contents)
            (SZ.v cb_val.pl) (reveal src_data) });
    let new_data_ready = SZ.gt write_len 0sz;
    new_data_ready
  }
  else
  {
    // --- NO RESIZE BRANCH ---
    // Track coherence directly in the loop invariant
    let mut wi : SZ.t = 0sz;
    while (let vi = R.read wi; SZ.lt vi write_len)
    invariant exists* (vi: SZ.t) (cur_phys: Seq.seq byte).
      B.pts_to cb cbi ** Vec.pts_to cb_val.buf cur_phys **
      A.pts_to src #p src_data **
      R.pts_to wi vi **
      pure (
        SZ.v vi <= SZ.v write_len /\
        Seq.length cur_phys == SZ.v cb_val.al /\
        is_full_vec cb_val.buf /\
        SZ.v cb_val.al > 0 /\
        SZ.v cb_val.al <= pow2_63 /\
        SZ.v cb_val.pl == GT.contiguous_prefix_length st.contents /\
        SZ.v cb_val.rs == st.read_start /\
        SZ.v cb_val.al == st.alloc_length /\
        SZ.v write_len == Seq.length src_data /\
        SZ.v write_len == A.length src /\
        SZ.v cb_val.pl + SZ.v write_len <= SZ.v cb_val.al /\
        st.read_start < st.alloc_length /\
        Spec.phys_log_coherent st.alloc_length cur_phys
          (GT.write_range_contents st.contents (SZ.v cb_val.pl)
            (Seq.slice (reveal src_data) 0 (SZ.v vi)))
          st.read_start)
    {
      let vi = R.read wi;
      with cur_phys. assert (Vec.pts_to cb_val.buf cur_phys);
      A.pts_to_len src;
      let byte_val = A.op_Array_Access src vi;
      let off = SZ.add cb_val.pl vi;
      lemma_idx_sum_fits cb_val.al cb_val.rs off;
      let pidx = SZ.rem (SZ.add cb_val.rs off) cb_val.al;
      lemma_mod_spec_eq (SZ.v (SZ.add cb_val.rs off)) (SZ.v cb_val.al);
      cb_val.buf.(pidx) <- byte_val;
      Spec.write_step_coherence (SZ.v cb_val.al) cur_phys st.contents
        st.read_start (SZ.v cb_val.pl) (reveal src_data) (SZ.v vi);
      lemma_inc_fits vi write_len;
      R.write wi (SZ.add vi 1sz);
    };

    with _vi _cur_phys. _;
    // Bridge: Seq.slice data 0 write_len `Seq.equal` data
    Seq.lemma_eq_intro (Seq.slice (reveal src_data) 0 (SZ.v write_len)) (reveal src_data);
    let new_pl = SZ.add cb_val.pl write_len;
    
    let new_cbi = Mkcb_internal cb_val.buf cb_val.rs cb_val.al new_pl cb_val.vl;
    ( := ) cb new_cbi;
    rewrite (Vec.pts_to cb_val.buf _cur_phys) as (Vec.pts_to new_cbi.buf _cur_phys);
    
    // Prefix + gapless
    Spec.write_range_sequential_prefix (SZ.v cb_val.al) st.contents
      (reveal src_data) (SZ.v cb_val.pl);
    fold (is_circular_buffer cb
      { st with contents = GT.write_range_contents st.contents (SZ.v cb_val.pl)
          (reveal src_data) });
    let new_data_ready = SZ.gt write_len 0sz;
    new_data_ready
  }
}
#pop-options

#push-options "--z3rlimit_factor 8"
fn read_buffer
  (cb: circular_buffer)
  (dst: A.array byte)
  (read_len: SZ.t)
  (#dst_data: erased (Seq.seq byte))
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer cb st **
    A.pts_to dst dst_data **
    pure (Spec.cb_wf st /\
          SZ.v read_len <= GT.contiguous_prefix_length st.contents /\
          SZ.v read_len <= st.alloc_length /\
          SZ.v read_len <= A.length dst /\
          A.is_full_array dst)
  ensures exists* (dst_data': Seq.seq byte).
    is_circular_buffer cb st **
    A.pts_to dst dst_data' **
    pure (Spec.cb_wf st /\
          SZ.v read_len <= Seq.length st.contents /\
          SZ.v read_len <= Seq.length dst_data' /\
          Seq.length dst_data' == Seq.length dst_data /\
          (forall (i:nat{i < SZ.v read_len}).
            Some? (Seq.index st.contents i) /\
            Seq.index dst_data' i == Some?.v (Seq.index st.contents i)))
{
  unfold (is_circular_buffer cb st);
  with cbi buf_data. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  A.pts_to_len dst;

  let mut ri : SZ.t = 0sz;
  while (let vi = R.read ri; SZ.lt vi read_len)
  invariant exists* (vi: SZ.t) (cur_dst: Seq.seq byte).
    B.pts_to cb cbi ** Vec.pts_to cb_val.buf buf_data **
    A.pts_to dst cur_dst **
    R.pts_to ri vi **
    pure (
      SZ.v vi <= SZ.v read_len /\
      SZ.v cb_val.al > 0 /\
      SZ.v cb_val.al <= pow2_63 /\
      SZ.v cb_val.al == st.alloc_length /\
      SZ.v cb_val.rs == st.read_start /\
      Seq.length buf_data == SZ.v cb_val.al /\
      Seq.length cur_dst == Seq.length dst_data /\
      is_full_vec cb_val.buf /\
      A.is_full_array dst /\
      SZ.v read_len <= SZ.v cb_val.al /\
      SZ.v read_len <= A.length dst /\
      SZ.v read_len <= Seq.length cur_dst /\
      SZ.v read_len <= GT.contiguous_prefix_length st.contents /\
      Spec.phys_log_coherent st.alloc_length buf_data st.contents st.read_start /\
      (forall (k:nat{k < SZ.v vi}).
        Some? (Seq.index st.contents k) /\
        Seq.index cur_dst k == Some?.v (Seq.index st.contents k)))
  {
    let vi = R.read ri;
    with cur_dst. assert (A.pts_to dst cur_dst);
    lemma_idx_sum_fits cb_val.al cb_val.rs vi;
    let pidx = SZ.rem (SZ.add cb_val.rs vi) cb_val.al;
    lemma_mod_spec_eq (SZ.v (SZ.add cb_val.rs vi)) (SZ.v cb_val.al);
    GT.prefix_elements_are_some st.contents (SZ.v vi);
    let byte_val = cb_val.buf.(pidx);
    A.op_Array_Assignment dst vi byte_val;
    with cur_dst'. assert (A.pts_to dst cur_dst');
    Spec.read_step_invariant (SZ.v cb_val.al) buf_data st.contents st.read_start cur_dst (SZ.v vi) byte_val;
    lemma_inc_fits vi read_len;
    R.write ri (SZ.add vi 1sz);
  };

  with _vi _cur_dst. _;
  rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to cbi.buf buf_data);
  fold (is_circular_buffer cb st);
}
#pop-options
