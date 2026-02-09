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

/// Helper: prove that modular arithmetic identity holds

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
type circular_buffer = {
  buf: box (vec byte);  // Physical array (mutable via box for resize)
  rs: box SZ.t;         // read_start (mutable)
  al: box SZ.t;         // alloc_length (mutable, changes on resize)
  pl: box SZ.t;         // prefix_length (mutable, tracks contiguous readable data)
  vl: SZ.t;             // virtual_length (constant)
  // base_offset is ghost-only (tracked via cb_state parameter)
}

let is_circular_buffer ([@@@mkey]cb: circular_buffer) (st: Spec.cb_state) : slprop =
  exists* (buf_vec: vec byte) (buf_data: Seq.seq byte)
          (rs_v: SZ.t) (al_v: SZ.t) (pl_v: SZ.t).
    B.pts_to cb.buf buf_vec **
    Vec.pts_to buf_vec buf_data **
    B.pts_to cb.rs rs_v **
    B.pts_to cb.al al_v **
    B.pts_to cb.pl pl_v **
    pure (
      SZ.v al_v > 0 /\
      SZ.v al_v == st.alloc_length /\
      SZ.v cb.vl == st.virtual_length /\
      SZ.v rs_v == st.read_start /\
      SZ.v pl_v == GT.contiguous_prefix_length st.contents /\
      Seq.length buf_data == SZ.v al_v /\
      is_full_vec buf_vec /\
      Spec.cb_wf st /\
      SZ.v al_v <= pow2_63 /\
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
  let buf_box : box (vec byte) = B.alloc buf_vec;
  let rs_box : box SZ.t = B.alloc 0sz;
  let al_v : SZ.t = alloc_len;
  let al_box : box SZ.t = B.alloc al_v;
  let pl_box : box SZ.t = B.alloc 0sz;
  let vl_v : SZ.t = virt_len;
  let cb : circular_buffer = { buf = buf_box; rs = rs_box; al = al_box; pl = pl_box; vl = vl_v };
  
  with buf_v. assert (B.pts_to buf_box buf_v);
  rewrite (B.pts_to buf_box buf_v) as (B.pts_to cb.buf buf_v);
  with buf_data. assert (Vec.pts_to buf_v buf_data);
  lemma_nones_coherent (SZ.v alloc_len) buf_data 0;
  GT.prefix_of_nones (SZ.v alloc_len);
  with rs_v. assert (B.pts_to rs_box rs_v);
  rewrite (B.pts_to rs_box rs_v) as (B.pts_to cb.rs rs_v);
  with al_v. assert (B.pts_to al_box al_v);
  rewrite (B.pts_to al_box al_v) as (B.pts_to cb.al al_v);
  with pl_v. assert (B.pts_to pl_box pl_v);
  rewrite (B.pts_to pl_box pl_v) as (B.pts_to cb.pl pl_v);
  
  fold (is_circular_buffer cb {
    base_offset = 0; read_start = 0;
    alloc_length = SZ.v alloc_len; virtual_length = SZ.v virt_len;
    contents = GT.create_nones (SZ.v alloc_len)
  });
  cb
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
  with buf_vec buf_data rs_v al_v pl_v. _;
  let rs = !cb.rs;
  let al = !cb.al;
  let buf = !cb.buf;
  lemma_idx_sum_fits al rs offset;
  let sum = SZ.add rs offset;
  let pidx = SZ.rem sum al;
  buf.(pidx) <- b;
  with buf_data'. assert (Vec.pts_to buf buf_data');
  Spec.write_preserves_coherence st.alloc_length buf_data st.contents st.read_start (SZ.v offset) b;
  cb.pl := new_pl;
  fold (is_circular_buffer cb (Spec.write_result st (SZ.v offset) b));
}

fn read_length
  (cb: circular_buffer) (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st ** pure (Spec.cb_wf st)
  returns n : SZ.t
  ensures is_circular_buffer cb st ** pure (SZ.v n == GT.contiguous_prefix_length st.contents)
{
  unfold (is_circular_buffer cb st);
  with buf_vec buf_data rs_v al_v pl_v. _;
  let n = !cb.pl;
  fold (is_circular_buffer cb st);
  n
}

fn drain
  (cb: circular_buffer) (n: SZ.t) (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st **
    pure (Spec.cb_wf st /\ SZ.v n <= st.alloc_length /\
          SZ.v n <= GT.contiguous_prefix_length st.contents)
  ensures is_circular_buffer cb (Spec.drain_result st (SZ.v n))
{
  unfold (is_circular_buffer cb st);
  with buf_vec buf_data rs_v al_v pl_v. _;
  let rs = !cb.rs;
  let al = !cb.al;
  let pl = !cb.pl;
  lemma_idx_sum_fits al rs n;
  let temp = SZ.add rs n;
  let new_rs = SZ.rem temp al;
  cb.rs := new_rs;
  let new_pl = SZ.sub pl n;
  cb.pl := new_pl;
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
  with buf_vec buf_data rs_v al_v pl_v. _;
  let old_vec = !cb.buf;
  let rs = !cb.rs;
  let al = !cb.al;
  let new_vec : vec byte = alloc #byte 0uy new_al;
  let mut i : SZ.t = 0sz;
  while (let vi = R.read i; SZ.lt vi al)
  invariant exists* vi new_v.
    B.pts_to cb.buf old_vec ** Vec.pts_to old_vec buf_data **
    B.pts_to cb.rs rs ** B.pts_to cb.al al ** B.pts_to cb.pl pl_v **
    R.pts_to i vi ** Vec.pts_to new_vec new_v **
    pure (SZ.v vi <= SZ.v al /\
      Seq.length new_v == SZ.v new_al /\
      Seq.length buf_data == SZ.v al /\
      is_full_vec old_vec /\
      SZ.v al <= pow2_63 /\
      SZ.v al > 0 /\
      SZ.v rs == st.read_start /\
      SZ.v al == st.alloc_length /\
      (forall (j:nat). j < SZ.v vi ==>
        Seq.index new_v j == Seq.index buf_data ((st.read_start + j) % st.alloc_length)) /\
      (forall (j:nat). (SZ.v vi <= j /\ j < SZ.v new_al) ==>
        Seq.index new_v j == 0uy))
  {
    let vi = R.read i;
    with new_v. assert (Vec.pts_to new_vec new_v);
    lemma_idx_sum_fits al rs vi;
    let temp = SZ.add rs vi;
    let src_idx = SZ.rem temp al;
    lemma_mod_spec_eq (SZ.v temp) (SZ.v al);
    
    assert (pure (SZ.v src_idx < Seq.length buf_data));
    let byte_val = old_vec.(src_idx);
    assert (pure (byte_val == Seq.index buf_data ((st.read_start + SZ.v vi) % st.alloc_length)));
    new_vec.(vi) <- byte_val;
    with new_v'. assert (Vec.pts_to new_vec new_v');
    lemma_resize_invariant_step st.alloc_length (SZ.v new_al) buf_data st.read_start new_v (SZ.v vi) byte_val;
    lemma_inc_fits vi al;
    R.write i (SZ.add vi 1sz);
  };
  with _vi _new_v. _;
  lemma_loop_is_linearized st.alloc_length (SZ.v new_al) buf_data st.read_start _new_v;
  assert (pure (_new_v == Spec.linearized_phys st.alloc_length (SZ.v new_al) buf_data st.read_start));
  Vec.free old_vec;
  cb.buf := new_vec;
  cb.rs := 0sz;
  cb.al := new_al;
  with new_buf_data. assert (Vec.pts_to new_vec new_buf_data);
  assert (pure (new_buf_data == _new_v));
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
  with buf_vec buf_data rs_v al_v pl_v. _;
  let current_vec = !cb.buf;
  Vec.free current_vec;
  B.free cb.buf;
  B.free cb.rs;
  B.free cb.al;
  B.free cb.pl;
}

fn get_alloc_length
  (cb: circular_buffer) (#st: erased Spec.cb_state)
  requires is_circular_buffer cb st ** pure (Spec.cb_wf st)
  returns n : SZ.t
  ensures is_circular_buffer cb st ** pure (SZ.v n == st.alloc_length)
{
  unfold (is_circular_buffer cb st);
  with buf_vec buf_data rs_v al_v pl_v. _;
  let n = !cb.al;
  fold (is_circular_buffer cb st);
  n
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
  with buf_vec buf_data rs_v al_v pl_v. _;
  let rs = !cb.rs;
  let al = !cb.al;
  let buf = !cb.buf;
  lemma_idx_sum_fits al rs offset;
  let pidx = SZ.rem (SZ.add rs offset) al;
  lemma_mod_spec_eq (SZ.v (SZ.add rs offset)) (SZ.v al);
  GT.prefix_elements_are_some st.contents (SZ.v offset);
  assert (pure (Spec.coherent_at st.alloc_length buf_data st.contents st.read_start (SZ.v offset)));
  let b = buf.(pidx);
  fold (is_circular_buffer cb st);
  b
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
  with buf_vec buf_data rs_v al_v pl_v. _;
  let al = !cb.al;
  let rs = !cb.rs;
  let pl = !cb.pl;
  let buf = !cb.buf;

  let needed = SZ.add pl write_len;

  if SZ.gt needed al
  {
    // --- RESIZE BRANCH ---
    // Compute new_al by doubling
    let mut nal_ref : SZ.t = al;
    Pow2.next_pow2_ge_le_bound (SZ.v al) (SZ.v needed) st.virtual_length;
    while (
      let cur = R.read nal_ref;
      SZ.lt cur needed
    )
    invariant exists* (nal_v: SZ.t).
      B.pts_to cb.buf buf ** Vec.pts_to buf buf_data **
      B.pts_to cb.rs rs ** B.pts_to cb.al al ** B.pts_to cb.pl pl **
      A.pts_to src #p src_data **
      R.pts_to nal_ref nal_v **
      pure (
        SZ.v nal_v >= SZ.v al /\
        Pow2.is_pow2 (SZ.v nal_v) /\
        SZ.v nal_v <= st.virtual_length /\
        SZ.v al > 0 /\
        SZ.v al == st.alloc_length /\
        SZ.v rs == st.read_start /\
        SZ.v pl == GT.contiguous_prefix_length st.contents /\
        Seq.length buf_data == SZ.v al /\
        is_full_vec buf /\
        SZ.v al <= pow2_63 /\
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
    let mut j : SZ.t = 0sz;
    while (let vj = R.read j; SZ.lt vj al)
    invariant exists* vj new_v.
      B.pts_to cb.buf buf ** Vec.pts_to buf buf_data **
      B.pts_to cb.rs rs ** B.pts_to cb.al al ** B.pts_to cb.pl pl **
      A.pts_to src #p src_data **
      R.pts_to j vj ** Vec.pts_to new_vec new_v **
      pure (SZ.v vj <= SZ.v al /\
        Seq.length new_v == SZ.v new_al /\
        Seq.length buf_data == SZ.v al /\
        is_full_vec buf /\
        SZ.v al <= pow2_63 /\
        SZ.v al > 0 /\
        SZ.v rs == st.read_start /\
        SZ.v al == st.alloc_length /\
        (forall (k:nat). k < SZ.v vj ==>
          Seq.index new_v k == Seq.index buf_data ((st.read_start + k) % st.alloc_length)) /\
        (forall (k:nat). (SZ.v vj <= k /\ k < SZ.v new_al) ==>
          Seq.index new_v k == 0uy))
    {
      let vj = R.read j;
      with new_v. assert (Vec.pts_to new_vec new_v);
      lemma_idx_sum_fits al rs vj;
      let temp = SZ.add rs vj;
      let src_idx = SZ.rem temp al;
      lemma_mod_spec_eq (SZ.v temp) (SZ.v al);
      let byte_val = buf.(src_idx);
      new_vec.(vj) <- byte_val;
      with new_v'. assert (Vec.pts_to new_vec new_v');
      lemma_resize_invariant_step st.alloc_length (SZ.v new_al) buf_data st.read_start new_v (SZ.v vj) byte_val;
      lemma_inc_fits vj al;
      R.write j (SZ.add vj 1sz);
    };
    with _vj _new_v. _;
    lemma_loop_is_linearized st.alloc_length (SZ.v new_al) buf_data st.read_start _new_v;
    Vec.free buf;
    cb.buf := new_vec;
    cb.rs := 0sz;
    cb.al := new_al;

    // After resize: rs=0, al=new_al, data linearized
    with new_buf_data. assert (Vec.pts_to new_vec new_buf_data);
    Spec.linearize_preserves_coherence st.alloc_length (SZ.v new_al) buf_data st.contents st.read_start;
    Spec.resize_prefix_length st.alloc_length (SZ.v new_al) st.contents;
    Spec.gapless_preserved_by_resize st (SZ.v new_al);

    // Now write the data using new_vec (rs=0, al=new_al)
    let new_al_v = new_al;
    let new_rs : SZ.t = 0sz;
    let new_buf = !cb.buf;
    rewrite (Vec.pts_to new_vec new_buf_data) as (Vec.pts_to new_buf new_buf_data);

    let mut wi : SZ.t = 0sz;
    let mut pcont = SZ.lt 0sz write_len;
    while (let c = R.read pcont; c)
    invariant b. exists* (vi: SZ.t) (cur_phys: Seq.seq byte).
      R.pts_to pcont b **
      B.pts_to cb.buf new_buf ** Vec.pts_to new_buf cur_phys **
      B.pts_to cb.rs new_rs ** B.pts_to cb.al new_al_v ** B.pts_to cb.pl pl **
      A.pts_to src #p src_data **
      R.pts_to wi vi **
      pure (
        SZ.v vi <= SZ.v write_len /\
        b == (SZ.v vi < SZ.v write_len) /\
        Seq.length cur_phys == SZ.v new_al /\
        is_full_vec new_buf /\
        SZ.v new_al > 0 /\
        SZ.v new_al <= pow2_63 /\
        SZ.v new_al >= SZ.v needed /\
        SZ.v pl == GT.contiguous_prefix_length st.contents /\
        SZ.v write_len == Seq.length src_data /\
        SZ.v write_len == A.length src /\
        SZ.v pl + SZ.v write_len <= SZ.v new_al /\
        Pow2.is_pow2 (SZ.v new_al) /\
        Pow2.is_pow2 st.virtual_length /\
        SZ.v new_al <= st.virtual_length /\
        Spec.phys_log_coherent (SZ.v new_al) cur_phys
          (GT.write_range_contents
            (Spec.resized_contents st.alloc_length (SZ.v new_al) st.contents)
            (SZ.v pl) (Seq.slice (reveal src_data) 0 (SZ.v vi)))
          0)
    {
      let vi = R.read wi;
      with cur_phys. assert (Vec.pts_to new_buf cur_phys);
      A.pts_to_len src;
      let byte_val = A.op_Array_Access src vi;
      let off = SZ.add pl vi;
      SZ.fits_lte (SZ.v off) st.virtual_length;
      let pidx = SZ.rem off new_al_v;
      lemma_mod_spec_eq (SZ.v off) (SZ.v new_al_v);
      new_buf.(pidx) <- byte_val;
      Spec.write_step_coherence (SZ.v new_al) cur_phys
        (Spec.resized_contents st.alloc_length (SZ.v new_al) st.contents)
        0 (SZ.v pl) (reveal src_data) (SZ.v vi);
      lemma_inc_fits vi write_len;
      let next_vi = SZ.add vi 1sz;
      R.write wi next_vi;
      R.write pcont (SZ.lt next_vi write_len);
    };

    with _vi _cur_phys. _;
    // Transfer coherence from loop's Seq.slice to full src_data via Spec lemma
    Spec.write_buffer_resize_coherence_transfer
      (SZ.v new_al) _cur_phys st.alloc_length st.contents
      (SZ.v pl) (reveal src_data) (SZ.v _vi) (SZ.v write_len);
    let new_pl = SZ.add pl write_len;
    cb.pl := new_pl;

    // Prove fold conjuncts via standalone lemmas
    Spec.resize_prefix_length st.alloc_length (SZ.v new_al) st.contents;
    Spec.write_range_sequential_prefix (SZ.v new_al)
      (Spec.resized_contents st.alloc_length (SZ.v new_al) st.contents)
      (reveal src_data) (SZ.v pl);
    Spec.write_buffer_resize_wf st (SZ.v new_al) (reveal src_data);
    Spec.write_buffer_resize_prefix st (SZ.v new_al) (reveal src_data);

    // Assert each fold conjunct separately so Z3 handles them as individual queries
    // (a) new alloc_length is positive
    assert (pure (SZ.v new_al > 0));
    // (b) al_v matches target alloc_length
    assert (pure (SZ.v new_al_v == SZ.v new_al));
    // (c) vl unchanged
    assert (pure (SZ.v cb.vl == st.virtual_length));
    // (d) rs matches target read_start
    assert (pure (SZ.v new_rs == 0));
    // (e) prefix length — uses write_buffer_resize_prefix ensures
    assert (pure (
      SZ.v new_pl ==
      GT.contiguous_prefix_length
        (GT.write_range_contents
          (Spec.resized_contents st.alloc_length (SZ.v new_al) st.contents)
          (SZ.v pl) (reveal src_data))));
    // (f) physical data length
    assert (pure (Seq.length _cur_phys == SZ.v new_al_v));
    // (g) vec is full
    assert (pure (is_full_vec new_buf));
    // (h) cb_wf — uses write_buffer_resize_wf ensures
    assert (pure (
      Spec.cb_wf { st with
        read_start = 0;
        alloc_length = SZ.v new_al;
        contents = GT.write_range_contents
          (Spec.resized_contents st.alloc_length (SZ.v new_al) st.contents)
          (SZ.v pl) (reveal src_data) }));
    // (i) alloc <= pow2_63
    assert (pure (SZ.v new_al_v <= pow2_63));
    // (j) virtual_length <= pow2_63
    assert (pure (st.virtual_length <= pow2_63));
    // (k) physical-logical coherence
    assert (pure (
      Spec.phys_log_coherent (SZ.v new_al) _cur_phys
        (GT.write_range_contents
          (Spec.resized_contents st.alloc_length (SZ.v new_al) st.contents)
          (SZ.v pl) (reveal src_data))
        0));

    fold (is_circular_buffer cb
      { st with
          read_start = 0;
          alloc_length = SZ.v new_al;
          contents = GT.write_range_contents
            (Spec.resized_contents st.alloc_length (SZ.v new_al) st.contents)
            (SZ.v pl) (reveal src_data) });
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
      B.pts_to cb.buf buf ** Vec.pts_to buf cur_phys **
      B.pts_to cb.rs rs ** B.pts_to cb.al al ** B.pts_to cb.pl pl **
      A.pts_to src #p src_data **
      R.pts_to wi vi **
      pure (
        SZ.v vi <= SZ.v write_len /\
        Seq.length cur_phys == SZ.v al /\
        is_full_vec buf /\
        SZ.v al > 0 /\
        SZ.v al <= pow2_63 /\
        SZ.v pl == GT.contiguous_prefix_length st.contents /\
        SZ.v rs == st.read_start /\
        SZ.v al == st.alloc_length /\
        SZ.v write_len == Seq.length src_data /\
        SZ.v write_len == A.length src /\
        SZ.v pl + SZ.v write_len <= SZ.v al /\
        st.read_start < st.alloc_length /\
        Spec.phys_log_coherent st.alloc_length cur_phys
          (GT.write_range_contents st.contents (SZ.v pl)
            (Seq.slice (reveal src_data) 0 (SZ.v vi)))
          st.read_start)
    {
      let vi = R.read wi;
      with cur_phys. assert (Vec.pts_to buf cur_phys);
      A.pts_to_len src;
      let byte_val = A.op_Array_Access src vi;
      let off = SZ.add pl vi;
      lemma_idx_sum_fits al rs off;
      let pidx = SZ.rem (SZ.add rs off) al;
      lemma_mod_spec_eq (SZ.v (SZ.add rs off)) (SZ.v al);
      buf.(pidx) <- byte_val;
      Spec.write_step_coherence (SZ.v al) cur_phys st.contents
        st.read_start (SZ.v pl) (reveal src_data) (SZ.v vi);
      lemma_inc_fits vi write_len;
      R.write wi (SZ.add vi 1sz);
    };

    with _vi _cur_phys. _;
    // Bridge: Seq.slice data 0 write_len `Seq.equal` data
    Seq.lemma_eq_intro (Seq.slice (reveal src_data) 0 (SZ.v write_len)) (reveal src_data);
    let new_pl = SZ.add pl write_len;
    cb.pl := new_pl;
    // Prefix + gapless
    Spec.write_range_sequential_prefix (SZ.v al) st.contents
      (reveal src_data) (SZ.v pl);
    fold (is_circular_buffer cb
      { st with contents = GT.write_range_contents st.contents (SZ.v pl)
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
  with buf_vec buf_data rs_v al_v pl_v. _;
  let al = !cb.al;
  let rs = !cb.rs;
  let buf = !cb.buf;
  A.pts_to_len dst;

  let mut ri : SZ.t = 0sz;
  while (let vi = R.read ri; SZ.lt vi read_len)
  invariant exists* (vi: SZ.t) (cur_dst: Seq.seq byte).
    B.pts_to cb.buf buf ** Vec.pts_to buf buf_data **
    B.pts_to cb.rs rs ** B.pts_to cb.al al ** B.pts_to cb.pl pl_v **
    A.pts_to dst cur_dst **
    R.pts_to ri vi **
    pure (
      SZ.v vi <= SZ.v read_len /\
      SZ.v al > 0 /\
      SZ.v al <= pow2_63 /\
      SZ.v al == st.alloc_length /\
      SZ.v rs == st.read_start /\
      Seq.length buf_data == SZ.v al /\
      Seq.length cur_dst == Seq.length dst_data /\
      is_full_vec buf /\
      A.is_full_array dst /\
      SZ.v read_len <= SZ.v al /\
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
    lemma_idx_sum_fits al rs vi;
    let pidx = SZ.rem (SZ.add rs vi) al;
    lemma_mod_spec_eq (SZ.v (SZ.add rs vi)) (SZ.v al);
    GT.prefix_elements_are_some st.contents (SZ.v vi);
    let byte_val = buf.(pidx);
    A.op_Array_Assignment dst vi byte_val;
    with cur_dst'. assert (A.pts_to dst cur_dst');
    Spec.read_step_invariant (SZ.v al) buf_data st.contents st.read_start cur_dst (SZ.v vi) byte_val;
    lemma_inc_fits vi read_len;
    R.write ri (SZ.add vi 1sz);
  };

  with _vi _cur_dst. _;
  fold (is_circular_buffer cb st);
}
#pop-options
