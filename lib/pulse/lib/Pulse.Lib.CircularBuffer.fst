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
module RM = Pulse.Lib.RangeVec
module RMSpec = Pulse.Lib.RangeMap.Spec
module PTR = Pulse.Lib.Array.PtsToRange
open Pulse.Lib.Trade

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

/// cb_max_length fits in SZ.t (follows from cb_max_length <= pow2_63 and fits_u64)
let cb_max_length_sz : SZ.t =
  SZ.fits_u64_implies_fits Spec.cb_max_length;
  SZ.uint_to_t Spec.cb_max_length

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
  bo: SZ.t;             // base_offset (absolute stream position of read_start)
}

type circular_buffer = box cb_internal

let is_circular_buffer
  ([@@@mkey]cb: circular_buffer)
  (rm: RM.range_vec_t)
  (st: Spec.cb_state) : slprop =
  exists* (cbi: cb_internal) (buf_data: Seq.seq byte) (repr: Seq.seq RMSpec.interval).
    B.pts_to cb cbi **
    Vec.pts_to cbi.buf buf_data **
    RM.is_range_vec rm repr **
    pure (
      SZ.v cbi.al > 0 /\
      SZ.v cbi.al == st.alloc_length /\
      SZ.v cbi.vl == st.virtual_length /\
      SZ.v cbi.rs == st.read_start /\
      SZ.v cbi.bo == st.base_offset /\
      SZ.v cbi.pl == RMSpec.contiguous_from repr (SZ.v cbi.bo) /\
      SZ.v cbi.pl == GT.contiguous_prefix_length st.contents /\
      Seq.length buf_data == SZ.v cbi.al /\
      is_full_vec cbi.buf /\
      Spec.cb_wf st /\
      SZ.v cbi.al <= pow2_63 /\
      st.virtual_length <= pow2_63 /\
      Spec.phys_log_coherent st.alloc_length buf_data st.contents st.read_start /\
      Spec.ranges_match_contents repr st.contents (SZ.v cbi.bo) /\
      RMSpec.range_map_wf repr /\
      Spec.repr_well_positioned repr (SZ.v cbi.bo) /\
      (Seq.length repr = 0 \/ (Seq.index repr 0).low >= SZ.v cbi.bo) /\
      Seq.length repr < RM.max_range_vec_entries
    )

/// Get the length of contiguous readable data
fn read_length
  (cb: circular_buffer) (rm: RM.range_vec_t)
  (#st: erased Spec.cb_state)
  requires is_circular_buffer cb rm st
  returns n : SZ.t
  ensures is_circular_buffer cb rm st **
          pure (SZ.v n == GT.contiguous_prefix_length st.contents)
{
  unfold (is_circular_buffer cb rm st);
  with cbi buf_data repr. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  let n = cb_val.pl;
  rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to cbi.buf buf_data);
  fold (is_circular_buffer cb rm st);
  n
}

fn get_total_length
  (cb: circular_buffer) (rm: RM.range_vec_t)
  (#st: erased Spec.cb_state)
  requires is_circular_buffer cb rm st
  returns n: SZ.t
  ensures is_circular_buffer cb rm st **
          pure (SZ.v n <= st.base_offset + st.alloc_length)
{
  unfold (is_circular_buffer cb rm st);
  with cbi buf_data repr. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  let n = RM.range_vec_max_endpoint rm;
  rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to cbi.buf buf_data);
  RMSpec.range_map_max_endpoint_bounded repr (SZ.v cbi.bo + SZ.v cbi.al);
  fold (is_circular_buffer cb rm st);
  n
}

fn set_virtual_length
  (cb: circular_buffer) (rm: RM.range_vec_t) (new_vl: SZ.t{SZ.v new_vl > 0})
  (#st: erased Spec.cb_state)
  requires is_circular_buffer cb rm st **
    pure (Spec.cb_wf st /\
          Pow2.is_pow2 (SZ.v new_vl) /\
          SZ.v new_vl >= st.virtual_length /\
          SZ.v new_vl <= pow2_63)
  ensures is_circular_buffer cb rm ({ st with virtual_length = SZ.v new_vl })
{
  unfold (is_circular_buffer cb rm st);
  with cbi buf_data repr. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  let new_cbi = Mkcb_internal cb_val.buf cb_val.rs cb_val.al cb_val.pl new_vl cb_val.bo;
  ( := ) cb new_cbi;
  rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to new_cbi.buf buf_data);
  fold (is_circular_buffer cb rm ({ st with virtual_length = SZ.v new_vl }));
  ()
}

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 4"
fn create
  (alloc_len: SZ.t{SZ.v alloc_len > 0})
  (virt_len: SZ.t{SZ.v virt_len > 0})
  requires pure (
    Pow2.is_pow2 (SZ.v alloc_len) /\
    Pow2.is_pow2 (SZ.v virt_len) /\
    SZ.v alloc_len <= SZ.v virt_len /\
    SZ.v alloc_len <= Spec.cb_max_length /\
    SZ.v virt_len <= pow2_63)
  returns res : (circular_buffer & RM.range_vec_t)
  ensures exists* st.
    is_circular_buffer (fst res) (snd res) st **
    pure (Spec.cb_wf st /\
          st.base_offset == 0 /\
          st.alloc_length == SZ.v alloc_len /\
          st.virtual_length == SZ.v virt_len /\
          GT.contiguous_prefix_length st.contents == 0)
{
  let buf_vec : vec byte = alloc #byte 0uy alloc_len;
  let al_v : SZ.t = alloc_len;
  let vl_v : SZ.t = virt_len;

  let vi = Mkcb_internal buf_vec 0sz al_v 0sz vl_v 0sz;
  let cb = B.alloc vi;
  let rm = RM.range_vec_create ();

  with buf_data. assert (Vec.pts_to buf_vec buf_data);
  lemma_nones_coherent (SZ.v alloc_len) buf_data 0;
  GT.prefix_of_nones (SZ.v alloc_len);
  Spec.ranges_match_create_nones (SZ.v alloc_len);

  rewrite (Vec.pts_to buf_vec buf_data) as (Vec.pts_to vi.buf buf_data);

  fold (is_circular_buffer cb rm ({
    base_offset = 0; read_start = 0;
    alloc_length = SZ.v alloc_len; virtual_length = SZ.v virt_len;
    contents = GT.create_nones (SZ.v alloc_len)
  }));
  (cb, rm)
}
#pop-options

/// Resize: grow buffer while preserving range map bridge.
fn resize
  (cb: circular_buffer) (rm: RM.range_vec_t) (new_al: SZ.t{SZ.v new_al > 0})
  (#st: erased Spec.cb_state)
  requires is_circular_buffer cb rm st **
    pure (Spec.cb_wf st /\ Pow2.is_pow2 (SZ.v new_al) /\
          SZ.v new_al >= st.alloc_length /\
          SZ.v new_al <= st.virtual_length /\
          SZ.v new_al <= Spec.cb_max_length /\
          SZ.v new_al <= pow2_63)
  ensures is_circular_buffer cb rm (Spec.resize_result st (SZ.v new_al))
{
  unfold (is_circular_buffer cb rm st);
  with cbi buf_data repr. _;

  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);

  let new_vec : vec byte = alloc #byte 0uy new_al;
  let mut i : SZ.t = 0sz;
  while (let vi = R.read i; SZ.lt vi cb_val.al)
  invariant exists* vi new_v.
    B.pts_to cb cbi ** Vec.pts_to cb_val.buf buf_data **
    RM.is_range_vec rm repr **
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

  let new_cbi = Mkcb_internal new_vec 0sz new_al cb_val.pl cb_val.vl cb_val.bo;
  ( := ) cb new_cbi;

  with new_buf_data. assert (Vec.pts_to new_vec new_buf_data);
  assert (pure (new_buf_data == _new_v));
  rewrite (Vec.pts_to new_vec new_buf_data) as (Vec.pts_to new_cbi.buf new_buf_data);

  Spec.linearize_preserves_coherence st.alloc_length (SZ.v new_al) buf_data st.contents st.read_start;
  Spec.resize_prefix_length st.alloc_length (SZ.v new_al) st.contents;
  Spec.ranges_match_resize repr st.contents (SZ.v cb_val.bo) st.alloc_length (SZ.v new_al);
  fold (is_circular_buffer cb rm (Spec.resize_result st (SZ.v new_al)));
}

fn free
  (cb: circular_buffer) (rm: RM.range_vec_t) (#st: erased Spec.cb_state)
  requires is_circular_buffer cb rm st
  ensures emp
{
  unfold (is_circular_buffer cb rm st);
  with cbi buf_data repr. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  Vec.free cb_val.buf;
  RM.range_vec_free rm;
  B.free cb;
}

fn get_alloc_length
  (cb: circular_buffer) (rm: RM.range_vec_t) (#st: erased Spec.cb_state)
  requires is_circular_buffer cb rm st ** pure (Spec.cb_wf st)
  returns n : SZ.t
  ensures is_circular_buffer cb rm st ** pure (SZ.v n == st.alloc_length)
{
  unfold (is_circular_buffer cb rm st);
  with cbi buf_data repr. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  let n = cb_val.al;
  rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to cbi.buf buf_data);
  fold (is_circular_buffer cb rm st);
  n
}

#push-options "--z3rlimit_factor 4"
fn read_buffer
  (cb: circular_buffer)
  (rm: RM.range_vec_t)
  (dst: A.array byte)
  (read_len: SZ.t)
  (#dst_data: erased (Seq.seq byte))
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer cb rm st **
    A.pts_to dst dst_data **
    pure (Spec.cb_wf st /\
          SZ.v read_len <= GT.contiguous_prefix_length st.contents /\
          SZ.v read_len <= st.alloc_length /\
          SZ.v read_len <= A.length dst /\
          A.is_full_array dst)
  ensures exists* (dst_data': Seq.seq byte).
    is_circular_buffer cb rm st **
    A.pts_to dst dst_data' **
    pure (Spec.cb_wf st /\
          SZ.v read_len <= Seq.length st.contents /\
          SZ.v read_len <= Seq.length dst_data' /\
          Seq.length dst_data' == Seq.length dst_data /\
          (forall (i:nat{i < SZ.v read_len}).
            Some? (Seq.index st.contents i) /\
            Seq.index dst_data' i == Some?.v (Seq.index st.contents i)))
{
  unfold (is_circular_buffer cb rm st);
  with cbi buf_data repr. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  A.pts_to_len dst;

  let mut ri : SZ.t = 0sz;
  while (let vi = R.read ri; SZ.lt vi read_len)
  invariant exists* (vi: SZ.t) (cur_dst: Seq.seq byte).
    B.pts_to cb cbi ** Vec.pts_to cb_val.buf buf_data **
    RM.is_range_vec rm repr **
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
  fold (is_circular_buffer cb rm st);
}
#pop-options

/// Internal helper: out-of-order write at a relative offset,
/// updates both the physical buffer and the range map, and computes exact new prefix.
#push-options "--z3rlimit_factor 32 --fuel 2 --ifuel 1"
fn write_buffer_core
  (cb: circular_buffer)
  (rm: RM.range_vec_t)
  (offset: SZ.t)
  (src: A.array byte)
  (write_len: SZ.t)
  (#p: perm)
  (#src_data: erased (Seq.seq byte))
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer cb rm st **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st /\
          SZ.v write_len == Seq.length src_data /\
          SZ.v write_len == A.length src /\
          SZ.v write_len > 0 /\
          SZ.v offset + SZ.v write_len <= st.alloc_length /\
          SZ.fits (st.base_offset + SZ.v offset + SZ.v write_len))
  ensures exists* st'.
    is_circular_buffer cb rm st' **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st' /\
          st'.base_offset == st.base_offset /\
          st'.virtual_length == st.virtual_length /\
          st'.alloc_length == st.alloc_length /\
          st'.read_start == st.read_start /\
          st'.contents == GT.write_range_contents_t st.contents (SZ.v offset) (reveal src_data) /\
          GT.contiguous_prefix_length st'.contents >=
            GT.contiguous_prefix_length st.contents)
{
  unfold (is_circular_buffer cb rm st);
  with cbi buf_data repr. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  A.pts_to_len src;

  // Write loop: copy src into physical array at (rs + offset + i) % al
  let mut wi : SZ.t = 0sz;
  while (let vi = R.read wi; SZ.lt vi write_len)
  invariant exists* (vi: SZ.t) (cur_phys: Seq.seq byte).
    B.pts_to cb cbi ** Vec.pts_to cb_val.buf cur_phys **
    A.pts_to src #p src_data **
    RM.is_range_vec rm repr **
    R.pts_to wi vi **
    pure (
      SZ.v vi <= SZ.v write_len /\
      Seq.length cur_phys == SZ.v cb_val.al /\
      is_full_vec cb_val.buf /\
      SZ.v cb_val.al > 0 /\
      SZ.v cb_val.al <= pow2_63 /\
      SZ.v cb_val.rs == st.read_start /\
      SZ.v cb_val.al == st.alloc_length /\
      SZ.v write_len == Seq.length src_data /\
      SZ.v write_len == A.length src /\
      SZ.v offset + SZ.v write_len <= SZ.v cb_val.al /\
      st.read_start < st.alloc_length /\
      Spec.phys_log_coherent st.alloc_length cur_phys
        (GT.write_range_contents st.contents (SZ.v offset)
          (Seq.slice (reveal src_data) 0 (SZ.v vi)))
        st.read_start)
  {
    let vi = R.read wi;
    with cur_phys. assert (Vec.pts_to cb_val.buf cur_phys);
    A.pts_to_len src;
    let byte_val = A.op_Array_Access src vi;
    let off = SZ.add offset vi;
    lemma_idx_sum_fits cb_val.al cb_val.rs off;
    let pidx = SZ.rem (SZ.add cb_val.rs off) cb_val.al;
    lemma_mod_spec_eq (SZ.v (SZ.add cb_val.rs off)) (SZ.v cb_val.al);
    cb_val.buf.(pidx) <- byte_val;
    Spec.write_step_coherence (SZ.v cb_val.al) cur_phys st.contents
      st.read_start (SZ.v offset) (reveal src_data) (SZ.v vi);
    lemma_inc_fits vi write_len;
    R.write wi (SZ.add vi 1sz);
  };

  with _vi _cur_phys. _;
  // Bridge: Seq.slice data 0 write_len == data
  Seq.lemma_eq_intro (Seq.slice (reveal src_data) 0 (SZ.v write_len)) (reveal src_data);

  // Coherence transfer
  Spec.write_ooo_coherence_transfer (SZ.v cb_val.al) _cur_phys st.contents
    st.read_start (SZ.v offset) (reveal src_data) (SZ.v _vi) (SZ.v write_len);

  // Bridge: total version equals partial version (precondition holds)
  GT.write_range_contents_t_eq st.contents (SZ.v offset) (reveal src_data);

  // Prefix monotonicity
  GT.write_range_monotone st.contents (SZ.v offset) (reveal src_data);

  // cb_wf preserved
  Spec.write_range_preserves_wf st (SZ.v offset) (reveal src_data);

  // Update range map with absolute offset (bo + offset)
  let abs_offset = SZ.add cb_val.bo offset;
  RM.range_vec_add rm abs_offset write_len;

  // Bridge preservation (using absolute offsets)
  RMSpec.add_range_wf repr (SZ.v abs_offset) (SZ.v write_len);
  Spec.ranges_match_write repr st.contents (SZ.v cb_val.bo) (SZ.v offset) (reveal src_data);

  // Compute new prefix length from range map using base_offset
  let new_pl = RM.range_vec_contiguous_from rm cb_val.bo;

  // Update cb with new pl
  let new_cbi = Mkcb_internal cb_val.buf cb_val.rs cb_val.al new_pl cb_val.vl cb_val.bo;
  ( := ) cb new_cbi;
  rewrite (Vec.pts_to cb_val.buf _cur_phys) as (Vec.pts_to new_cbi.buf _cur_phys);

  // repr_well_positioned preservation
  Spec.write_preserves_rwp repr (SZ.v cb_val.bo) (SZ.v offset) (SZ.v write_len);

  // cf == cpl after write
  Spec.write_preserves_cf_eq_cpl repr st.contents (SZ.v cb_val.bo) (SZ.v offset) (reveal src_data);

  // Bounded: add_range preserves boundedness
  RMSpec.add_range_bounded repr (SZ.v abs_offset) (SZ.v write_len) (SZ.v cb_val.bo + SZ.v cb_val.al);

  // Count bound: first.low >= bo preserved by add_range
  RMSpec.add_range_first_low repr (SZ.v abs_offset) (SZ.v write_len) (SZ.v cb_val.bo);
  // now: |add_range repr ...| > 0 /\ first'.low >= bo
  // so repr_count_bound_gap applies
  Spec.repr_count_bound_gap (RMSpec.add_range repr (SZ.v abs_offset) (SZ.v write_len))
    (SZ.v cb_val.bo) (SZ.v cb_val.al);
  // gives: 2 * |repr'| <= al + 1 <= pow2_63 + 1, so |repr'| <= pow2_62 < max

  fold (is_circular_buffer cb rm
    { st with contents =
        GT.write_range_contents_t st.contents (SZ.v offset) (reveal src_data) });
}
#pop-options

/// Absolute-offset write with trim, auto-resize, and failure handling.
/// Handles stale writes (no-op), partial overlap trim, auto-resize up to cb_max_length.
/// Returns write_result with wrote/new_data_ready/resize_failed flags.
#push-options "--z3rlimit_factor 32 --fuel 2 --ifuel 1"
fn write_buffer
  (cb: circular_buffer) (rm: RM.range_vec_t)
  (abs_offset: SZ.t) (src: A.array byte) (write_len: SZ.t)
  (#p: perm)
  (#src_data: erased (Seq.seq byte))
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer cb rm st **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st /\
          SZ.v write_len == Seq.length src_data /\
          SZ.v write_len == A.length src /\
          SZ.v write_len > 0 /\
          SZ.v abs_offset + SZ.v write_len <= st.base_offset + st.virtual_length /\
          SZ.fits (SZ.v abs_offset + SZ.v write_len))
  returns wr: write_result
  ensures exists* st'.
    is_circular_buffer cb rm st' **
    A.pts_to src #p src_data **
    pure (Spec.cb_wf st' /\
          st'.base_offset == st.base_offset /\
          st'.virtual_length == st.virtual_length /\
          (not wr.wrote ==> st'.alloc_length == st.alloc_length /\
                            st'.read_start == st.read_start /\
                            st'.contents == st.contents) /\
          (wr.wrote ==> st'.alloc_length >= st.alloc_length /\
                        GT.contiguous_prefix_length st'.contents >=
                          GT.contiguous_prefix_length st.contents))
{
  // Step 1: Read base_offset and alloc_length
  unfold (is_circular_buffer cb rm st);
  with cbi buf_data repr. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  let bo = cb_val.bo;
  let al = cb_val.al;
  let old_pl = cb_val.pl;

  // Step 2: Check stale (abs_end <= base_offset)
  let abs_end = SZ.add abs_offset write_len;
  if SZ.lte abs_end bo
  {
    // Fully stale — no-op
    rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to cbi.buf buf_data);
    fold (is_circular_buffer cb rm st);
    { wrote = false; new_data_ready = false; resize_failed = false }
  }
  else
  {
    // Step 3: Compute trim params
    // rel_offset: how far into buffer to start writing
    // skip: how many src bytes to skip (already consumed)
    let rel_offset : SZ.t =
      (if SZ.gte abs_offset bo then SZ.sub abs_offset bo
       else 0sz);
    let skip : SZ.t =
      (if SZ.lt abs_offset bo then SZ.sub bo abs_offset
       else 0sz);
    let trimmed_len = SZ.sub write_len skip;

    // The furthest point from base_offset the write reaches
    let needed = SZ.add rel_offset trimmed_len;

    // Step 4: Check if resize needed
    if SZ.gt needed al
    {
      // Need to resize — check if it fits within cb_max_length
      // Compute the needed new_al by doubling
      Pow2.next_pow2_ge_le_bound (SZ.v al) (SZ.v needed) st.virtual_length;
      // Check if doubling can reach needed within cb_max_length
      if SZ.gt needed cb_max_length_sz
      {
        // Resize would exceed max — return failure
        rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to cbi.buf buf_data);
        fold (is_circular_buffer cb rm st);
        { wrote = false; new_data_ready = false; resize_failed = true }
      }
      else
      {
        // Compute new_al by doubling loop
        let mut nal_ref : SZ.t = al;
        while (
          let cur = R.read nal_ref;
          SZ.lt cur needed
        )
        invariant exists* (nal_v: SZ.t).
          B.pts_to cb cbi ** Vec.pts_to cb_val.buf buf_data **
          A.pts_to src #p src_data **
          RM.is_range_vec rm repr **
          R.pts_to nal_ref nal_v **
          pure (
            SZ.v nal_v >= SZ.v al /\
            Pow2.is_pow2 (SZ.v nal_v) /\
            SZ.v nal_v <= st.virtual_length /\
            SZ.v nal_v <= Spec.cb_max_length /\
            SZ.v al > 0 /\
            SZ.v al == st.alloc_length /\
            SZ.v cb_val.rs == st.read_start /\
            Seq.length buf_data == SZ.v al /\
            is_full_vec cb_val.buf /\
            SZ.v al <= pow2_63 /\
            Pow2.is_pow2 st.virtual_length /\
            SZ.v needed <= st.virtual_length /\
            SZ.v needed <= Spec.cb_max_length)
        {
          let cur = R.read nal_ref;
          Pow2.pow2_double_le (SZ.v cur) st.virtual_length;
          Pow2.pow2_double_le (SZ.v cur) Spec.cb_max_length;
          SZ.fits_lte (SZ.v cur + SZ.v cur) st.virtual_length;
          Pow2.doubling_stays_pow2 (SZ.v cur);
          R.write nal_ref (SZ.add cur cur);
        };
        let new_al = R.read nal_ref;

        // Fold back to call resize
        rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to cbi.buf buf_data);
        fold (is_circular_buffer cb rm st);
        resize cb rm new_al;

        // After resize, unfold to write inline
        A.pts_to_len src;
        Spec.trim_write_in_bounds (SZ.v abs_offset) (SZ.v write_len) st.base_offset (SZ.v new_al);

        unfold (is_circular_buffer cb rm (Spec.resize_result st (SZ.v new_al)));
        with cbi2 buf_data2 repr2. _;
        let cb_val2 = !cb;
        rewrite (Vec.pts_to cbi2.buf buf_data2) as (Vec.pts_to cb_val2.buf buf_data2);
        A.pts_to_len src;

        // Write loop: copy src[skip..] into physical array
        let mut wi : SZ.t = 0sz;
        while (let vi = R.read wi; SZ.lt vi trimmed_len)
        invariant exists* (vi: SZ.t) (cur_phys: Seq.seq byte).
          B.pts_to cb cbi2 ** Vec.pts_to cb_val2.buf cur_phys **
          A.pts_to src #p src_data **
          RM.is_range_vec rm repr2 **
          R.pts_to wi vi **
          pure (
            SZ.v vi <= SZ.v trimmed_len /\
            Seq.length cur_phys == SZ.v cb_val2.al /\
            is_full_vec cb_val2.buf /\
            SZ.v cb_val2.al > 0 /\
            SZ.v cb_val2.al <= pow2_63 /\
            SZ.v cb_val2.rs < SZ.v cb_val2.al /\
            SZ.v trimmed_len + SZ.v skip == SZ.v write_len /\
            SZ.v write_len == Seq.length src_data /\
            SZ.v write_len == A.length src /\
            SZ.v rel_offset + SZ.v trimmed_len <= SZ.v cb_val2.al /\
            Spec.phys_log_coherent (SZ.v cb_val2.al) cur_phys
              (GT.write_range_contents (Spec.resize_result st (SZ.v new_al)).contents
                (SZ.v rel_offset)
                (Seq.slice (reveal src_data) (SZ.v skip) (SZ.v skip + SZ.v vi)))
              (SZ.v cb_val2.rs))
        {
          let vi = R.read wi;
          with cur_phys. assert (Vec.pts_to cb_val2.buf cur_phys);
          A.pts_to_len src;
          let src_idx = SZ.add skip vi;
          let byte_val = A.op_Array_Access src src_idx;
          let off = SZ.add rel_offset vi;
          lemma_idx_sum_fits cb_val2.al cb_val2.rs off;
          let pidx = SZ.rem (SZ.add cb_val2.rs off) cb_val2.al;
          lemma_mod_spec_eq (SZ.v (SZ.add cb_val2.rs off)) (SZ.v cb_val2.al);
          cb_val2.buf.(pidx) <- byte_val;
          Spec.write_step_coherence (SZ.v cb_val2.al) cur_phys
            (Spec.resize_result st (SZ.v new_al)).contents
            (SZ.v cb_val2.rs) (SZ.v rel_offset)
            (Seq.slice (reveal src_data) (SZ.v skip) (SZ.v write_len)) (SZ.v vi);
          lemma_inc_fits vi trimmed_len;
          R.write wi (SZ.add vi 1sz);
        };

        with _vi _cur_phys. _;
        let trimmed_data = Ghost.hide (Seq.slice (reveal src_data) (SZ.v skip) (SZ.v write_len));
        Seq.lemma_eq_intro
          (Seq.slice (reveal src_data) (SZ.v skip) (SZ.v skip + SZ.v trimmed_len))
          (reveal trimmed_data);
        Seq.lemma_eq_intro
          (Seq.slice (reveal trimmed_data) 0 (SZ.v trimmed_len))
          (reveal trimmed_data);

        let rs_contents = Ghost.hide (Spec.resize_result st (SZ.v new_al)).contents;
        Spec.write_ooo_coherence_transfer (SZ.v cb_val2.al) _cur_phys
          rs_contents (SZ.v cb_val2.rs) (SZ.v rel_offset)
          (reveal trimmed_data) (SZ.v _vi) (SZ.v trimmed_len);
        GT.write_range_contents_t_eq rs_contents (SZ.v rel_offset) (reveal trimmed_data);
        GT.write_range_monotone rs_contents (SZ.v rel_offset) (reveal trimmed_data);
        Spec.resize_prefix_length st.alloc_length (SZ.v new_al) st.contents;

        let new_st_contents = Ghost.hide (
          GT.write_range_contents_t rs_contents (SZ.v rel_offset) (reveal trimmed_data));
        Spec.write_range_preserves_wf (Spec.resize_result st (SZ.v new_al))
          (SZ.v rel_offset) (reveal trimmed_data);

        // Update range map with absolute offset
        let rm_abs = SZ.add cb_val2.bo rel_offset;
        RM.range_vec_add rm rm_abs trimmed_len;
        RMSpec.add_range_wf repr2 (SZ.v rm_abs) (SZ.v trimmed_len);
        Spec.ranges_match_write repr2 rs_contents (SZ.v cb_val2.bo) (SZ.v rel_offset) (reveal trimmed_data);

        let new_pl = RM.range_vec_contiguous_from rm cb_val2.bo;
        let ndr = SZ.gt new_pl 0sz && SZ.eq old_pl 0sz;

        let new_cbi = Mkcb_internal cb_val2.buf cb_val2.rs cb_val2.al new_pl cb_val2.vl cb_val2.bo;
        ( := ) cb new_cbi;
        rewrite (Vec.pts_to cb_val2.buf _cur_phys) as (Vec.pts_to new_cbi.buf _cur_phys);

        let rs_st = Ghost.hide (Spec.resize_result st (SZ.v new_al));
        Spec.write_preserves_rwp repr2 (SZ.v cb_val2.bo) (SZ.v rel_offset) (SZ.v trimmed_len);
        Spec.write_preserves_cf_eq_cpl repr2 (reveal rs_st).contents (SZ.v cb_val2.bo) (SZ.v rel_offset) (reveal trimmed_data);

        // Bounded: add_range preserves boundedness
        RMSpec.add_range_bounded repr2 (SZ.v rm_abs) (SZ.v trimmed_len) (SZ.v cb_val2.bo + SZ.v cb_val2.al);

        // Count bound: first.low >= bo preserved, then derive count < max
        RMSpec.add_range_first_low repr2 (SZ.v rm_abs) (SZ.v trimmed_len) (SZ.v cb_val2.bo);
        Spec.repr_count_bound_gap (RMSpec.add_range repr2 (SZ.v rm_abs) (SZ.v trimmed_len))
          (SZ.v cb_val2.bo) (SZ.v cb_val2.al);

        fold (is_circular_buffer cb rm
          { Spec.resize_result st (SZ.v new_al) with contents = reveal new_st_contents });
        { wrote = true; new_data_ready = ndr; resize_failed = false }
      }
    }
    else
    {
      // No resize needed — write directly
      A.pts_to_len src;
      Spec.trim_write_in_bounds (SZ.v abs_offset) (SZ.v write_len) st.base_offset st.alloc_length;

      // Write loop: copy src[skip..] into buffer at (rs + rel_offset + i) % al
      let mut wi : SZ.t = 0sz;
      while (let vi = R.read wi; SZ.lt vi trimmed_len)
      invariant exists* (vi: SZ.t) (cur_phys: Seq.seq byte).
        B.pts_to cb cbi ** Vec.pts_to cb_val.buf cur_phys **
        A.pts_to src #p src_data **
        RM.is_range_vec rm repr **
        R.pts_to wi vi **
        pure (
          SZ.v vi <= SZ.v trimmed_len /\
          Seq.length cur_phys == SZ.v cb_val.al /\
          is_full_vec cb_val.buf /\
          SZ.v cb_val.al > 0 /\
          SZ.v cb_val.al <= pow2_63 /\
          SZ.v cb_val.rs == st.read_start /\
          SZ.v cb_val.al == st.alloc_length /\
          SZ.v trimmed_len + SZ.v skip == SZ.v write_len /\
          SZ.v write_len == Seq.length src_data /\
          SZ.v write_len == A.length src /\
          SZ.v rel_offset + SZ.v trimmed_len <= SZ.v cb_val.al /\
          st.read_start < st.alloc_length /\
          Spec.phys_log_coherent st.alloc_length cur_phys
            (GT.write_range_contents st.contents (SZ.v rel_offset)
              (Seq.slice (reveal src_data) (SZ.v skip) (SZ.v skip + SZ.v vi)))
            st.read_start)
      {
        let vi = R.read wi;
        with cur_phys. assert (Vec.pts_to cb_val.buf cur_phys);
        A.pts_to_len src;
        let src_idx = SZ.add skip vi;
        let byte_val = A.op_Array_Access src src_idx;
        let off = SZ.add rel_offset vi;
        lemma_idx_sum_fits cb_val.al cb_val.rs off;
        let pidx = SZ.rem (SZ.add cb_val.rs off) cb_val.al;
        lemma_mod_spec_eq (SZ.v (SZ.add cb_val.rs off)) (SZ.v cb_val.al);
        cb_val.buf.(pidx) <- byte_val;
        Spec.write_step_coherence (SZ.v cb_val.al) cur_phys st.contents
          st.read_start (SZ.v rel_offset) (Seq.slice (reveal src_data) (SZ.v skip) (SZ.v write_len)) (SZ.v vi);
        lemma_inc_fits vi trimmed_len;
        R.write wi (SZ.add vi 1sz);
      };

      with _vi _cur_phys. _;
      let trimmed_data = Ghost.hide (Seq.slice (reveal src_data) (SZ.v skip) (SZ.v write_len));
      Seq.lemma_eq_intro
        (Seq.slice (reveal src_data) (SZ.v skip) (SZ.v skip + SZ.v trimmed_len))
        (reveal trimmed_data);
      Seq.lemma_eq_intro
        (Seq.slice (reveal trimmed_data) 0 (SZ.v trimmed_len))
        (reveal trimmed_data);

      Spec.write_ooo_coherence_transfer (SZ.v cb_val.al) _cur_phys st.contents
        st.read_start (SZ.v rel_offset) (reveal trimmed_data) (SZ.v _vi) (SZ.v trimmed_len);
      GT.write_range_contents_t_eq st.contents (SZ.v rel_offset) (reveal trimmed_data);
      GT.write_range_monotone st.contents (SZ.v rel_offset) (reveal trimmed_data);
      Spec.write_range_preserves_wf st (SZ.v rel_offset) (reveal trimmed_data);

      let rm_abs = SZ.add cb_val.bo rel_offset;
      RM.range_vec_add rm rm_abs trimmed_len;
      RMSpec.add_range_wf repr (SZ.v rm_abs) (SZ.v trimmed_len);
      Spec.ranges_match_write repr st.contents (SZ.v cb_val.bo) (SZ.v rel_offset) (reveal trimmed_data);

      let new_pl = RM.range_vec_contiguous_from rm cb_val.bo;
      let ndr = SZ.gt new_pl 0sz && SZ.eq old_pl 0sz;

      let new_cbi = Mkcb_internal cb_val.buf cb_val.rs cb_val.al new_pl cb_val.vl cb_val.bo;
      ( := ) cb new_cbi;
      rewrite (Vec.pts_to cb_val.buf _cur_phys) as (Vec.pts_to new_cbi.buf _cur_phys);

      Spec.write_preserves_rwp repr (SZ.v cb_val.bo) (SZ.v rel_offset) (SZ.v trimmed_len);
      Spec.write_preserves_cf_eq_cpl repr st.contents (SZ.v cb_val.bo) (SZ.v rel_offset) (reveal trimmed_data);

      // Bounded: add_range preserves boundedness
      RMSpec.add_range_bounded repr (SZ.v rm_abs) (SZ.v trimmed_len) (SZ.v cb_val.bo + SZ.v cb_val.al);

      // Count bound: first.low >= bo preserved, then derive count < max
      RMSpec.add_range_first_low repr (SZ.v rm_abs) (SZ.v trimmed_len) (SZ.v cb_val.bo);
      Spec.repr_count_bound_gap (RMSpec.add_range repr (SZ.v rm_abs) (SZ.v trimmed_len))
        (SZ.v cb_val.bo) (SZ.v cb_val.al);

      fold (is_circular_buffer cb rm
        { st with contents =
            GT.write_range_contents_t st.contents (SZ.v rel_offset) (reveal trimmed_data) });
      { wrote = true; new_data_ready = ndr; resize_failed = false }
    }
  }
}
#pop-options

/// Drain: advance read_start and base_offset, slice contents.
/// The range map is UNCHANGED — this is the key advantage of absolute offsets.
#push-options "--z3rlimit_factor 8 --fuel 2 --ifuel 1"
fn drain
  (cb: circular_buffer) (rm: RM.range_vec_t) (n: SZ.t)
  (#st: erased Spec.cb_state)
  requires is_circular_buffer cb rm st **
    pure (Spec.cb_wf st /\ SZ.v n <= st.alloc_length /\
          SZ.v n <= GT.contiguous_prefix_length st.contents /\
          SZ.fits (st.base_offset + SZ.v n))
  returns no_more_data: bool
  ensures is_circular_buffer cb rm (Spec.drain_result st (SZ.v n)) **
    pure (no_more_data == (GT.contiguous_prefix_length st.contents = SZ.v n))
{
  unfold (is_circular_buffer cb rm st);
  with cbi buf_data repr. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);

  // Advance read_start and base_offset
  lemma_idx_sum_fits cb_val.al cb_val.rs n;
  let temp = SZ.add cb_val.rs n;
  let new_rs = SZ.rem temp cb_val.al;
  let new_bo = SZ.add cb_val.bo n;

  if (SZ.gt n 0sz) {
    // n > 0: drain range vec + fold with drain_repr
    RM.range_vec_drain rm new_bo;

    let new_pl = RM.range_vec_contiguous_from rm new_bo;
    let new_cbi = Mkcb_internal cb_val.buf new_rs cb_val.al new_pl cb_val.vl new_bo;
    ( := ) cb new_cbi;
    rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to new_cbi.buf buf_data);

    Spec.drain_preserves_coherence st.alloc_length buf_data st.contents st.read_start (SZ.v n);
    Spec.ranges_match_drain_repr repr st.contents (SZ.v cb_val.bo) (SZ.v n);
    RMSpec.drain_repr_wf repr (SZ.v new_bo);
    Spec.drain_repr_preserves_rwp repr (SZ.v cb_val.bo) (SZ.v n);
    Spec.rwp_cf_eq_cpl (RMSpec.drain_repr repr (SZ.v new_bo))
      (Spec.drained_contents st.alloc_length st.contents (SZ.v n))
      (SZ.v new_bo);
    Spec.drain_prefix_length st.alloc_length st.contents (SZ.v n);
    RMSpec.drain_repr_length repr (SZ.v new_bo);

    fold (is_circular_buffer cb rm (Spec.drain_result st (SZ.v n)));
    SZ.eq new_pl 0sz
  } else {
    // n = 0: no drain, fold with original repr
    let new_pl = RM.range_vec_contiguous_from rm new_bo;
    let new_cbi = Mkcb_internal cb_val.buf new_rs cb_val.al new_pl cb_val.vl new_bo;
    ( := ) cb new_cbi;
    rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to new_cbi.buf buf_data);

    Spec.drain_preserves_coherence st.alloc_length buf_data st.contents st.read_start (SZ.v n);
    Spec.ranges_match_drain_padded repr st.contents (SZ.v cb_val.bo) (SZ.v n);
    Spec.drain_preserves_rwp repr (SZ.v cb_val.bo) (SZ.v n);
    Spec.rwp_cf_eq_cpl repr
      (Spec.drained_contents st.alloc_length st.contents (SZ.v n))
      (SZ.v new_bo);
    Spec.drain_prefix_length st.alloc_length st.contents (SZ.v n);

    fold (is_circular_buffer cb rm (Spec.drain_result st (SZ.v n)));
    SZ.eq new_pl 0sz
  }
}
#pop-options

/// --- Zero-copy Read ---

/// Core: split the buffer array into read segments, return trade back to raw resources.
/// Shared by all mode wrappers (non-RM, RM, OOO, ...).
#push-options "--z3rlimit_factor 32 --fuel 1 --ifuel 1"
fn read_zerocopy_core
  (cb: circular_buffer)
  (read_len: SZ.t)
  (cbi: cb_internal)
  (#buf_data: erased (Seq.seq byte))
  requires
    B.pts_to cb cbi ** Vec.pts_to cbi.buf buf_data **
    pure (SZ.v cbi.al > 0 /\ SZ.v cbi.rs < SZ.v cbi.al /\
          SZ.v read_len <= SZ.v cbi.al /\ SZ.v read_len > 0 /\
          SZ.v cbi.al <= pow2_63 /\ is_full_vec cbi.buf /\
          Seq.length buf_data == SZ.v cbi.al /\
          SZ.fits (SZ.v cbi.rs + SZ.v read_len))
  returns rv: read_view
  ensures exists* (s1 s2: Seq.seq byte).
    zc_segs rv s1 s2 **
    (zc_segs rv s1 s2 @==> (B.pts_to cb cbi ** Vec.pts_to cbi.buf buf_data)) **
    pure (
      SZ.v rv.len1 + SZ.v rv.len2 == SZ.v read_len /\
      SZ.v rv.off1 + SZ.v rv.len1 <= SZ.v cbi.al /\
      SZ.v rv.off2 + SZ.v rv.len2 <= SZ.v cbi.al)
{
  // Convert Vec -> Array -> pts_to_range
  to_array_pts_to cbi.buf;
  A.pts_to_len (vec_to_array cbi.buf);
  PTR.pts_to_range_intro (vec_to_array cbi.buf) 1.0R buf_data;

  // Compute segment boundaries
  let rs = cbi.rs;
  let al = cbi.al;
  let wraps = SZ.gt (SZ.add rs read_len) al;

  if wraps {
    // Wrap case: seg1 = [rs, al), seg2 = [0, read_len - (al - rs))
    let len1 = SZ.sub al rs;
    let len2 = SZ.sub read_len len1;

    // Split: [0, rs) + [rs, al)
    PTR.pts_to_range_split (vec_to_array cbi.buf) 0 (SZ.v rs) (A.length (vec_to_array cbi.buf));
    with s_pre s_post. _;

    // Split [0, rs) into [0, len2) + [len2, rs)
    PTR.pts_to_range_split (vec_to_array cbi.buf) 0 (SZ.v len2) (SZ.v rs);
    with s2 s_mid. _;

    let rv = Mkread_view (vec_to_array cbi.buf) rs len1 0sz len2;

    // Package trade: segments → raw resources
    intro (trade (zc_segs rv s_post s2)
                 (B.pts_to cb cbi ** Vec.pts_to cbi.buf buf_data))
      #(A.pts_to_range (vec_to_array cbi.buf) (SZ.v len2) (SZ.v rs) s_mid **
        B.pts_to cb cbi) fn _
    {
      // Rewrite hyp from rv.* to concrete values
      unfold zc_segs;
      rewrite
        (A.pts_to_range rv.arr (SZ.v rv.off1) (SZ.v rv.off1 + SZ.v rv.len1) s_post)
      as (A.pts_to_range (vec_to_array cbi.buf) (SZ.v rs) (SZ.v rs + SZ.v len1) s_post);
      rewrite
        (A.pts_to_range rv.arr (SZ.v rv.off2) (SZ.v rv.off2 + SZ.v rv.len2) s2)
      as (A.pts_to_range (vec_to_array cbi.buf) 0 (SZ.v len2) s2);
      // Rejoin [0, len2) + [len2, rs)
      PTR.pts_to_range_join (vec_to_array cbi.buf) 0 (SZ.v len2) (SZ.v rs);
      // Rejoin [0, rs) + [rs, al)
      PTR.pts_to_range_join (vec_to_array cbi.buf) 0 (SZ.v rs) (A.length (vec_to_array cbi.buf));
      // pts_to_range -> pts_to -> Vec
      PTR.pts_to_range_elim (vec_to_array cbi.buf) 1.0R (Seq.append (Seq.append s2 s_mid) s_post);
      to_vec_pts_to cbi.buf;
      with s'. assert (Vec.pts_to cbi.buf s');
      assert (pure (s' `Seq.equal` buf_data));
      rewrite (Vec.pts_to cbi.buf s') as (Vec.pts_to cbi.buf buf_data);
    };
    // Rewrite from concrete array to rv.arr for postcondition
    rewrite
      (A.pts_to_range (vec_to_array cbi.buf) (SZ.v rs) (A.length (vec_to_array cbi.buf)) s_post)
    as (A.pts_to_range rv.arr (SZ.v rv.off1) (SZ.v rv.off1 + SZ.v rv.len1) s_post);
    rewrite
      (A.pts_to_range (vec_to_array cbi.buf) 0 (SZ.v len2) s2)
    as (A.pts_to_range rv.arr (SZ.v rv.off2) (SZ.v rv.off2 + SZ.v rv.len2) s2);
    fold (zc_segs rv s_post s2);
    rv
  } else {
    // No-wrap case: seg1 = [rs, rs+read_len), seg2 = empty
    // Split: [0, rs) + [rs, al)
    PTR.pts_to_range_split (vec_to_array cbi.buf) 0 (SZ.v rs) (A.length (vec_to_array cbi.buf));
    with s_pre s_post. _;

    // Split [rs, al) into [rs, rs+read_len) + [rs+read_len, al)
    PTR.pts_to_range_split (vec_to_array cbi.buf) (SZ.v rs) (SZ.v rs + SZ.v read_len) (A.length (vec_to_array cbi.buf));
    with s1 s_tail. _;

    let rv = Mkread_view (vec_to_array cbi.buf) rs read_len 0sz 0sz;

    // Create empty pts_to_range for segment 2
    PTR.pts_to_range_split (vec_to_array cbi.buf) 0 0 (SZ.v rs);
    with s_empty s_pre'. _;

    // Package trade: segments → raw resources
    intro (trade (zc_segs rv s1 s_empty)
                 (B.pts_to cb cbi ** Vec.pts_to cbi.buf buf_data))
      #(A.pts_to_range (vec_to_array cbi.buf) 0 (SZ.v rs) s_pre' **
        A.pts_to_range (vec_to_array cbi.buf) (SZ.v rs + SZ.v read_len) (A.length (vec_to_array cbi.buf)) s_tail **
        B.pts_to cb cbi) fn _
    {
      unfold zc_segs;
      rewrite
        (A.pts_to_range rv.arr (SZ.v rv.off1) (SZ.v rv.off1 + SZ.v rv.len1) s1)
      as (A.pts_to_range (vec_to_array cbi.buf) (SZ.v rs) (SZ.v rs + SZ.v read_len) s1);
      rewrite
        (A.pts_to_range rv.arr (SZ.v rv.off2) (SZ.v rv.off2 + SZ.v rv.len2) s_empty)
      as (A.pts_to_range (vec_to_array cbi.buf) 0 0 s_empty);
      // Rejoin [0,0) + [0,rs)
      PTR.pts_to_range_join (vec_to_array cbi.buf) 0 0 (SZ.v rs);
      // Rejoin [rs, rs+rl) + [rs+rl, al)
      PTR.pts_to_range_join (vec_to_array cbi.buf) (SZ.v rs) (SZ.v rs + SZ.v read_len) (A.length (vec_to_array cbi.buf));
      // Rejoin [0, rs) + [rs, al)
      PTR.pts_to_range_join (vec_to_array cbi.buf) 0 (SZ.v rs) (A.length (vec_to_array cbi.buf));
      // pts_to_range -> pts_to -> Vec
      PTR.pts_to_range_elim (vec_to_array cbi.buf) 1.0R
        (Seq.append (Seq.append s_empty s_pre') (Seq.append s1 s_tail));
      to_vec_pts_to cbi.buf;
      with s'. assert (Vec.pts_to cbi.buf s');
      assert (pure (s' `Seq.equal` buf_data));
      rewrite (Vec.pts_to cbi.buf s') as (Vec.pts_to cbi.buf buf_data);
    };
    // Rewrite from concrete array to rv.arr for postcondition
    rewrite
      (A.pts_to_range (vec_to_array cbi.buf) (SZ.v rs) (SZ.v rs + SZ.v read_len) s1)
    as (A.pts_to_range rv.arr (SZ.v rv.off1) (SZ.v rv.off1 + SZ.v rv.len1) s1);
    rewrite
      (A.pts_to_range (vec_to_array cbi.buf) 0 0 s_empty)
    as (A.pts_to_range rv.arr (SZ.v rv.off2) (SZ.v rv.off2 + SZ.v rv.len2) s_empty);
    fold (zc_segs rv s1 s_empty);
    rv
  }
}
#pop-options

/// Zero-copy read: unfold is_circular_buffer, call core, compose trade
fn read_zerocopy
  (cb: circular_buffer)
  (rm: RM.range_vec_t)
  (read_len: SZ.t)
  (#st: erased Spec.cb_state)
  requires
    is_circular_buffer cb rm st **
    pure (Spec.cb_wf st /\
          SZ.v read_len <= GT.contiguous_prefix_length st.contents /\
          SZ.v read_len <= st.alloc_length /\
          SZ.v read_len > 0)
  returns rv: read_view
  ensures exists* (s1 s2: Seq.seq byte).
    zc_segs rv s1 s2 **
    (zc_segs rv s1 s2 @==> is_circular_buffer cb rm st) **
    pure (
      SZ.v rv.len1 + SZ.v rv.len2 == SZ.v read_len /\
      SZ.v rv.off1 + SZ.v rv.len1 <= st.alloc_length /\
      SZ.v rv.off2 + SZ.v rv.len2 <= st.alloc_length)
{
  unfold (is_circular_buffer cb rm st);
  with cbi buf_data repr. _;
  let cb_val = !cb;
  rewrite (Vec.pts_to cbi.buf buf_data) as (Vec.pts_to cb_val.buf buf_data);
  rewrite (B.pts_to cb cbi) as (B.pts_to cb cb_val);
  Spec.ranges_match_prefix_lower repr st.contents (SZ.v cbi.bo);
  lemma_idx_sum_fits cb_val.al cb_val.rs read_len;

  let rv = read_zerocopy_core cb read_len cb_val;
  with s1 s2. _;

  // Fold trade: raw resources → is_circular_buffer (captures RM as extra)
  intro (trade (B.pts_to cb cb_val ** Vec.pts_to cb_val.buf buf_data)
               (is_circular_buffer cb rm st))
    #(RM.is_range_vec rm repr) fn _ {
    rewrite (B.pts_to cb cb_val) as (B.pts_to cb cbi);
    rewrite (Vec.pts_to cb_val.buf buf_data) as (Vec.pts_to cbi.buf buf_data);
    fold (is_circular_buffer cb rm st);
  };

  // Compose: (segs @==> raw) ** (raw @==> is_circular_buffer) → (segs @==> is_circular_buffer)
  trade_compose
    (zc_segs rv s1 s2)
    (B.pts_to cb cb_val ** Vec.pts_to cb_val.buf buf_data)
    (is_circular_buffer cb rm st);

  rv
}

/// Release zero-copy read without draining (cancel)
fn release_read
  (cb: circular_buffer)
  (rm: RM.range_vec_t)
  (rv: read_view)
  (#st: erased Spec.cb_state)
  (#s1 #s2: erased (Seq.seq byte))
  requires
    zc_segs rv s1 s2 **
    (zc_segs rv s1 s2 @==> is_circular_buffer cb rm st)
  ensures
    is_circular_buffer cb rm st
{
  elim_trade (zc_segs rv s1 s2) (is_circular_buffer cb rm st);
}

/// Release zero-copy read AND drain
#push-options "--z3rlimit_factor 8 --fuel 1 --ifuel 1"
fn drain_after_read
  (cb: circular_buffer)
  (rm: RM.range_vec_t)
  (rv: read_view)
  (drain_len: SZ.t)
  (#st: erased Spec.cb_state)
  (#s1 #s2: erased (Seq.seq byte))
  requires
    zc_segs rv s1 s2 **
    (zc_segs rv s1 s2 @==> is_circular_buffer cb rm st) **
    pure (Spec.cb_wf st /\
          SZ.v drain_len <= st.alloc_length /\
          SZ.v drain_len <= GT.contiguous_prefix_length st.contents /\
          SZ.fits (st.base_offset + SZ.v drain_len))
  returns no_more_data: bool
  ensures
    is_circular_buffer cb rm (Spec.drain_result st (SZ.v drain_len)) **
    pure (no_more_data == (GT.contiguous_prefix_length st.contents = SZ.v drain_len))
{
  release_read cb rm rv;
  drain cb rm drain_len
}
#pop-options
