(*
   Copyright 2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Steel.Actions
open FStar.Real
open Steel.Permissions
open Steel.Memory
module U32 = FStar.UInt32
open FStar.FunctionalExtensionality

friend Steel.Memory

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

let m_action_depends_only_on #pre #a #post (f:pre_m_action pre a post)
  = forall (m0:hmem pre)
      (h1:heap {m_disjoint m0 h1})
      (post: (x:a -> fp_prop (post x))).
      (let m1 = upd_joined_heap m0 h1 in
       let (| x0, m |) = f m0 in
       let (| x1, m' |) = f m1 in
       x0 == x1 /\
       (post x0 (heap_of_mem m) <==> post x1 (heap_of_mem m')))

#push-options "--initial_fuel 2 --max_fuel 2"
let is_m_frame_preserving #a #fp #fp' (f:pre_m_action fp a fp') =
  forall frame (m0:hmem (fp `star` frame)).
    (affine_star fp frame (heap_of_mem m0);
     let (| x, m1 |) = f m0 in
     interp (fp' x `star` frame `star` locks_invariant m1) (heap_of_mem m1))
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --z3rlimit 30"
let frame_fp_prop' #fp #a #fp' frame
                   (q:fp_prop frame)
                   (act:action fp a fp')
                   (h0:hheap (fp `star` frame))
   : Lemma (requires q h0)
           (ensures (
             let (| x, h1 |) = act h0 in
             q h1))
   = assert (interp (Refine (fp `star` frame) q) h0);
     assert (interp (fp `star` (Refine frame q)) h0);
     let (| x, h1 |) = act h0 in
     assert (interp (fp' x `star` (Refine frame q)) h1);
     refine_star_r (fp' x) frame q;
     assert (interp (Refine (fp' x `star` frame) q) h1);
     assert (q h1)
#pop-options

let frame_fp_prop #fp #a #fp' (act:action fp a fp')
                  (#frame:hprop) (q:fp_prop frame)
   = let aux (h0:hheap (fp `star` frame))
       : Lemma
         (requires q h0)
         (ensures
           (let (|x, h1|) = act h0 in
            q h1))
         [SMTPat (act h0)]
       = frame_fp_prop' frame q act h0
     in
     ()

#push-options "--warn_error -271"
let action_depends_only_on_fp_intro (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_action fp a fp')
  (lemma:
    (h0:hheap fp) ->
    (h1:heap{disjoint h0 h1}) ->
    (post: (x:a -> fp_prop (fp' x))) ->
    Lemma (
      let (|x0, h0'|) = f h0 in
      let (|x1, h'|) = f (join h0 h1) in
      x0 == x1 /\
      (post x0 h0' <==> post x1 h')
    )
  )
  : Lemma (action_depends_only_on_fp f)
  =
  let aux (h0:hheap fp) (h1:heap {disjoint h0 h1}) (post: (x:a -> fp_prop (fp' x)))
    : Lemma (
      let (| x0, h |) = f h0 in
      let (| x1, h' |) = f (join h0 h1) in
      x0 == x1 /\
      (post x0 h <==> post x1 h')
    )
   =
     lemma h0 h1 post
   in
   Classical.forall_intro_3 aux;
   admit() //TODO: DM 22/01/20 figure out why F* can't recognize the intro...
#pop-options

#push-options "--z3rlimit 50 --max_ifuel 3 --initial_ifuel 3 --max_fuel 3 --initial_fuel 3"
let action_depends_only_on_fp_elim
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_action fp a fp')
  (h0: hheap fp) (h1:heap{disjoint h0 h1}) (post: (x:a -> fp_prop (fp' x)))
  : Lemma (requires (action_depends_only_on_fp f)) (ensures (
    interp fp (join h0 h1) /\ (
     let (| x0, h |) = f h0 in
     let (| x1, h' |) = f (join h0 h1) in
     x0 == x1 /\
     (post x0 h <==> post x1 h'))
  ))
=
  admit() //TODO DM 24/01/20 figure out why F* can't recognize it
#pop-options

#push-options "--max_fuel 2 --initial_ifuel 2"
let is_frame_preserving_intro
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_action fp a fp')
  (preserves_frame_prop_intro:
    (frame: hprop) -> (h0: heap) ->
    (q: (heap -> prop){q `depends_only_on_without_affinity` frame}) ->
    Lemma (requires (interp (fp `star` frame) h0)) (ensures (
      let (| x, h1 |) = f h0 in q h0 <==> q h1
    ))
  )
  (preserves_framing_intro:
    (frame: hprop) -> (h0: heap) ->
    Lemma (requires (interp (fp `star` frame) h0)) (ensures (
      let (| x, h1 |) = f h0 in  interp (fp' x `star` frame) h1
    ))
  )
  : Lemma (is_frame_preserving f)
  =
  let aux (frame: hprop) (h0: heap) : Lemma (interp (fp `star` frame) h0 ==>
     (let (| x, h1 |) = f h0 in
     interp (fp' x `star` frame) h1 /\
     preserves_frame_prop frame h0 h1)
  ) =
    let aux (pf: (interp (fp `star` frame) h0)) : Lemma (
      interp (fp `star` frame) h0 /\ (
      let h0 : (h0:heap{interp fp h0}) = affine_star fp frame h0; h0 in
      let (| x, h1 |) = f h0 in
      interp (fp' x `star` frame) h1 /\
      preserves_frame_prop frame h0 h1)
    ) =
      affine_star fp frame h0;
      let (| x, h1 |) = f h0 in
      let aux (q: (heap -> prop){q `depends_only_on_without_affinity` frame})
        : Lemma (q h0 <==> q h1) =
        preserves_frame_prop_intro frame h0 q
      in
      Classical.forall_intro aux;
      assert(preserves_frame_prop frame h0 h1);
      preserves_framing_intro frame h0
    in
    Classical.impl_intro aux
  in
  Classical.forall_intro_2 aux
#pop-options

let is_frame_preserving_elim
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_action fp a fp')
  (frame: hprop) (h0: heap)
  : Lemma (requires (is_frame_preserving f /\ interp (fp `star` frame) h0)) (ensures (
     let (| x, h1 |) = f h0 in
     interp (fp' x `star` frame) h1 /\
     preserves_frame_prop frame h0 h1
  ))
  = ()

#push-options "--z3rlimit 100 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let pre_action_to_action
  (fp:hprop) (a: Type) (fp': a -> hprop) (f: pre_action fp a fp')
  (action_preserves_frame_disjointness_addr:
    (frame: hprop) ->
    (h0:hheap fp) ->
    (h1:hheap frame{disjoint h0 h1}) ->
    (addr: addr) ->
    Lemma (
      let (|_, h0'|) = f h0 in
      disjoint_addr h0' h1 addr
    )
  )
  (action_does_not_depend_on_framing_addr:
    (frame: hprop) ->
    (h0:hheap fp) ->
    (h1:hheap frame{disjoint h0 h1}) ->
    (addr: addr) ->
    Lemma (requires (
      let (|_, h0'|) = f h0 in
      disjoint h0' h1
    ))
    (ensures (
      let (|_, h0'|) = f h0 in
      let (|_, h'|) = f (join h0 h1) in
      h' addr == join h0' h1 addr
    ))
  )
  (action_return_and_post_does_not_depend_on_framing:
    (frame: hprop) ->
    (h0:hheap fp) ->
    (h1:hheap frame{disjoint h0 h1}) ->
    (post: (x:a -> fp_prop (fp' x))) ->
    Lemma (
      let (|x_alone, h0'|) = f h0 in
      let (|x_joint, h'|) = f (join h0 h1) in
      x_alone == x_joint /\
      (post x_alone h0' <==> post x_joint h')
    )
  )
  : Tot (action fp a fp')
  =
  let aux (frame: hprop) (h: hheap (fp `star` frame))
    : Lemma (
      let (|x, h' |) = f h in
      preserves_frame_prop frame h h' /\
      interp (fp' x `star` frame) h'
    )
    =
    let (| x, h' |) = f h in
    let pf :squash (exists (h0:heap). (exists (h1:heap).
      disjoint h0 h1 /\ h == join h0 h1 /\ interp fp h0 /\ interp frame h1
    )) =
      assert(interp (fp `star` frame) h)
    in
    Classical.exists_elim
      (preserves_frame_prop frame h h' /\ interp (fp' x `star` frame) h') pf
      (fun h0 ->
        let pf: squash (exists (h1: hheap frame).
          disjoint h0 h1 /\ h == join h0 h1 /\ interp fp h0 /\ interp frame h1
        ) =
          ()
        in
        Classical.exists_elim
          (preserves_frame_prop frame h h' /\ interp (fp' x `star` frame) h') pf
          (fun h1 ->
            let h0 : hheap fp = h0 in
            let h1 : (h1:hheap frame{disjoint h0 h1 /\ h == join h0 h1}) = h1 in
            let (|x_alone, h0'|) = f h0 in
            let (|x_joint, h'|) = f (join h0 h1) in
            let aux (addr: addr) : Lemma (disjoint_addr h0' h1 addr) =
              action_preserves_frame_disjointness_addr frame h0 h1 addr
            in
            Classical.forall_intro aux;
            let aux (addr: addr) : Lemma (h' addr == join h0' h1 addr) =
              action_does_not_depend_on_framing_addr frame h0 h1 addr
            in
            Classical.forall_intro aux;
            mem_equiv_eq h' (join h0' h1);
            let aux (q:(heap -> prop){q `depends_only_on_without_affinity` frame})
              : Lemma (q h <==> q h')
            = ()
            in
            Classical.forall_intro aux;
            action_return_and_post_does_not_depend_on_framing frame h0 h1 (fun _ _ -> True);
            assert(x_alone == x);
            assert(x_joint == x);
            assert(interp (fp' x_alone) h0');
            assert(interp frame h1);
            assert(h' == join h0' h1);
            assert(disjoint h0' h1);
            intro_star (fp' x) (frame) h0' h1;
            assert(interp (fp' x `star` frame) h')
        )
    )
  in
  Classical.forall_intro_2 aux;
  let aux (h0:hheap fp) (h1:heap {disjoint h0 h1}) (post: (x:a -> fp_prop (fp' x)))
    : Lemma (
       let (| x0, h0' |) = f h0 in
       let (| x1, h' |) = f (join h0 h1) in
       interp fp (join h0 h1) /\
       x0 == x1 /\
       (post x0 h0' <==> post x1 h')
    )
    =
      let (| x0, h0' |) = f h0 in
      let (| x1, h' |) = f (join h0 h1) in
      action_return_and_post_does_not_depend_on_framing emp h0 h1 post
  in
  action_depends_only_on_fp_intro f aux;
  f
#pop-options


#push-options "--warn_error -271 --max_fuel 1 --initial_fuel 1"
let non_alloc_action_to_non_locking_pre_m_action
  (fp:hprop) (a: Type) (fp': a -> hprop) (f: action fp a fp')
  (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
    (requires (h addr == None))
    (ensures (let (| _, h'|) = f h in h' addr == None))
  )
  : Tot (pre_m_action fp a fp')
  =
  fun m ->
    let (|x, h'|) = f m.heap in
    let aux (i: addr) : Lemma (requires (i >= m.ctr)) (ensures (h' i == None)) =
      non_alloc m.heap i
    in
    Classical.forall_intro (Classical.move_requires aux);
    let does_not_perturb_locks (lock_p: hprop) (h:hheap (fp `star` lock_p))
      : Lemma (let (|_, h'|) = f h in interp lock_p h') [SMTPat ()]
    =
      assert(is_frame_preserving f);
      assert(interp (fp `star` lock_p) h);
      let (| x, h' |) = f h in
      assert(interp (fp' x `star` lock_p) h');
      affine_star (fp' x) lock_p h';
      assert(interp lock_p h')
    in
    assert(interp (lock_store_invariant m.locks) h');
    let m':mem = {m with heap = h'} in
    (| x, m' |)
#pop-options


#push-options "--warn_error -271 --max_fuel 1 --initial_fuel 1"
let alloc_action_to_non_locking_pre_m_action
  (fp:hprop) (a: Type) (fp': a -> hprop) (f: action fp a fp')
  (alloc_lemma: (h: hheap fp) -> (alloc_addr: addr) -> Lemma
    (forall (a: addr). let (| _, h'|) = f h in
      h a == None ==> (if a = alloc_addr then h' a =!= None else h' a == None)
    )
  )
  : Tot (pre_m_action fp a fp')
  =
  fun m ->
    let (|x, h'|) = f m.heap in
    let aux (i: addr) : Lemma (requires (i >= m.ctr + 1)) (ensures (h' i == None)) =
      alloc_lemma m.heap m.ctr
    in
    Classical.forall_intro (Classical.move_requires aux);
    let does_not_perturb_locks (lock_p: hprop) (h:hheap (fp `star` lock_p))
      : Lemma (let (|_, h'|) = f h in interp lock_p h') [SMTPat ()]
    =
      assert(is_frame_preserving f);
      assert(interp (fp `star` lock_p) h);
      let (| x, h' |) = f h in
      assert(interp (fp' x `star` lock_p) h');
      affine_star (fp' x) lock_p h';
      assert(interp lock_p h')
    in
    assert(interp (lock_store_invariant m.locks) h');
    let m':mem = {m with heap = h'; ctr = m.ctr + 1} in
    (| x, m' |)
#pop-options

#push-options "--warn_error -271"
let m_action_depends_only_on_intro (fp:hprop) (a:Type) (fp':a -> hprop) (f:pre_m_action fp a fp')
  (lemma:
    (m0:hmem fp) ->
    (h1:heap{m_disjoint m0 h1}) ->
    (post: (x:a -> fp_prop (fp' x))) ->
    Lemma (
      let m1 = upd_joined_heap m0 h1 in
      let (|x0, m|) = f m0 in
      let (|x1, m'|) = f m1 in
      x0 == x1 /\
      (post x0 (heap_of_mem m) <==> post x1 (heap_of_mem m'))
    )
  )
  : Lemma (m_action_depends_only_on f)
  =
  let aux (m0:hmem fp) (h1:heap {m_disjoint m0 h1}) (post: (x:a -> fp_prop (fp' x)))
    : Lemma (
     let m1 = upd_joined_heap m0 h1 in
      let (|x0, m|) = f m0 in
      let (|x1, m'|) = f m1 in
      x0 == x1 /\
      (post x0 (heap_of_mem m) <==> post x1 (heap_of_mem m'))
    )
   =
     lemma m0 h1 post
   in
   Classical.forall_intro_3 aux;
   admit() //TODO: DM 22/01/20 figure out why F* can't recognize the intro...
#pop-options


#push-options "--max_fuel 2 --initial_ifuel 2"
let is_m_frame_preserving_intro
  (#fp:hprop) (#a:Type) (#fp':a -> hprop) (f:pre_m_action fp a fp')
  (preserves_framing_intro:
    (frame: hprop) -> (m0: hmem (fp `star` frame)) ->
    Lemma (
      let (| x, m1 |) = f m0 in
      interp (fp' x `star` frame `star` locks_invariant m1) (heap_of_mem m1)
    )
  )
  : Lemma (is_m_frame_preserving f)
  =
  let aux (frame: hprop) (m0: hmem (fp `star` frame)) : Lemma (
     let (| x, m1 |) = f m0 in
     interp (fp' x `star` frame `star` locks_invariant m1) (heap_of_mem m1)
  ) =
    let (| x, h1 |) = f m0 in
    preserves_framing_intro frame m0
  in
  Classical.forall_intro_2 aux
#pop-options

#push-options "--z3rlimit 50 --max_ifuel 0 --initial_ifuel 0 --max_fuel 1 --initial_fuel 1"
let non_alloc_action_to_non_locking_m_action
  (fp:hprop) (a: Type) (fp': a -> hprop) (f: action fp a fp')
    (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
    (requires (h addr == None))
    (ensures (let (| _, h'|) = f h in h' addr == None))
  )
  : Tot (m_action fp a fp')
=
  let f_m = non_alloc_action_to_non_locking_pre_m_action fp a fp' f non_alloc in
  m_action_depends_only_on_intro fp a fp' f_m (fun m0 h1 post ->
    let m1 = upd_joined_heap m0 h1 in
    let (|x0, m|) = f_m m0 in
    let (|x1, m'|) = f_m m1 in
    assert(action_depends_only_on_fp f);
    action_depends_only_on_fp_elim f m0.heap h1 post;
    assert(x0 == x1);
    assert(post x0 (heap_of_mem m) <==> post x1 (heap_of_mem m'))
  );
  assert(m_action_depends_only_on f_m);
  is_m_frame_preserving_intro f_m (fun frame m0 ->
    star_associative fp frame (locks_invariant m0);
    let (| x, m1 |) = f_m m0 in
    star_associative (fp' x) frame (locks_invariant m1);
    is_frame_preserving_elim f frame m0.heap
  );
  assert(is_m_frame_preserving f_m);
  f_m
#pop-options

#push-options "--z3rlimit 50 --max_ifuel 0 --initial_ifuel 0 --max_fuel 1 --initial_fuel 1"
let alloc_action_to_non_locking_m_action
  (fp:hprop) (a: Type) (fp': a -> hprop) (f: action fp a fp')
  (non_alloc: (h: hheap fp) -> (addr: addr) -> Lemma
    (requires (h addr == None))
    (ensures (let (| _, h'|) = f h in h' addr == None))
  )
  : Tot (m_action fp a fp')
=
  let f_m = non_alloc_action_to_non_locking_pre_m_action fp a fp' f non_alloc in
  m_action_depends_only_on_intro fp a fp' f_m (fun m0 h1 post ->
    let m1 = upd_joined_heap m0 h1 in
    let (|x0, m|) = f_m m0 in
    let (|x1, m'|) = f_m m1 in
    assert(action_depends_only_on_fp f);
    action_depends_only_on_fp_elim f m0.heap h1 post;
    assert(x0 == x1);
    assert(post x0 (heap_of_mem m) <==> post x1 (heap_of_mem m'))
  );
  assert(m_action_depends_only_on f_m);
  is_m_frame_preserving_intro f_m (fun frame m0 ->
    star_associative fp frame (locks_invariant m0);
    let (| x, m1 |) = f_m m0 in
    star_associative (fp' x) frame (locks_invariant m1);
    is_frame_preserving_elim f frame m0.heap
  );
  assert(is_m_frame_preserving f_m);
  f_m
#pop-options

/////////////////////////////////////////////////////////////////////////////
// Arrays
/////////////////////////////////////////////////////////////////////////////

#push-options "--max_fuel 3"
let as_seq (#t:_) (a:array_ref t) (m:hheap (array a)) =
  let Array t' len' seq = select_addr m a.array_addr in
  let len = U32.v a.array_length in
  assert(U32.v a.array_offset + U32.v a.array_length <= len');
  Seq.init len (fun i -> let (x, _) =  select_index seq (U32.v a.array_offset + i) in x)
#pop-options

#push-options "--max_fuel 2"
let as_seq_lemma
  (#t:_)
  (a:array_ref t)
  (i:U32.t{U32.v i < U32.v (length a)})
  (p:permission{allows_read p})
  (m:hheap (array_perm a p))
  =
  ()
#pop-options

let read_array_addr
  (#t: _)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i: U32.t{U32.v i < U32.v (length a)})
  (p:permission{allows_read p})
  (m: hheap (pts_to_array a p iseq))
  : Tot (x:t{x == Seq.index iseq (U32.v i)})
  =
  match m a.array_addr with
  | Some (Array t' len seq) ->
    assert(contains_index seq (U32.v a.array_offset + U32.v i));
    match Seq.index seq (U32.v a.array_offset + U32.v i) with
    | None -> ()
    | Some (x, _) -> x
  | _ -> ()

let index_array_pre_action
  (#t: _)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i: U32.t{U32.v i < U32.v (length a)})
  (p:permission{allows_read p})
  : Tot (pre_action
    (pts_to_array a p iseq)
    (x:t{x == Seq.index iseq (U32.v i)})
    (fun _ -> pts_to_array a p iseq))
  = fun h ->
  let x = read_array_addr a iseq i p h in
  (| x, h |)

let index_array_action
  (#t: _)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i: U32.t{U32.v i < U32.v (length a)})
  (p:permission{allows_read p})
  : Tot (pre_action
    (pts_to_array a p iseq)
    (x:t{x == Seq.index iseq (U32.v i)})
    (fun _ -> pts_to_array a p iseq))
  =
  pre_action_to_action
    (pts_to_array a p iseq)
    (x:t{x == Seq.index iseq (U32.v i)})
    (fun _ -> pts_to_array a p iseq)
    (index_array_pre_action a iseq i p)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 post -> ())

let index_array
  (#t:_)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  (i:U32.t{U32.v i < U32.v (length a)}) =
  non_alloc_action_to_non_locking_m_action
    (pts_to_array a p iseq)
    (x:t{x == Seq.index iseq (U32.v i)})
    (fun _ -> pts_to_array a p iseq)
    (index_array_action a iseq i p)
    (fun h addr -> ())

let update_array_addr
  (#t:_)
  (a: array_ref t)
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (perm:permission{allows_read perm})
  (m: heap{match m a.array_addr with
    | Some (Array t' len seq) ->
      t' == t /\ U32.v (offset a) + U32.v (length a) <= len
    | _ -> False
  })
  =
  match m a.array_addr with
  | Some (Array t' len seq) ->
    on _ (fun a' ->
      if a.array_addr = a' then
        let new_seq = Seq.upd seq (U32.v i + U32.v a.array_offset) (Some (v, perm)) in
        Some (Array t len new_seq)
      else
        m a'
    )
   | _ -> m

#push-options "--max_fuel 2 --initial_fuel 2"
let upd_array_heap
  (#t:_)
  (a:array_ref t)
  (iseq:  Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (h: hheap (pts_to_array a full_permission iseq)) : heap =
  let Array _ len v_orig = select_addr h a.array_addr in
  update_array_addr a i v full_permission h
#pop-options

#push-options "--z3rlimit 15 --max_fuel 2 --initial_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let upd_array_heap_frame_disjointness_preservation
  (#t:_)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (h h0 h1:heap)
  (frame:hprop)
  : Lemma
    (requires
      disjoint h0 h1 /\
      h == join h0 h1 /\
      interp (pts_to_array a full_permission iseq) h0 /\
      interp frame h1)
    (ensures (
      let h0' = upd_array_heap a iseq i v h0 in
      disjoint h0' h1))
  =
  ()
#pop-options


let upd_array_pre_action
  (#t:_)
  (a:array_ref t)
  (iseq:  Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : pre_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))
  = fun h ->
    (| (), upd_array_heap a iseq i v h |)

#push-options "--z3rlimit 100 --max_fuel 1 --initial_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let upd_array_action_memory_split_independence
  (#t:_)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  (h h0 h1:heap)
  (frame:hprop)
  : Lemma
    (requires
      disjoint h0 h1 /\
      h == join h0 h1 /\
      interp (pts_to_array a full_permission iseq) h0 /\
      interp frame h1)
    (ensures (
      let (| _, h' |) = upd_array_pre_action a iseq i v h in
      let h0' = upd_array_heap a iseq i v h0 in
      upd_array_heap_frame_disjointness_preservation a iseq i v h h0 h1 frame;
      h' == (join h0' h1)))
  =
  let (| _, h' |) = upd_array_pre_action a iseq i v h in
  let h0' = upd_array_heap a iseq i v h0 in
  let aux (addr: addr) : Lemma (
    upd_array_heap_frame_disjointness_preservation a iseq i v h h0 h1 frame;
    h' addr == (join h0' h1) addr
  ) =
    upd_array_heap_frame_disjointness_preservation a iseq i v h h0 h1 frame;
    if addr <> a.array_addr then () else
    if not (h1 `contains_addr` addr) then ()
    else match  h' addr, (join h0' h1) addr with
    | Some (Array t2 len2 seq2), Some (Array t3 len3 seq3) ->
      assert(seq2 `Seq.equal` seq3)
    | _ -> ()
  in
  Classical.forall_intro aux;
  mem_equiv_eq h' (join h0' h1)
#pop-options

let upd_array_action
  (#t:_)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : Tot (
    action
      (pts_to_array a full_permission iseq)
      unit
      (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))
    )
  =
  pre_action_to_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))
    (upd_array_pre_action a iseq i v)
    (fun frame h0 h1 addr -> (* Disjointness preservation *)
      upd_array_heap_frame_disjointness_preservation a iseq i v (join h0 h1) h0 h1 frame
    )
    (fun frame h0 h1 addr -> (* Does not depend on framing *)
      upd_array_action_memory_split_independence a iseq i v (join h0 h1) h0 h1 frame
    )
    (fun frame h0 h1 post -> (* Return and post *)
      let (| x0, h |) = upd_array_pre_action a iseq i v h0 in
      let (| x1, h' |) = upd_array_pre_action a iseq i v (join h0 h1) in
      assert (x0 == x1);
      upd_array_heap_frame_disjointness_preservation a iseq i v (join h0 h1) h0 h1 frame;
      upd_array_action_memory_split_independence a iseq i v (join h0 h1) h0 h1 frame;
      assert (h' == join h h1)
    )

let upd_array
  (#t:_)
  (a:array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : m_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))
  =
  non_alloc_action_to_non_locking_m_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))
    (upd_array_action a iseq i v)
    (fun h addr -> ())

// MST = MST mem locks_preorder

// let (:=) #a r v
// : action_t (ptr r) (fun _ -> points_to r v) (fun _ -> True)
//   (fun h0 _ h1 -> True)
//   let m = MST.get () in
//   let m1 = upd r v m in
//   MST.put m1

let alloc_array
  (#t: _)
  (len:U32.t)
  (init: t)
  : m_action
    emp
    (a:array_ref t{length a = len /\ offset a = 0ul})
    (fun a -> pts_to_array a full_permission (Seq.Base.create (U32.v len) init))
  =
  admit()

let free_array_pre_action
  (#t: _)
  (a: array_ref t{freeable a})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  : pre_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> emp)
  = fun h -> (| (), h |)

let free_array_action
  (#t: _)
  (a: array_ref t{freeable a})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  =
  pre_action_to_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> emp)
    (free_array_pre_action a iseq)
    (fun frame h0 h1 addr -> ())
    (fun frame h0 h1 post -> ())
    (fun frame h0 h1 post -> ())

let free_array
  (#t: _)
  (a: array_ref t{freeable a})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  : m_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> emp)
  =
  non_alloc_action_to_non_locking_m_action
    (pts_to_array a full_permission iseq)
    unit
    (fun _ -> emp)
    (free_array_action a iseq)
    (fun h addr -> ())

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 30"
let share_array_pre_action
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  : pre_action
    (pts_to_array a p iseq)
    (a':array_ref t{
      length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
      address a = address a'
    })
    (fun a' -> star
      (pts_to_array a (half_permission p) iseq)
      (pts_to_array a' (half_permission p) (Ghost.hide (Ghost.reveal iseq)))
    )
    = fun h ->
      let split_h_1 : heap = on _ (fun addr ->
        if addr <> a.array_addr then h addr else
        match h a.array_addr with
        | Some (Array t len seq) ->
          let new_seq = Seq.init len (fun i ->
            match Seq.index seq i with
            | None -> None
            | Some (x, p) -> Some (x, (half_permission p <: (perm:permission{allows_read perm})))
          ) in
          assert(Seq.length new_seq = len);
          Some (Array t len new_seq)
        | _ -> h addr
      ) in
      let split_h_2 : heap = on _ (fun addr ->
        if addr <> a.array_addr then None else
        match h a.array_addr with
        | Some (Array t len seq) ->
          let new_seq = Seq.init len (fun i ->
            match Seq.index seq i with
            | None -> None
            | Some (x, p) -> Some (x, (half_permission p <: (perm:permission{allows_read perm})))
          ) in
          assert(Seq.length new_seq = len);
          Some (Array t len new_seq)
        | _ -> None
      ) in
      assert(interp (pts_to_array a (half_permission p) iseq) split_h_1);
      let aux (addr: addr) : Lemma (disjoint_addr split_h_1 split_h_2 addr) =
        if addr <> a.array_addr then () else match split_h_1 addr, split_h_2 addr with
        | Some (Array t1 len1 seq1), Some (Array t2 len2 seq2) ->
          assert(t1 == t2);
          assert(len1 == len2);
          let aux (i:nat{i < len1}) : Lemma (
            match contains_index seq1 i, contains_index seq2 i with
	    | true, true ->
              let (x0, p0) = select_index seq1 i in
	      let (x1, p1) = select_index seq2 i in
              x0 == x1 /\ summable_permissions p0 p1
            | _ -> True
          ) = match contains_index seq1 i, contains_index seq2 i with
	    | true, true ->
              let (x0, p0) = select_index seq1 i in
	      let (x1, p1) = select_index seq2 i in
              assert(x0 == x1);
              assume(p0 == half_permission p);
              assume(p1 == half_permission p);
              ()
            | _ -> ()
          in
          Classical.forall_intro aux
        | _ -> ()
      in
      Classical.forall_intro aux;
      assert(disjoint split_h_1 split_h_2);
      let aux (addr: addr) : Lemma ((join split_h_1 split_h_2) addr == h addr) =
        if addr <> a.array_addr then () else match split_h_1 addr, split_h_2 addr, h addr with
        | Some (Array t1 len1 seq1), Some (Array t2 len2 seq2), Some (Array t len seq) ->
          assert(t1 == t2 /\ t == t1);
          assert(len1 == len2 /\ len == len1);
          let aux (i:nat{i < len1}) : Lemma (
            match contains_index seq1 i,  contains_index seq2 i with
	    | true, true ->
              let (_, p1) = select_index seq1 i in
              let (x0, p0) = select_index seq2 i in
	      Seq.index seq i == Some(x0, sum_permissions p0 p1)
            | true, false -> Seq.index seq i == Seq.index seq1 i
            | false, true -> Seq.index seq i == Seq.index seq2 i
	    | false, false -> Seq.index seq i == None
          ) = match contains_index seq1 i, contains_index seq2 i with
	    | true, true ->
              let (x0, p0) = select_index seq1 i in
	      let (x1, p1) = select_index seq2 i in
              assume(p0 == half_permission p);
              assume(p1 == half_permission p);
              assert(p == sum_permissions (half_permission p) (half_permission p));
              admit()
            | _ -> ()
          in
          Classical.forall_intro aux;
          admit()
        | _ -> ()
      in
      Classical.forall_intro aux;
      mem_equiv_eq (join split_h_1 split_h_2) h;
      (| a, h|)
#pop-options

let share_array
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  : m_action
    (pts_to_array a p iseq)
    (a':array_ref t{
      length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
      address a = address a'
    })
    (fun a' -> star
      (pts_to_array a (half_permission p) iseq)
      (pts_to_array a' (half_permission p) (Ghost.hide (Ghost.reveal iseq)))
    )
    =
    admit()

let gather_array
  (#t: _)
  (a: array_ref t)
  (a':array_ref t{
    length a' = length a /\ offset a' = offset a /\ max_length a' = max_length a /\
    address a = address a'
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  : m_action
    (star
      (pts_to_array a (half_permission p) iseq)
      (pts_to_array a' (half_permission p) (Ghost.hide (Ghost.reveal iseq)))
    )
    unit
    (fun _ -> pts_to_array a p iseq)
    =
    admit()

let split_array
  (#t: _)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: permission{allows_read p})
  (i:U32.t{U32.v i < U32.v (length a)})
  : m_action
    (pts_to_array a p iseq)
    (as:(array_ref t & array_ref t){(
      length (fst as) = i /\ length (snd as) = U32.sub (length a) i /\
      offset (fst as) = offset a /\ offset (snd as) = U32.add (offset a) i /\
      max_length (fst as) = max_length a /\ max_length (snd as) = max_length a /\
      address (fst as) = address a /\ address (snd as) = address a
    )})
    (fun (a1, a2) -> star
      (pts_to_array a1 p (Seq.slice iseq 0 (U32.v i)))
      (pts_to_array a2 p (Seq.slice iseq (U32.v i) (U32.v (length a))))
    )
  =
  admit()

let glue_array
  (#t: _)
  (a: array_ref t)
  (a': array_ref t{
    address a = address a' /\ max_length a = max_length a' /\
    offset a' = U32.add (offset a) (length a)
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (iseq': Ghost.erased (Seq.lseq t (U32.v (length a'))))
  (p: permission{allows_read p})
  : m_action
    (star (pts_to_array a p iseq) (pts_to_array a' p iseq'))
    (new_a:array_ref t{
      address new_a = address a /\ max_length new_a = max_length a /\
      offset new_a = offset a /\ length new_a = U32.add (length a) (length a')
    })
    (fun new_a -> pts_to_array new_a p (Seq.Base.append iseq iseq'))
  =
  admit()

////////////////////////////////////////////////////////////////////////////////
// Locks
////////////////////////////////////////////////////////////////////////////////


let lock (p:hprop) = nat

module L = FStar.List.Tot

let new_lock_pre_m_action (p:hprop)
  : pre_m_action p (lock p) (fun _ -> emp)
  = fun m ->
     let l = Available p in
     let locks' = l :: m.locks in
     assert (interp (lock_store_invariant locks') (heap_of_mem m));
     let mem :mem = { m with locks = locks' } in
     assert (locks_invariant mem == p `star` locks_invariant m);
     assert (interp (locks_invariant mem) (heap_of_mem mem));
     emp_unit (locks_invariant mem);
     star_commutative emp (locks_invariant mem);
     assert (interp (emp `star` locks_invariant mem) (heap_of_mem mem));
     let lock_id = List.Tot.length locks' - 1 in
     (| lock_id, mem |)

let emp_unit_left (p:hprop)
  : Lemma
    ((emp `star` p) `equiv` p)
  = emp_unit p;
    star_commutative emp p

let equiv_star_left (p q r:hprop)
  : Lemma
    (requires q `equiv` r)
    (ensures (p `star` q) `equiv` (p `star` r))
  = ()

#push-options "--warn_error -271 --max_fuel 2 --initial_fuel 2"
let new_lock_is_frame_preserving (p:hprop)
  : Lemma (is_m_frame_preserving (new_lock_pre_m_action p))
  = let aux (frame:hprop) (m:hmem (p `star` frame))
      : Lemma
          (ensures (
            let (| x, m1 |) = new_lock_pre_m_action p m in
            interp (emp `star` frame `star` locks_invariant m1) (heap_of_mem m1)))
          [SMTPat ()]
      = let (| x, m1 |) = new_lock_pre_m_action p m in
        assert (m1.locks == Available p :: m.locks);
        assert (locks_invariant m1 == (p `star` locks_invariant m));
        assert (interp ((p `star` frame) `star` locks_invariant m) (heap_of_mem m));
        star_associative p frame (locks_invariant m);
        assert (interp (p `star` (frame `star` locks_invariant m)) (heap_of_mem m));
        star_commutative frame (locks_invariant m);
        equiv_star_left p (frame `star` locks_invariant m) (locks_invariant m `star` frame);
        assert (interp (p `star` (locks_invariant m `star` frame)) (heap_of_mem m));
        star_associative p (locks_invariant m) frame;
        assert (interp ((p `star` locks_invariant m) `star` frame) (heap_of_mem m));
        assert (interp ((locks_invariant m1) `star` frame) (heap_of_mem m));
        assert (heap_of_mem m == heap_of_mem m1);
        star_commutative (locks_invariant m1) frame;
        assert (interp (frame `star` (locks_invariant m1)) (heap_of_mem m1));
        emp_unit_left (frame `star` (locks_invariant m1));
        assert (interp (emp `star` (frame `star` (locks_invariant m1))) (heap_of_mem m1));
        star_associative emp frame (locks_invariant m1)
    in
    ()
#pop-options

let new_lock (p:hprop)
  : m_action p (lock p) (fun _ -> emp)
  = new_lock_is_frame_preserving p;
    new_lock_pre_m_action p

////////////////////////////////////////////////////////////////////////////////
assume
val get_lock (l:lock_store) (i:nat{i < L.length l})
  : (prefix : lock_store &
     li : lock_state &
     suffix : lock_store {
       l == L.(prefix @ (li::suffix)) /\
       L.length (li::suffix) == i + 1
     })

let lock_i (l:lock_store) (i:nat{i < L.length l}) : lock_state =
  let (| _, li, _ |) = get_lock l i in
  li

assume
val lock_store_invariant_append (l1 l2:lock_store)
  : Lemma (lock_store_invariant (l1 @ l2) `equiv`
           (lock_store_invariant l1 `star` lock_store_invariant l2))

let hprop_of_lock_state (l:lock_state) : hprop =
  match l with
  | Available p -> p
  | Locked p -> p

let lock_ok (#p:hprop) (l:lock p) (m:mem) =
  l < L.length m.locks /\
  hprop_of_lock_state (lock_i m.locks l) == p

let lock_store_evolves : Preorder.preorder lock_store =
  fun (l1 l2 : lock_store) ->
    L.length l2 >= L.length l1 /\
    (forall (i:nat{i < L.length l1}).
       hprop_of_lock_state (lock_i l1 i) ==
       hprop_of_lock_state (lock_i l2 i))

let mem_evolves : Preorder.preorder mem =
  fun m0 m1 -> lock_store_evolves m0.locks m1.locks

let lock_ok_stable (#p:_) (l:lock p) (m0 m1:mem)
  : Lemma (lock_ok l m0 /\
           m0 `mem_evolves` m1 ==>
           lock_ok l m1)
  = ()

let pure (p:prop) : hprop = refine emp (fun _ -> p)

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let intro_pure (p:prop) (q:hprop) (h:hheap q { p })
  : hheap (pure p `star` q)
  = emp_unit q;
    star_commutative q emp;
    h
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let intro_hmem_or (p:prop) (q:hprop) (h:hmem q)
  : hmem (h_or (pure p) q)
  = h
#pop-options

let middle_to_head (p q r:hprop) (h:hheap (p `star` (q `star` r)))
  : hheap (q `star` (p `star` r))
  = star_associative p q r;
    star_commutative p q;
    star_associative q p r;
    h

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let maybe_acquire #p (l:lock p) (m:mem { lock_ok l m } )
  : (b:bool &
     m:hmem (h_or (pure (b == false)) p))
  = let (| prefix, li, suffix |) = get_lock m.locks l in
    match li with
    | Available _ ->
      let h = heap_of_mem m in
      assert (interp (lock_store_invariant m.locks) h);
      lock_store_invariant_append prefix (li::suffix);
      assert (lock_store_invariant m.locks `equiv`
             (lock_store_invariant prefix `star`
                      (p `star` lock_store_invariant suffix)));
      assert (interp (lock_store_invariant prefix `star`
                       (p `star` lock_store_invariant suffix)) h);
      let h = middle_to_head (lock_store_invariant prefix) p (lock_store_invariant suffix) h in
      assert (interp (p `star`
                        (lock_store_invariant prefix `star`
                         lock_store_invariant suffix)) h);
      let new_lock_store = prefix @ (Locked p :: suffix) in
      lock_store_invariant_append prefix (Locked p :: suffix);
      assert (lock_store_invariant new_lock_store `equiv`
              (lock_store_invariant prefix `star`
                         lock_store_invariant suffix));
      equiv_star_left p (lock_store_invariant new_lock_store)
                        (lock_store_invariant prefix `star`
                          lock_store_invariant suffix);
      assert (interp (p `star` lock_store_invariant new_lock_store) h);
      let h : hheap (p `star` lock_store_invariant new_lock_store) = h in
      assert (heap_of_mem m == h);
      star_commutative p (lock_store_invariant new_lock_store);
      affine_star (lock_store_invariant new_lock_store) p h;
      assert (interp (lock_store_invariant new_lock_store) h);
      let mem : hmem p = { m with locks = new_lock_store } in
      let b = true in
      let mem : hmem (h_or (pure (b==false)) p) = intro_hmem_or (b == false) p mem in
      (| b, mem |)

    | Locked _ ->
      let b = false in
      assert (interp (pure (b == false)) (heap_of_mem m));
      let h : hheap (locks_invariant m) = heap_of_mem m in
      let h : hheap (pure (b==false) `star` locks_invariant m) =
        intro_pure (b==false) (locks_invariant m) h in
      intro_or_l (pure (b==false) `star` locks_invariant m)
                 (p `star` locks_invariant m)
                 h;
      or_star (pure (b==false)) p (locks_invariant m) h;
      assert (interp (h_or (pure (b==false)) p `star` locks_invariant m) h);
      (| false, m |)
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"
let hmem_emp (p:hprop) (m:hmem p) : hmem emp = m
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 20"
let release #p (l:lock p) (m:hmem p { lock_ok l m } )
  : (b:bool &
     hmem emp)
  = let (| prefix, li, suffix |) = get_lock m.locks l in
    let h = heap_of_mem m in
    lock_store_invariant_append prefix (li::suffix);
    assert (interp (p `star`
                     (lock_store_invariant prefix `star`
                       (lock_store_invariant (li::suffix)))) h);
    match li with
    | Available _ ->
      (* this case is odd, but not inadmissible.
         We're releasing a lock that was not previously acquired.
         We could either fail, or just silently proceed.
         I choose to at least signal this case in the result
         so that we can decide to fail if we like, at a higher layer.

         Another cleaner way to handle this would be to insist
         that lockable resources are non-duplicable ...
         in which case this would be unreachable, since we have `p star p` *)
      (| false, hmem_emp p m |)

    | Locked _ ->
      assert (interp (p `star`
                        (lock_store_invariant prefix `star`
                          (lock_store_invariant suffix))) h);
      let h = middle_to_head p (lock_store_invariant prefix) (lock_store_invariant suffix) h in
      assert (interp (lock_store_invariant prefix `star`
                        (p `star`
                          (lock_store_invariant suffix))) h);
      let new_lock_store = prefix @ (Available p :: suffix) in
      lock_store_invariant_append prefix (Available p :: suffix);
      assert (lock_store_invariant new_lock_store `equiv`
                (lock_store_invariant prefix `star`
                 (p `star` lock_store_invariant (suffix))));
      assert (interp (lock_store_invariant new_lock_store) h);
      emp_unit_left (lock_store_invariant new_lock_store);
      let mem : hmem emp = { m with locks = new_lock_store } in
      (| true, mem |)
#pop-options
