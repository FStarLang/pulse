module PulseCore.BaseHeapSig
open PulseCore.HeapSig
open FStar.Ghost
open FStar.PCM
module H = PulseCore.Heap
module H2 = PulseCore.Heap2

type mem : Type u#(a + 1) = H2.heap u#a

let empty_mem : mem u#a = H2.empty_heap

let disjoint_mem (m0 m1: mem) : prop = H2.disjoint m0 m1

let join_mem (m0:mem) (m1:mem { disjoint_mem m0 m1 }) : mem = H2.join m0 m1

let sep : separable (mem u#a) = {
    empty = empty_mem;
    disjoint = disjoint_mem;
    join = join_mem;
    disjoint_sym = (fun m1 m2 -> H2.disjoint_sym m1 m2);
    join_commutative = (fun h0 h1 -> H2.join_commutative h0 h1); 
    disjoint_join = (fun m1 m2 m3 -> H2.disjoint_join m1 m2 m3);
    join_associative = (fun h0 h1 h2 -> H2.join_associative h0 h1 h2);
    join_empty = (fun m -> H2.join_empty m);
}

let full_mem_pred m = H2.full_heap_pred m

let is_ghost_action m0 m1 : prop =
  H2.concrete m0 == H2.concrete m1

let slprop = H2.slprop

val interp (p:slprop u#a) : affine_mem_prop u#(a+1) sep

val as_slprop (p:affine_mem_prop sep) : q:slprop{forall h. interp q h <==> p h}

let emp : slprop = H2.emp
val pure (p:prop) : slprop

let star (p1:slprop) (p2:slprop) : slprop =
  H2.star p1 p2
val star_equiv (p q:slprop u#a) (m:mem u#a)
: Lemma (
    interp (p `star` q) m <==> 
        (exists m0 m1. 
          sep.disjoint m0 m1 /\
          m == sep.join m0 m1 /\
          interp p m0 /\
          interp q m1)
  )

val slprop_extensionality (p q:slprop)
: Lemma ((forall c. interp p c <==> interp q c) ==> p == q)

val interp_as (p:affine_mem_prop sep)
: Lemma (forall c. interp (as_slprop p) c == p c)

val emp_unit (p:slprop) : Lemma (p == (p `star` emp))

let update_ghost (m0:mem u#a) (m1:erased (mem u#a) { is_ghost_action m0 m1 })
: m:mem u#a { m == reveal m1 }
= H2.upd_ghost_heap m0 m1

val pure_true_emp () : Lemma (pure True == emp)
val intro_emp (h:mem) : Lemma (interp emp h)
val pure_interp (p:prop) (c:mem) : Lemma (interp (pure p) c == p)
let base_heap : heap_sig u#a =
  {
    mem;
    sep;
    full_mem_pred;
    is_ghost_action;
    is_ghost_action_preorder= (fun _ -> ());
    update_ghost;
    slprop;
    interp;
    as_slprop;
    interp_as;
    slprop_extensionality;
    non_info_slprop = (fun x -> reveal x);
    emp;
    pure;
    star;
    intro_emp;
    pure_interp;
    pure_true_emp;
    emp_unit;
    star_equiv;
}

val core_ghost_ref_is_null (c:core_ghost_ref) : GTot bool
let non_null_core_ghost_ref = r:core_ghost_ref { not (core_ghost_ref_is_null r) }
val core_ghost_ref_as_addr (_:core_ghost_ref) : GTot nat
val addr_as_core_ghost_ref (addr:nat) : non_null_core_ghost_ref
val core_ghost_ref_as_addr_injective (c1:core_ghost_ref)
: Lemma 
  (requires not (core_ghost_ref_is_null c1))
  (ensures addr_as_core_ghost_ref (core_ghost_ref_as_addr c1) == c1)
val addr_as_core_ghost_ref_injective (a:nat)
: Lemma 
  (ensures core_ghost_ref_as_addr (addr_as_core_ghost_ref a) == a)
val select_ghost (i:nat) (m:(base_heap u#a).mem) : GTot (option (H.cell u#a))
val ghost_ctr (b:base_heap.mem) : GTot nat
let free_above_ghost_ctr (m:base_heap.mem)
: prop
= forall addr. addr >= ghost_ctr m ==> select_ghost addr m == None
val empty_mem_props () 
: Lemma (
    free_above_ghost_ctr base_heap.sep.empty /\
    ghost_ctr base_heap.sep.empty == 0
  )

val pts_to (#a:Type u#a) (#p:pcm a) (r:ref a p) (x:a) : (base_heap u#a).slprop
val ghost_pts_to (#a:Type u#a) (#p:pcm a) (r:ghost_ref a p) (x:a) : (base_heap u#a).slprop

val ghost_extend
    (#a:Type)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: ghost_action_except base_heap (ghost_ref a pcm) emp (fun r -> ghost_pts_to r x)

val ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: ghost_action_except base_heap (erased (v:a{compatible p x v /\ p.refine v}))
        (ghost_pts_to r x)
        (fun v -> ghost_pts_to r (f v)) 

val ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: ghost_action_except base_heap unit
        (ghost_pts_to r x)
        (fun _ -> ghost_pts_to r y)

val ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: ghost_action_except base_heap unit
    (ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pts_to r v0 `base_heap.star` ghost_pts_to r v1)

val ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: ghost_action_except base_heap (squash (composable pcm v0 v1))
    (ghost_pts_to r v0 `base_heap.star` ghost_pts_to r v1)
    (fun _ -> ghost_pts_to r (op pcm v0 v1))

val extend
    (#a:Type)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: action_except base_heap (ref a pcm) emp (fun r -> pts_to r x)

val read
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: action_except base_heap (v:a{compatible p x v /\ p.refine v})
    (pts_to r x)
    (fun v -> pts_to r (f v))

val write
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: action_except base_heap unit
    (pts_to r x)
    (fun _ -> pts_to r y)

val share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: ghost_action_except base_heap unit
    (pts_to r (v0 `op pcm` v1))
    (fun _ -> pts_to r v0 `base_heap.star` pts_to r v1)

val gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: ghost_action_except base_heap (squash (composable pcm v0 v1))
    (pts_to r v0 `base_heap.star` pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))

val pts_to_not_null_action 
      (#a:Type u#a)
      (#pcm:pcm a)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: ghost_action_except base_heap (squash (not (is_null r)))
    (pts_to r v)
    (fun _ -> pts_to r v)

val ghost_pts_to' (#a:Type u#a) (#p:pcm a) (r:ghost_ref a p) (x:a) : (base_heap u#(max a b)).slprop

val ghost_extend'
    (#a:Type u#a)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: ghost_action_except base_heap (ghost_ref a pcm) emp (fun r -> ghost_pts_to' u#a u#b r x)

val ghost_read'
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: ghost_action_except base_heap (erased (v:a{compatible p x v /\ p.refine v}))
        (ghost_pts_to' u#a u#b r x)
        (fun v -> ghost_pts_to' u#a u#b r (f v)) 

val ghost_write'
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: ghost_action_except base_heap unit
        (ghost_pts_to' u#a u#b r x)
        (fun _ -> ghost_pts_to' u#a u#b r y)

val ghost_share'
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: ghost_action_except base_heap unit
    (ghost_pts_to' u#a u#b r (v0 `op pcm` v1))
    (fun _ -> ghost_pts_to' u#a u#b r v0 `base_heap.star` ghost_pts_to' u#a u#b r v1)

val ghost_gather'
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: ghost_action_except base_heap (squash (composable pcm v0 v1))
    (ghost_pts_to' u#a u#b r v0 `base_heap.star` ghost_pts_to' u#a u#b r v1)
    (fun _ -> ghost_pts_to' u#a u#b r (op pcm v0 v1))

val pts_to' (#a:Type u#a) (#p:pcm a) (r:ref a p) (x:a) : (base_heap u#(max a b)).slprop

val extend'
    (#a:Type)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: action_except base_heap (ref a pcm) emp (fun r -> pts_to' u#a u#b r x)

val read'
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: action_except base_heap (v:a{compatible p x v /\ p.refine v})
    (pts_to' u#a u#b r x)
    (fun v -> pts_to' u#a u#b r (f v))

val write'
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: action_except base_heap unit
    (pts_to' u#a u#b r x)
    (fun _ -> pts_to' u#a u#b r y)

val share'
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: ghost_action_except base_heap unit
    (pts_to' u#a u#b r (v0 `op pcm` v1))
    (fun _ -> pts_to' u#a u#b r v0 `base_heap.star` pts_to' u#a u#b r v1)

val gather'
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: ghost_action_except base_heap (squash (composable pcm v0 v1))
    (pts_to' u#a u#b r v0 `base_heap.star` pts_to' u#a u#b r v1)
    (fun _ -> pts_to' u#a u#b r (op pcm v0 v1))

val pts_to_not_null_action'
      (#a:Type u#a)
      (#pcm:pcm a)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: ghost_action_except base_heap (squash (not (is_null r)))
    (pts_to' u#a u#b r v)
    (fun _ -> pts_to' u#a u#b r v)