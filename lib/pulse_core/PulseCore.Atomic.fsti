module PulseCore.Atomic
open PulseCore.InstantiatedSemantics
open PulseCore.Action
open FStar.Ghost

type observability =
  | Observable
  | Unobservable

let at_most_one_observable o1 o2 =
  match o1, o2 with
  | Observable, Observable -> false
  | _ -> true

let join_obs o1 o2 =
  match o1, o2 with
  | Observable, _
  | _, Observable -> Observable
  | _ -> Unobservable

(* stt_unobservable a opens pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   takes an unobservable atomic step
   potentially opening invariants in `opens`
   and returns `x:a`
   such that the final state satisfies `post x` *)
[@@extract_as_impure_effect]
val stt_atomic
    (a:Type u#a)
    (#obs:observability)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
: Type u#(max 2 a)

val return_atomic
    (#a:Type u#a)
    (x:a)
    (p:a -> slprop)
: stt_atomic a #Unobservable emp_inames (p x) (fun r -> p r ** pure (r == x))

val return_atomic_noeq
    (#a:Type u#a)
    (x:a)
    (p:a -> slprop)
: stt_atomic a #Unobservable emp_inames (p x) p

val bind_atomic
    (#a:Type u#a)
    (#b:Type u#b)
    (#obs1:_)
    (#obs2:observability { at_most_one_observable obs1 obs2 })
    (#opens:inames)
    (#pre1:slprop)
    (#post1:a -> slprop)
    (#post2:b -> slprop)
    (e1:stt_atomic a #obs1 opens pre1 post1)
    (e2:(x:a -> stt_atomic b #obs2 opens (post1 x) post2))
: stt_atomic b #(join_obs obs1 obs2) opens pre1 post2

val lift_unobservable 
    (#a:Type u#a)
    (#obs:_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e1:stt_atomic a #obs opens pre post)
: stt_atomic a #Observable opens pre post

val lift_atomic0
    (#a:Type u#0)
    (#obs:_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens pre post)
: stt a pre post

val lift_atomic1
    (#a:Type u#1)
    (#obs:_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens pre post)
: stt a pre post

val lift_atomic2
    (#a:Type u#2)
    (#obs:_)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens pre post)
: stt a pre post

val frame_atomic
    (#a:Type u#a)
    (#obs: observability)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (frame:slprop)
    (e:stt_atomic a #obs opens pre post)
: stt_atomic a #obs opens (pre ** frame) (fun x -> post x ** frame)

val sub_atomic
    (#a:Type u#a)
    (#obs:_)
    (#opens:inames)
    (#pre1:slprop)
    (pre2:slprop)
    (#post1:a -> slprop)
    (post2:a -> slprop)
    (pf1 : slprop_equiv pre1 pre2)
    (pf2 : slprop_post_equiv post1 post2)
    (e:stt_atomic a #obs opens pre1 post1)
: stt_atomic a #obs opens pre2 post2

val sub_invs_stt_atomic
    (#a:Type u#a)
    (#obs:_)
    (#opens1 #opens2:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_atomic a #obs opens1 pre post)
    (_ : squash (inames_subset opens1 opens2))
: stt_atomic a #obs opens2 pre post

(* stt_ghost a opens pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   takes a single ghost atomic step (i.e. a step that does not modify the heap, and does not get extracted)
   potentially opening invariants in `opens`
   and returns `x:a`
   such that the final state satisfies `post x` *)
[@@ erasable]
val stt_ghost
    (a:Type u#a)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
: Type u#(max 2 a)

val return_ghost
    (#a:Type u#a)
    (x:a)
    (p:a -> slprop)
: stt_ghost a emp_inames (p x) (fun r -> p r ** pure (r == x))

val return_ghost_noeq
    (#a:Type u#a)
    (x:a)
    (p:a -> slprop)
: stt_ghost a emp_inames (p x) p

val bind_ghost
    (#a:Type u#a)
    (#b:Type u#b)
    (#opens:inames)
    (#pre1:slprop)
    (#post1:a -> slprop)
    (#post2:b -> slprop)
    (e1:stt_ghost a opens pre1 post1)
    (e2:(x:a -> stt_ghost b opens (post1 x) post2))
: stt_ghost b opens pre1 post2

type non_informative_witness (a:Type u#a) =
  x:Ghost.erased a -> y:a{y == Ghost.reveal x}

val lift_ghost
    (#a:Type u#a)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_ghost a opens pre post)
    (reveal_a:non_informative_witness a)
: stt_atomic a #Unobservable opens pre post

val frame_ghost
    (#a:Type u#a)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (frame:slprop)
    (e:stt_ghost a opens pre post)
: stt_ghost a opens (pre ** frame) (fun x -> post x ** frame)

val sub_ghost
    (#a:Type u#a)
    (#opens:inames)
    (#pre1:slprop)
    (pre2:slprop)
    (#post1:a -> slprop)
    (post2:a -> slprop)
    (pf1 : slprop_equiv pre1 pre2)
    (pf2 : slprop_post_equiv post1 post2)
    (e:stt_ghost a opens pre1 post1)
: stt_ghost a opens pre2 post2

val sub_invs_stt_ghost
    (#a:Type u#a)
    (#opens1 #opens2:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt_ghost a opens1 pre post)
    (_ : squash (inames_subset opens1 opens2))
: stt_ghost a opens2 pre post

val noop (p:slprop)
: stt_ghost unit emp_inames p (fun _ -> p)

val intro_pure (p:prop) (pf:squash p)
: stt_ghost unit emp_inames emp (fun _ -> pure p)

val elim_pure (p:prop)
: stt_ghost (squash p) emp_inames (pure p) (fun _ -> emp)

val intro_exists (#a:Type u#a) (p:a -> slprop) (x:erased a)
: stt_ghost unit emp_inames (p x) (fun _ -> exists* x. p x)

val elim_exists (#a:Type u#a) (p:a -> slprop)
: stt_ghost (erased a) emp_inames (exists* x. p x) (fun x -> p x)

val ghost_reveal (a:Type) (x:erased a)
  : stt_ghost a emp_inames emp (fun y -> pure (reveal x == y))

//////////////////////////////////////////////////////////////////

val new_invariant
    (p:slprop)
: stt_atomic (inv p) #Unobservable emp_inames p (fun _ -> emp)

val with_invariant
    (#a:Type)
    (#obs:_)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:inv p{not (mem_inv f_opens i)})
    ($f:unit -> stt_atomic a #obs f_opens
                            (p ** fp)
                            (fun x -> p ** fp' x))
: stt_atomic a #obs (add_inv f_opens i) fp fp'

////////////////////////////////////////////////////////////////////////
// References
////////////////////////////////////////////////////////////////////////
open FStar.PCM
module PP = PulseCore.Preorder

val pts_to_not_null
    (#a:Type u#1)
    (#p:FStar.PCM.pcm a)
    (r:ref a p)
    (v:a)
: stt_ghost (squash (not (is_ref_null r)))
    emp_inames 
    (pts_to r v)
    (fun _ -> pts_to r v)

val alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:a{compatible pcm x x /\ pcm.refine x})
: stt_atomic (ref a pcm)
    #Observable
    emp_inames
    emp
    (fun r -> pts_to r x)

val read
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: stt_atomic (v:a{compatible p x v /\ p.refine v})
    #Observable
    emp_inames
    (pts_to r x)
    (fun v -> pts_to r (f v))

val write
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_atomic unit
    #Observable
    emp_inames
    (pts_to r x)
    (fun _ -> pts_to r y)

val share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (pts_to r (v0 `op pcm` v1))
    (fun _ -> pts_to r v0 ** pts_to r v1)

val gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (pts_to r v0 ** pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))

val witness
    (#a:Type)
    (#pcm:pcm a)
    (r:erased (ref a pcm))
    (fact:stable_property pcm)
    (v:Ghost.erased a)
    (pf:squash (forall z. compatible pcm v z ==> fact z))
: stt_ghost
    (witnessed r fact)
    emp_inames
    (pts_to r v)
    (fun _ -> pts_to r v)

val recall
    (#a:Type u#1)
    (#pcm:pcm a)
    (#fact:property a)
    (r:erased (ref a pcm))
    (v:Ghost.erased a)
    (w:witnessed r fact)
: stt_ghost (v1:Ghost.erased a{compatible pcm v v1})
    emp_inames
    (pts_to r v)
    (fun v1 -> pts_to r v ** pure (fact v1))

////////////////////////////////////////////////////////////////////////
// References
////////////////////////////////////////////////////////////////////////
[@@erasable]
val ghost_ref (#[@@@unused] a:Type u#a) ([@@@unused]p:pcm a) : Type0
val ghost_pts_to (#a:Type u#1) (#p:pcm a) (r:ghost_ref p) (v:a) : slprop 

val ghost_alloc
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:erased a{compatible pcm x x /\ pcm.refine x})
: stt_ghost (ghost_ref pcm)
    emp_inames
    emp
    (fun r -> ghost_pts_to r x)

val ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: stt_ghost (erased (v:a{compatible p x v /\ p.refine v}))
    emp_inames
    (ghost_pts_to r x)
    (fun v -> ghost_pts_to r (f v))

val ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_ghost unit
    emp_inames
    (ghost_pts_to r x)
    (fun _ -> ghost_pts_to r y)

val ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames  
    (ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pts_to r v0 ** ghost_pts_to r v1)

val ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (ghost_pts_to r v0 ** ghost_pts_to r v1)
    (fun _ -> ghost_pts_to r (op pcm v0 v1))

val ghost_witnessed
    (#a:Type u#1)
    (#p:pcm a)
    (r:ghost_ref p)
    (f:property a)
: Type0

val ghost_witness
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (fact:stable_property pcm)
    (v:Ghost.erased a)
    (pf:squash (forall z. compatible pcm v z ==> fact z))
: stt_ghost
    (ghost_witnessed r fact)
    emp_inames
    (ghost_pts_to r v)
    (fun _ -> ghost_pts_to r v)

val ghost_recall
    (#a:Type u#1)
    (#pcm:pcm a)
    (#fact:property a)
    (r:ghost_ref pcm)
    (v:Ghost.erased a)
    (w:ghost_witnessed r fact)
: stt_ghost (v1:Ghost.erased a{compatible pcm v v1})
    emp_inames
    (ghost_pts_to r v)
    (fun v1 -> ghost_pts_to r v ** pure (fact v1))

val drop (p:slprop)
: stt_ghost unit emp_inames p (fun _ -> emp)