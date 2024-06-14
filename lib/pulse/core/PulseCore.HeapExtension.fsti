module PulseCore.HeapExtension
open PulseCore.HeapSig

let boxable (h:heap_sig u#a) = p:h.slprop { h.up (h.down p) == p }

val extend (h:heap_sig u#a) : h2:heap_sig u#(a + 1) { h2.bprop == h.slprop }

val lift_iref (#h:heap_sig u#a) (i:h.iref) : (extend h).iref
val lift_iname (#h:heap_sig u#a) (i:h.iname) : (extend h).iname
val lift_inames (#h:heap_sig u#a) (is:inames h) : inames (extend h)

val lift_action
    (#h:heap_sig u#h)
    (#a:Type u#a)
    (#mg:bool)
    (#ex:inames h)
    (#pre:h.slprop)
    (#post:a -> h.slprop)
    (action:_action_except h a mg ex pre post)
: _action_except (extend h)
    a mg (lift_inames ex) 
    ((extend h).up pre)
    (fun x -> (extend h).up (post x))

 val dup_inv 
    (#h:heap_sig u#a)
    (e:inames (extend h))
    (i:(extend h).iref)
    (p:(extend h).slprop)
: ghost_action_except (extend h) unit e 
    ((extend h).inv i p) 
    (fun _ -> (extend h).inv i p `(extend h).star` (extend h).inv i p)

val new_invariant
    (#h:heap_sig u#a) 
    (e:inames (extend h))
    (p:boxable (extend h))
: ghost_action_except (extend h) 
    (extend h).iref
    e
    p
    (fun i -> (extend h).inv i p)
(*
val with_invariant
    (#h:heap_sig u#a)
    (#a:Type u#aa)
    (#fp:(extend h).slprop)
    (#fp':(a -> (extend h).slprop))
    (#opened_invariants:inames (extend h))
    (#p:(extend h).slprop)
    (#maybe_ghost:bool)
    (i:(extend h).iref{not (Set.mem ((extend h).iname_of i) opened_invariants)})
    (f:_action_except (extend h) a maybe_ghost
      (Set.add ((extend h).iname_of i) opened_invariants) 
      (p `(extend h).star` fp)
      (fun x -> p `(extend h).star` fp' x))
: _action_except (extend h) a maybe_ghost opened_invariants 
      ((extend h).inv i p `(extend h).star` fp)
      (fun x -> (extend h).inv i p `(extend h).star` fp' x)

val lift_inv (h:heap_sig u#a) (i:h.iref) (p:h.slprop)
: Lemma ((extend h).up (h.inv i p) == (extend h).inv (lift_iref i) ((extend h).up p))

open FStar.PCM
open FStar.Ghost
#push-options "--print_universes"
val sel_action
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (r:ref a pcm)
    (v0:erased a)
: action_except
    (extend h)
    (v:a{compatible pcm v0 v}) e 
    ((extend h).pts_to r v0) 
    (fun _ -> (extend h).pts_to r v0)

val upd_action
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:a {FStar.PCM.frame_preserving pcm v0 v1 /\ pcm.refine v1})
: action_except
    (extend h)
    unit e 
    ((extend h).pts_to r v0)
    (fun _ -> (extend h).pts_to r v1)

val free_action
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (r:ref a pcm)
    (x:FStar.Ghost.erased a{FStar.PCM.exclusive pcm x /\ pcm.refine pcm.FStar.PCM.p.one})
: action_except
    (extend h)
    unit e 
    ((extend h).pts_to r x)
    (fun _ -> (extend h).pts_to r pcm.FStar.PCM.p.one)

(** Splitting a permission on a composite resource into two separate permissions *)
val split_action
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: ghost_action_except
    (extend h)
    unit e
    ((extend h).pts_to r (v0 `op pcm` v1))
    (fun _ -> (extend h).pts_to r v0 `(extend h).star` (extend h).pts_to r v1)

(** Combining separate permissions into a single composite permission *)
val gather_action
  (#h:heap_sig u#h)
  (#a:Type u#(h + 1))
  (#pcm:pcm a)
  (e:inames _)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a)
: ghost_action_except
    (extend h)
    (squash (composable pcm v0 v1)) e
    ((extend h).pts_to r v0 `(extend h).star` (extend h).pts_to r v1)
    (fun _ -> (extend h).pts_to r (op pcm v0 v1))

val alloc_action
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (x:a{pcm.refine x})
: action_except
    (extend h)
    (ref a pcm) e
    (extend h).emp
    (fun r -> (extend h).pts_to r x)

val select_refine
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#p:pcm a)
    (e:inames _)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: action_except
    (extend h)
    (v:a{compatible p x v /\ p.refine v}) e
    ((extend h).pts_to r x)
    (fun v -> (extend h).pts_to r (f v))

val upd_gen
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#p:pcm a)
    (e:inames _) 
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: action_except
    (extend h)
    unit e
    ((extend h).pts_to r x)
    (fun _ -> (extend h).pts_to r y)

val pts_to_not_null_action 
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (r:erased (ref a pcm))
    (v:Ghost.erased a)
: ghost_action_except
    (extend h)
    (squash (not (is_null r))) e
    ((extend h).pts_to r v)
    (fun _ -> (extend h).pts_to r v)

    *)