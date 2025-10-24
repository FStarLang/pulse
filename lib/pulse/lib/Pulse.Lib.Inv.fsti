module Pulse.Lib.Inv
#lang-pulse
open Pulse.Lib.Core
open Pulse.Lib.SendSync
open Pulse.Class.Duplicable
open PulseCore.Observability

val inv (i: iname) (p: slprop) : slprop

ghost fn move i p l1 l2
    (fwd: unit -> stt_ghost unit emp_inames (on l1 p) (fun _ -> on l2 p))
    (bwd: unit -> stt_ghost unit emp_inames (on l2 p) (fun _ -> on l1 p))
  requires on l1 (inv i p)
  ensures on l2 (inv i p)

instance val is_send_across_inv #b #g i p {| is_send_across #b g p |} : is_send_across g (inv i p)
instance placeless_inv i p {| inst: placeless p |} : placeless (inv i p) = is_send_across_inv i p #inst
instance is_send_inv i p {| inst: is_send p |} : is_send (inv i p) = is_send_across_inv i p #inst
instance val duplicable_inv i p : duplicable (inv i p)

ghost fn dup_inv (i:iname) (p:slprop)
  preserves inv i p
  ensures inv i p
{
  dup (inv i p) ()
}

ghost fn fresh_invariant
    (ctx: inames { Pulse.Lib.GhostSet.is_finite ctx })
    (p: slprop)
  requires p
  returns i: iname
  ensures inv i p
  ensures pure (~(Pulse.Lib.GhostSet.mem i ctx))

ghost fn new_invariant (p: slprop)
  requires p
  returns i: iname
  ensures inv i p

inline_for_extraction noextract
unobservable fn with_inv_unobs u#a (a: Type u#a)
    is (i: iname { not (mem_inv is i) }) (p: slprop) pre (post: a->slprop)
    (k: unit -> stt_atomic a #Neutral is (pre ** p) (fun x -> post x ** p))
  opens add_inv is i
  preserves inv i p
  requires later_credit 1
  requires pre
  returns x:a
  ensures post x

ghost fn with_invariants_g u#a (a: Type u#a)
    is (i: iname { not (mem_inv is i) }) (p: slprop) pre (post: a->slprop)
    (k: unit -> stt_ghost a is (pre ** p) (fun x -> post x ** p))
  opens add_inv is i
  preserves inv i p
  requires later_credit 1
  requires pre
  returns x:a
  ensures post x

inline_for_extraction noextract
atomic fn with_invariants_a u#a (a: Type u#a)
    is (i: iname { not (mem_inv is i) }) (p: slprop) pre (post: a->slprop)
    (k: unit -> stt_atomic a #Observable is (pre ** p) (fun x -> post x ** p))
  opens add_inv is i
  preserves inv i p
  requires later_credit 1
  requires pre
  returns x:a
  ensures post x

inline_for_extraction noextract
fn with_invariants u#a (a: Type u#a)
    is (i: iname { not (mem_inv is i) }) (p: slprop) pre (post: a->slprop)
    (k: unit -> stt_atomic a #Observable is (pre ** p) (fun x -> post x ** p))
  preserves inv i p
  requires pre
  returns x:a
  ensures post x