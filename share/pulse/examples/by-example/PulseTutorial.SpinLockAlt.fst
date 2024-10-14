module PulseTutorial.SpinLock
#lang-pulse
open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module U32 = FStar.UInt32

let cas_u32 (r:B.box U32.t) (u v:U32.t) (#i:erased U32.t)
 : stt_atomic bool #Observable emp_inames 
    (B.pts_to r i)
    (fun b ->
      if b
      then (B.pts_to r v ** pure (reveal i == u)) 
      else (B.pts_to r i))
  = cas_box r u v #i
  
noeq
type lock = { r:B.box U32.t;  i:iname; }

[@@pulse_unfold]
let lock_inv (r:B.box U32.t) (p:slprop) : v:slprop { is_storable p ==> is_storable v } =
  exists* v. B.pts_to r v ** (if (v=0ul) then p else emp)

[@@pulse_unfold]
let protects (l:lock) (p:slprop) = inv l.i (lock_inv l.r p)

fn new_lock (p:storable)
requires p
returns l:lock
ensures protects l p
{
  let r = B.alloc 0ul;
  let i = new_invariant (lock_inv r p);
  ({r;i})
}


fn rec acquire #p (l:lock)
requires protects l p
ensures protects l p ** p
{
  let retry = 
    with_invariants l.i
      returns retry:bool
      ensures lock_inv l.r p ** (if retry then emp else p)
      opens [l.i]
  {
    let acquired = cas_u32 l.r 0ul 1ul;
    if acquired { false } else { true }
  };
  if retry { acquire l }
}


fn release #p (l:lock)
requires protects l p ** p
ensures protects l p
{
  with_invariants l.i
  {
    write_atomic_box l.r 0ul;
    drop_ (if _ then _ else _);
  }
}