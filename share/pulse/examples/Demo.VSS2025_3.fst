module Demo.VSS2025_3
#lang-pulse
open FStar.Mul
open Pulse.Lib
open Pulse.Lib.Pervasives

////////////////////////////////////////////////////
// A bit of concurrency
////////////////////////////////////////////////////

// All Pulse code is inherently data race free
fn update_ref (x:ref int) (v:int)
requires pts_to x 'i
ensures pts_to x v
{
  let old = !x;
  x := v;
}

[@@expect_failure]
fn parallel_update (x:ref int) (u v:int) 
requires pts_to x 'i
ensures pts_to x (u + v)
{
  let old = !x;
  par (fun _ -> update_ref x u) (fun _ -> update_ref x v);
}

fn read_into (x:ref int) (out:ref int) (#p:perm)
requires exists* v. pts_to x #p 'i ** pts_to out v
ensures pts_to x #p 'i ** pts_to out 'i
{
  let i = !x;
  out := i;
}

fn parallel_read (x:ref int)
requires pts_to x 'i
returns v:int
ensures pts_to x 'i ** pure (v = 2 * 'i)
{
  let mut out_l = 0;
  let mut out_r = 0;
  share x;
  par (fun _ -> read_into x out_l) (fun _ -> read_into x out_r);
  gather x;
  let l = !out_l;
  let r = !out_r;
  (l + r)
}

// How about atomically writing a shared ref from two threads?
// Use an invariant
module U32 = FStar.UInt32
let owns (x:ref U32.t) = exists* v. pts_to x v
let _ = write_atomic //a library function

atomic
fn _write_atomic (x:ref U32.t) (v:U32.t)
requires pts_to x 'i
ensures pts_to x v
{
  write_atomic x v
}

// A central notion in the Pulse logic is an INVARIANT

//1. Any predicate can be turned into an invariant

ghost
fn create_invariant (x:ref U32.t)
requires pts_to x 'i //lose ownership of pts_to x 'i
returns i:iname
ensures inv i (owns x) //gain ownership of inv i (owns x)
{
  fold (owns x);
  let i = new_invariant (owns x);
  i
}


//2. Invariants are freely shareable
ghost
fn share_owns (i:iname) (x:ref U32.t)
requires inv i (owns x)
ensures inv i (owns x) ** inv i (owns x)
{
  dup_inv _ _;
}

//3. Gain ownership of the underlying predicate, but only for
//an atomic step
//
//To break a circularity, opened invariants are guarded by a "later"
[@@expect_failure]
fn update_ref_inv (x:ref U32.t) (#i:iname)
requires inv i (owns x)
ensures inv i (owns x)
{
  with_invariants i { 
    unfold owns;      
  }
}

fn update_ref_inv (x:ref U32.t) (v:U32.t) (#i:iname) 
requires inv i (owns x)
ensures inv i (owns x)
{
  later_credit_buy 1;
  with_invariants i {
    later_elim _;
    unfold owns;
    write_atomic x v;
    fold owns;
    later_intro (owns x)
  }
}

[@@expect_failure]
fn update_ref_inv_par (u v:U32.t) (#i:iname)
requires emp
ensures emp
{
  let mut x = 0ul;
  create_invariant x;
  share_owns _ _;
  par (fun _ -> update_ref_inv x u) (fun _ -> update_ref_inv x v);
  show_proof_state;
}

////////////////////////////////////////////////////////////////////
// A spin lock
////////////////////////////////////////////////////////////////////
noeq
type lock = {
  i:iname;
  v:Box.box U32.t
}

let lock_owns (l:Box.box U32.t) (p:slprop) =
  exists* n. Box.pts_to l n ** (if n=0ul then p else emp)

[@@pulse_unfold]
let is_lock (l:lock) (p:slprop) =
  inv l.i (lock_owns l.v p)

fn new_lock (p:slprop)
requires p
returns l:lock
ensures is_lock l p
{
  let v = Box.alloc 0ul;
  fold (lock_owns v p);
  let i = new_invariant (lock_owns v p);
  let l = {i;v};
  l
}

atomic
fn cas_box_alt (r:Box.box U32.t) (u v:U32.t) (#i:erased U32.t)
requires Box.pts_to r i
returns b:(b:bool { b ==> reveal i == u })
ensures (if b then pts_to r v else pts_to r i)
{
  admit()
}

fn rec acquire (l:lock) (#p:slprop)
requires is_lock l p
ensures is_lock l p ** p
{
  later_credit_buy 1;
  let retry = 
    with_invariants l.i 
    returns retry:bool
    ensures later (lock_owns l.v p) ** (if retry then emp else p)
    {
      later_elim _;
      unfold lock_owns;
      with n. assert (Box.pts_to l.v n);
      let ok = cas_box_alt l.v 0ul 1ul;
      if ok 
      {
        rewrite each n as 0ul;
        fold (lock_owns l.v p);
        later_intro (lock_owns l.v p);
        false
      }
      else
      {
        fold (lock_owns l.v p);
        later_intro (lock_owns l.v p);
        true
      }
    };
  if retry { acquire l }
}

fn release (l:lock) (#p:slprop)
requires is_lock l p ** p
ensures is_lock l p
{
  later_credit_buy 1;
  with_invariants l.i
  { 
    later_elim _;
    unfold lock_owns;
    write_atomic_box l.v 0ul;
    drop_ (if _ then p else emp);
    fold (lock_owns l.v p);
    later_intro (lock_owns l.v p);
  }
}