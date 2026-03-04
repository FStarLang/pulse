module ExtractPulseFnIface
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
module R = Pulse.Lib.Reference

// Pattern 1: val + let (basic)
let pure_add (x y : int) : int = x + y

// Pattern 2: fn matched by fn
fn pulse_read_ref
  (r: ref int)
  (#v: Ghost.erased int)
  requires R.pts_to r v
  returns x: int
  ensures R.pts_to r v ** pure (x == Ghost.reveal v)
{
  let x = !r;
  x
}

// Pattern 3: Private helper NOT in .fsti — interleaver must skip past
// interface entries to avoid marking this as KrmlPrivate erroneously.
fn private_helper
  (r: ref int)
  (v: int)
  (#old: Ghost.erased int)
  requires R.pts_to r old
  ensures R.pts_to r v
{
  r := v
}

// Pattern 3 (continued): exposed fn after private helper
fn pulse_write_ref
  (r: ref int)
  (v: int)
  (#old: Ghost.erased int)
  requires R.pts_to r old
  ensures R.pts_to r v
{
  private_helper r v
}

// Pattern 4: Out-of-order — .fsti has write_and_return BEFORE assign_ref,
// but .fst defines assign_ref first and write_and_return as an alias.
// The interleaver must skip past write_and_return in the interface to
// match assign_ref, then come back for write_and_return.
fn assign_ref
  (r: ref int)
  (v: int)
  (#old: Ghost.erased int)
  requires R.pts_to r old
  returns x: int
  ensures R.pts_to r v ** pure (x == v)
{
  r := v;
  v
}

let write_and_return = assign_ref

// Pattern 5: let alias in .fst implementing fn in .fsti
let pulse_read_ref2 = pulse_read_ref
