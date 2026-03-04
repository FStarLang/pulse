module ExtractPulseFnIface
#lang-pulse

(** Regression test for interleaving DeclToBeDesugared (Pulse fn) in .fsti/.fst.
    Tests that all patterns extract to C correctly without KrmlPrivate.

    Patterns tested:
    1. val + let (basic, always worked)
    2. fn in .fsti + fn in .fst (basic DeclToBeDesugared matching)
    3. Private helper in .fst before interface fns (skip, not mark private)
    4. Out-of-order exposed definitions (fsti: write, assign; fst: assign, let write=assign)
    5. let alias in .fst implementing fn in .fsti
    6. fn in .fsti with let definitions before fn declarations *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
module R = Pulse.Lib.Reference

// Pattern 1: val + let (basic)
val pure_add (x y : int) : int

// Pattern 2: fn in .fsti matched by fn in .fst
fn pulse_read_ref
  (r: ref int)
  (#v: Ghost.erased int)
  requires R.pts_to r v
  returns x: int
  ensures R.pts_to r v ** pure (x == Ghost.reveal v)

// Pattern 6: let definition in .fsti before fn declarations
let double (x: int) : int = pure_add x x

// Pattern 3: .fst will have a private helper before this fn
fn pulse_write_ref
  (r: ref int)
  (v: int)
  (#old: Ghost.erased int)
  requires R.pts_to r old
  ensures R.pts_to r v

// Pattern 4: Out-of-order — .fsti has write_and_return before assign_ref,
// but .fst defines assign_ref first (as the primary fn) and then
// let write_and_return = assign_ref as an alias.
fn write_and_return
  (r: ref int)
  (v: int)
  (#old: Ghost.erased int)
  requires R.pts_to r old
  returns x: int
  ensures R.pts_to r v ** pure (x == v)

fn assign_ref
  (r: ref int)
  (v: int)
  (#old: Ghost.erased int)
  requires R.pts_to r old
  returns x: int
  ensures R.pts_to r v ** pure (x == v)

// Pattern 5: fn in .fsti, let alias in .fst
fn pulse_read_ref2
  (r: ref int)
  (#v: Ghost.erased int)
  requires R.pts_to r v
  returns x: int
  ensures R.pts_to r v ** pure (x == Ghost.reveal v)
