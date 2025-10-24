module Pulse.Lib.WithPure
#lang-pulse
open Pulse.Lib.Core
open Pulse.Main


let with_pure
  (p : prop)
  (v : squash p -> slprop)
: slprop
= exists* h. v h
// Alternative definition:
// = exists* v'. tag v' ** pure (p /\ v' == v ())
// much easier to work with, but proving the size wasn't obvious.

let with_pure_timeless
  (p : prop)
  (v : squash p -> slprop)
: Lemma (requires forall s. timeless (v s))
        (ensures  timeless (with_pure p v))
        [SMTPat (timeless (with_pure p v))]
= assert_norm (with_pure p v == (exists* h. v h))

let is_send_across_with_pure p v #_ = Tactics.Typeclasses.solve

ghost
fn intro_with_pure
  (p : prop)
  (v : squash p -> slprop)
  (_ : squash p)
  requires v ()
  ensures  with_pure p v
{
  assert (v ());
  fold (with_pure p v);
}



ghost
fn squash_single_coerce
  (p : prop)
  (v : squash p -> slprop)
  (s : squash p)
  requires v s
  ensures  pure p ** v ()
{
  rewrite v s as v ();
  ();
}



ghost
fn elim_with_pure
  (p : prop)
  (v : squash p -> slprop)
  requires with_pure p v
  returns  s : squash p
  ensures  v ()
{
  unfold (with_pure p v);
  with s. assert (v s);
  squash_single_coerce p v s;
  ()
}

