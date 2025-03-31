module NuWhile

#lang-pulse
open Pulse.Nolib

assume val p : int -> slprop

fn chk (x : int)
  requires p x
  returns  bool
  ensures  p x
{ false }

fn use (x : int)
  requires p x
  ensures  p x
{ () }

ghost
fn use_ghost (x : int)
  requires p x
  ensures  p x
{ () }

ghost
fn use_ghost_incr (x : int)
  requires p x
  ensures  p (x+1)
{ admit() }

[@@expect_failure] // kinda silly that this fails
fn nohint()
{
  { (); (); };
  ()
}

fn test0 ()
  requires p 1 ** p 2 ** p 3
  ensures  p 1 ** p 2 ** p 3
{
  nuwhile (chk 2)
    (* Invariant is inferred to be the full context: p 1 ** p 2 ** p 3 *)
    (* We can also specify any of them here (only once, of course, they are
    combined with ** ), that does not change much. *)
    invariant p 1
    invariant p 2
  { use 3; use 2; };
  ();
  (* all resources are still there *)
  use 1;
  use 2;
  use 3;
}

fn test1 ()
  requires exists* x. p x
  ensures  exists* x. p x
{
  nuwhile (true)
    (* The invariant (= ctxt) here is inferred to be p x0, with x0 having been
    eliminated into the environment. *)
  { use_ghost _; };
  ();
  use_ghost _;
}

[@@expect_failure]
fn test2 ()
  requires exists* x. p x
  ensures exists* x. p x
{
  nuwhile (true)
    (* Same as above, but that invariant does not work as we are
    changing x every iteration. *)
  { use_ghost_incr _; };
  ();
}

assume val q : slprop

fn use_q ()
  requires q
  ensures  q
{ () }

fn test3 ()
  requires q ** (exists* x. p x)
  ensures  q ** (exists* x. p x)
{
  // with x. assert (p x);
  nuwhile (false)
    (* Specifying a weaker invariant works. *)
    invariant exists* x. p x
  { 
    assert q;
    use_q ();
    use_ghost_incr _;
  };
  use_ghost _;
  assert q;
  // chk _;
  use_ghost _;
  ()
}


fn true_cond ()
  returns b : bool
  ensures pure (b == true)
{ true }

fn test_inf_loop ()
{
  nuwhile (true_cond ())
  { () };
  assert (pure False);
}
