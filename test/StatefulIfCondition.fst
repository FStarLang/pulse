module StatefulIfCondition

open Pulse.Lib.Pervasives

(* Regression test for issue #443: stateful if/match conditions *)

(* Pure conditions still work with backward-compatible syntax *)
```pulse
fn pure_condition (x : bool)
  requires emp
  ensures  emp
{
  if x {
    ();
  } else {
    ();
  }
}
```

(* Basic stateful condition — was already supported via hoisting *)
```pulse
fn basic_stateful_if (r : ref int)
  requires r |-> 'v
  ensures  r |-> 'v
{
  if (!r = 0) {
    ();
  } else {
    ();
  }
}
```

(* Nested stateful if in condition — the core of issue #443 *)
```pulse
fn nested_stateful_if (r : ref int)
  requires r |-> 0
  ensures  r |-> 0
{
  if (if true { !r = 0 } else { false }) {
    ();
  } else {
    ();
  }
}
```

(* Stateful match scrutinee *)
```pulse
fn stateful_match (r : ref int)
  requires r |-> 0
  ensures  r |-> 0
{
  match (!r) {
    0 -> { (); }
    _ -> { (); }
  }
}
```
