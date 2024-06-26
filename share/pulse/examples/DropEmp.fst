module DropEmp

open Pulse.Lib.Pervasives

```pulse
fn test0 (p:vprop)
  requires (if true then emp else p)
  ensures emp
{
  ();
}
```

```pulse
fn test1 (p:vprop)
  requires (if false then emp else p)
  ensures p
{
  ();
}
```

[@@expect_failure]
```pulse
fn test2 (p:vprop)
  requires (if true then emp else p)
  ensures p
{
  ();
}
```

[@@expect_failure]
```pulse
fn test3 (p:vprop)
  requires (if false then emp else p)
  ensures emp
{
  ();
}
```
