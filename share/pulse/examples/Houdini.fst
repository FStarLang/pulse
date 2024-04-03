module Houdini

open Pulse.Lib.Pervasives

```pulse
fn package_dup_pre
  (p q r : vprop)
  (f : (unit -> stt_ghost unit (p ** q) (fun _ -> r)))
  (dup : (unit -> stt_ghost unit q (fun _ -> q ** q)))
  requires q
  returns f' : (unit -> stt unit p (fun _ -> r))
  ensures q
{
  dup ();
  let i = new_invariant q;
  fn f' (_:unit)
    requires p
    ensures r
    // opens (add_inv emp_inames i)
  {
    with_invariants i
    {
      dup();
      f ();
    };
  };
  f'
}
```

```pulse
fn mk_houdini0
  (q : vprop)
  (dup : (unit -> stt_ghost unit q (fun _ -> q ** q)))
  requires q
  returns i : inv q
  ensures q
{
  dup ();
  new_invariant q;
}
```

```pulse
fn mk_houdini
  (q : vprop)
  (dup : (unit -> stt_ghost unit q (fun _ -> q ** q)))
  (i : inv q)
  requires emp
  returns f' : (unit -> stt_atomic unit #Unobservable (add_inv #q emp_inames i) emp (fun _ -> q))
  ensures emp
{
  unobservable
  fn f' (_:unit)
    requires emp
    ensures q
    opens (add_inv #q emp_inames i)
  {
    with_invariants i
    {
      dup();
    };
  };
  f'
}
```

```pulse
fn mk_houdini_stt
  (q : vprop)
  (dup : (unit -> stt_ghost unit q (fun _ -> q ** q)))
  requires q
  returns f' : (unit -> stt unit emp (fun _ -> q))
  ensures emp
{
  let i = new_invariant q;
  fn f' (_:unit)
    requires emp
    ensures q
  {
    with_invariants i
    {
      dup();
    };
  };
  f'
}
```
