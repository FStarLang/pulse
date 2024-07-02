module AutoShareGather

open Pulse.Lib.Pervasives

(*

#set-options "--print_implicits --debug prover.share_gather"

```pulse
fn test_gather1 (r : ref int) (f:perm)
  requires pts_to r #(f /. 2.0R) 1
        ** pts_to r #(f /. 2.0R) 1
  ensures pts_to r #f 1
{
  ();
}
```

```pulse
fn test_gather1_exists (r : ref int) (f:perm)
  requires (exists* v. pts_to r #(f /. 2.0R) v)
        ** pts_to r #(f /. 2.0R) 1
  ensures pts_to r #f 1
{
  // gather r;
  ()
}
```

```pulse
fn test_gather2_exists (r : ref int) (f:perm)
  requires pts_to r #(f /. 2.0R) 1
        ** (exists* v. pts_to r #(f /. 2.0R) v)
  ensures pts_to r #f 1
{
  // gather r;
  ()
}
```

```pulse
fn test_gather3_exists (r : ref int) (f:perm)
  requires (exists* v. pts_to r #(f /. 2.0R) v)
        ** (exists* v. pts_to r #(f /. 2.0R) v)
  ensures (exists* v. pts_to r #f v)
{
  // gather r;
  ()
}
```

```pulse
fn test_gather_het1 (r : ref int) (v:int) (f:perm)
  requires pts_to r #(f /. 2.0R) 1
        ** pts_to r #(f /. 2.0R) v
  ensures pts_to r #f 1
{
  ()
  // gather r;
}
```

```pulse
fn test_gather_het2 (r : ref int) (v:int) (f:perm)
  requires pts_to r #(f /. 2.0R) 1
        ** pts_to r #(f /. 2.0R) v
  ensures pts_to r #f v
{
  // gather r;
  ()
}
```

```pulse
fn test_share1 (r : ref int) (f:perm)
  requires pts_to r #f 1
  ensures pts_to r #(f /. 2.0R) 1
        ** pts_to r #(f /. 2.0R) 1
{
  admit()
}
```

```pulse
fn test_gather2 (r : ref int)
  requires pts_to r #(1.0R /. 2.0R) 1
        ** pts_to r #((1.0R /. 2.0R) /. 2.0R) 1
        ** pts_to r #((1.0R /. 2.0R) /. 2.0R) 1
  ensures pts_to r 1
{
  assert (pts_to r #(1.0R /. 2.0R) 1 ** pts_to r #(1.0R /. 2.0R) 1);
  ()
}
```

```pulse
fn test_share2 (r : ref int)
  requires pts_to r 1
  ensures  pts_to r #(half_perm 1.0R) 1
        ** pts_to r #(half_perm (half_perm 1.0R)) 1
        ** pts_to r #(half_perm (half_perm 1.0R)) 1
{
  ()
}
```

```pulse
fn test_share2_0 (r : ref int)
  requires pts_to r 1
  ensures  pts_to r #(half_perm (half_perm 1.0R)) 1
        ** pts_to r #(half_perm (half_perm 1.0R)) 1
        ** pts_to r #(half_perm (half_perm 1.0R)) 1
        ** pts_to r #(half_perm (half_perm 1.0R)) 1
{
  ()
}
```

```pulse
fn need_quarter (r : ref int) (f:perm)
  requires pts_to r #(half_perm (f /. 2.0R)) 1
  ensures  pts_to r #(half_perm (f /. 2.0R)) 1
{
  ()
}
```

```pulse
fn test_call_quarter (r: ref int)
  requires pts_to r 1
  ensures  pts_to r 1
{
  need_quarter r 1.0R;
  gather r;
  gather r;
}
```


```pulse
fn test_gather3 (r : ref int) (s : ref int)
  requires pts_to r #(half_perm 1.0R) 1
        ** pts_to r #(half_perm 1.0R) 1
        ** pts_to s 2
  ensures pts_to r 1 ** pts_to s 2
{
  ()
}
```

```pulse
fn test_share3 (r : ref int) (s : ref int)
  requires pts_to r 1 ** pts_to s 2
  ensures  pts_to r #(half_perm 1.0R) 1
        ** pts_to r #(half_perm 1.0R) 1
        ** pts_to s 2
{
  ()
}
```

```pulse
fn test_gather4 (r : ref int) (s : ref int)
  requires pts_to r #(half_perm 1.0R) 1
        ** pts_to r #(half_perm 1.0R) 1
        ** pts_to s #(half_perm 1.0R) 2
        ** pts_to s #(half_perm 1.0R) 2
  ensures pts_to r 1 ** pts_to s 2
{
  ()
}
```

```pulse
fn test_share4 (r : ref int) (s : ref int)
  requires pts_to r 1 ** pts_to s 2
  ensures  pts_to r #(half_perm 1.0R) 1
        ** pts_to r #(half_perm 1.0R) 1
        ** pts_to s #(half_perm 1.0R) 2
        ** pts_to s #(half_perm 1.0R) 2
{
  ()
}
```

```pulse
fn test_share5 (r : ref int) (s : ref int)
  requires
        pts_to r 1
     ** pts_to s #(half_perm 1.0R) 2
     ** pts_to s #(half_perm 1.0R) 2
  ensures  pts_to r #(half_perm 1.0R) 1
        ** pts_to r #(half_perm 1.0R) 1
        ** pts_to s #(half_perm 1.0R) 2
        ** pts_to s #(half_perm 1.0R) 2
{
  ()
}
```

```pulse
fn test_gather5 (r : ref int) (s : ref int)
  requires pts_to r #(half_perm 1.0R) 1
        ** pts_to r #(half_perm 1.0R) 1
        ** pts_to s #(half_perm 1.0R) 2
        ** pts_to s #(half_perm 1.0R) 2
  ensures 
        pts_to r 1
     ** pts_to s #(half_perm 1.0R) 2
     ** pts_to s #(half_perm 1.0R) 2
{
  ()
}
```

```pulse
fn test_gather6 (r : ref int) (s : ref int)
  requires pts_to s #1.0R 2
  ensures pts_to s #(half_perm 1.0R) 2
       ** pts_to s #(half_perm (half_perm 1.0R)) 2
       ** pts_to s #(half_perm (half_perm 1.0R)) 2
{
  ()
}
```

```pulse
fn test_share6 (r : ref int) (s : ref int)
  requires pts_to s #(half_perm 1.0R) 2
       ** pts_to s #(half_perm (half_perm 1.0R)) 2
       ** pts_to s #(half_perm (half_perm 1.0R)) 2
  ensures pts_to s #1.0R 2
{
  gather s;
  gather s;
}
```
