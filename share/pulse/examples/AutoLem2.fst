module AutoLem2

open Pulse.Lib.Pervasives
open FStar.Tactics.V2

(* Shadow the one in the library so its own primitive
automation does not apply.*)
assume
val pts_to (#a:Type) (r:ref a) (#f:perm) ([@@@equate_by_smt] n:a) 
    : vprop

// assume
// val gather (#a:Type) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
//   : stt_ghost unit
//       (pts_to r #p0 x0 ** pts_to r #p1 x1)
//       (fun _ -> pts_to r #(sum_perm p0 p1) x0 ** pure (x0 == x1))

// [@@guided_autolem]
assume
val share2 (#a:Type) (#f:perm) (r:ref a) (#v:erased a)
  : stt_ghost unit
      (pts_to r #f v)
      (fun _ -> pts_to r #(half_perm f) v ** pts_to r #(half_perm f) v)

[@@guided_autolem]
assume
val gather2 (#a:Type) (r:ref a) (#f:perm) (#x0 #x1:erased a)
  : stt_ghost unit
      (pts_to r #(half_perm f) x0 ** pts_to r #(half_perm f) x1)
      (fun _ -> pts_to r #f x0 ** pure (x0 == x1))


#set-options "--print_implicits --print_full_names"

// ```pulse
// fn test_share1 (r : ref int) (f:perm)
//   requires pts_to r #f 1
//   ensures pts_to r #(half_perm f) 1
//        ** pts_to r #(half_perm f) 1
// {
//   ()
// }
// ```

// assume
// val share (#a:Type) (r:ref a) (#v:erased a) (#p:perm)
//   : stt_ghost unit
//       (pts_to r #p v)
//       (fun _ ->
//        pts_to r #(half_perm p) v **
//        pts_to r #(half_perm p) v)

```pulse
fn test_gather1 (r : ref int) (f:perm)
  requires pts_to r #one_half 1
        ** pts_to r #one_half 1
  ensures pts_to r #full_perm 1
{
  ();
}
```

```pulse
fn test_gather1_exists (r : ref int) (f:perm)
  requires (exists* v. pts_to r #(half_perm f) v)
        ** pts_to r #(half_perm f) 1
  ensures pts_to r #f 1
{
  ()
}
```

```pulse
fn test_gather2_exists (r : ref int) (f:perm)
  requires pts_to r #(half_perm f) 1
        ** (exists* v. pts_to r #(half_perm f) v)
  ensures pts_to r #f 1
{
  ()
}
```

```pulse
fn test_gather3_exists (r : ref int) (f:perm)
  requires (exists* v. pts_to r #(half_perm f) v)
        ** (exists* v. pts_to r #(half_perm f) v)
  ensures (exists* v. pts_to r #f v)
{
  // FIXME: scoping
  admit()
}
```

```pulse
fn test_gather_het1 (r : ref int) (v:int) (f:perm)
  requires pts_to r #(half_perm f) 1
        ** pts_to r #(half_perm f) v
  ensures pts_to r #f 1
{
  ()
}
```

```pulse
fn test_gather_het2 (r : ref int) (v:int) (f:perm)
  requires pts_to r #(half_perm f) 1
        ** pts_to r #(half_perm f) v
  ensures pts_to r #f v
{
  ();
}
```


```pulse
fn test_gather2 (r : ref int)
  requires pts_to r #(half_perm full_perm) 1
        ** pts_to r #(half_perm (half_perm full_perm)) 1
        ** pts_to r #(half_perm (half_perm full_perm)) 1
  ensures pts_to r 1
{
  assert (pts_to r #(half_perm full_perm) 1 ** pts_to r #(half_perm full_perm) 1);
  ()
}
```

```pulse
fn test_share2 (r : ref int)
  requires pts_to r 1
  ensures  pts_to r #(half_perm full_perm) 1
        ** pts_to r #(half_perm (half_perm full_perm)) 1
        ** pts_to r #(half_perm (half_perm full_perm)) 1
{
  ()
}
```

```pulse
fn test_share2_0 (r : ref int)
  requires pts_to r 1
  ensures  pts_to r #(half_perm (half_perm full_perm)) 1
        ** pts_to r #(half_perm (half_perm full_perm)) 1
        ** pts_to r #(half_perm (half_perm full_perm)) 1
        ** pts_to r #(half_perm (half_perm full_perm)) 1
{
  ()
}
```

```pulse
fn need_quarter (r : ref int) (f:perm)
  requires pts_to r #(half_perm (half_perm f)) 1
  ensures  pts_to r #(half_perm (half_perm f)) 1
{
  ()
}
```

```pulse
fn test_call_quarter (r: ref int)
  requires pts_to r 1
  ensures  pts_to r 1
{
  need_quarter r full_perm;
  gather r;
  gather r;
}
```


```pulse
fn test_gather3 (r : ref int) (s : ref int)
  requires pts_to r #(half_perm full_perm) 1
        ** pts_to r #(half_perm full_perm) 1
        ** pts_to s 2
  ensures pts_to r 1 ** pts_to s 2
{
  ()
}
```

```pulse
fn test_share3 (r : ref int) (s : ref int)
  requires pts_to r 1 ** pts_to s 2
  ensures  pts_to r #(half_perm full_perm) 1
        ** pts_to r #(half_perm full_perm) 1
        ** pts_to s 2
{
  ()
}
```

```pulse
fn test_gather4 (r : ref int) (s : ref int)
  requires pts_to r #(half_perm full_perm) 1
        ** pts_to r #(half_perm full_perm) 1
        ** pts_to s #(half_perm full_perm) 2
        ** pts_to s #(half_perm full_perm) 2
  ensures pts_to r 1 ** pts_to s 2
{
  ()
}
```

```pulse
fn test_share4 (r : ref int) (s : ref int)
  requires pts_to r 1 ** pts_to s 2
  ensures  pts_to r #(half_perm full_perm) 1
        ** pts_to r #(half_perm full_perm) 1
        ** pts_to s #(half_perm full_perm) 2
        ** pts_to s #(half_perm full_perm) 2
{
  ()
}
```

```pulse
fn test_share5 (r : ref int) (s : ref int)
  requires
        pts_to r 1
     ** pts_to s #(half_perm full_perm) 2
     ** pts_to s #(half_perm full_perm) 2
  ensures  pts_to r #(half_perm full_perm) 1
        ** pts_to r #(half_perm full_perm) 1
        ** pts_to s #(half_perm full_perm) 2
        ** pts_to s #(half_perm full_perm) 2
{
  ()
}
```

```pulse
fn test_gather5 (r : ref int) (s : ref int)
  requires pts_to r #(half_perm full_perm) 1
        ** pts_to r #(half_perm full_perm) 1
        ** pts_to s #(half_perm full_perm) 2
        ** pts_to s #(half_perm full_perm) 2
  ensures 
        pts_to r 1
     ** pts_to s #(half_perm full_perm) 2
     ** pts_to s #(half_perm full_perm) 2
{
  ()
}
```

```pulse
fn test_gather6 (r : ref int) (s : ref int)
  requires pts_to s #full_perm 2
  ensures pts_to s #(half_perm full_perm) 2
       ** pts_to s #(half_perm (half_perm full_perm)) 2
       ** pts_to s #(half_perm (half_perm full_perm)) 2
{
  ()
}
```

```pulse
fn test_share6 (r : ref int) (s : ref int)
  requires pts_to s #(half_perm full_perm) 2
       ** pts_to s #(half_perm (half_perm full_perm)) 2
       ** pts_to s #(half_perm (half_perm full_perm)) 2
  ensures pts_to s #full_perm 2
{
  gather s;
  gather s;
}
```

