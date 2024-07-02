module AutoLem

open Pulse.Lib.Pervasives

assume val p : int -> vprop
assume val q : int -> vprop

[@@guided_autolem]
assume
val pq : i:int -> stt_ghost unit emp_inames (p i) (fun _ -> q i)

(*

```pulse
fn test ()
  requires p 42
  ensures q 42
{
  ();
}
```
