module Pulse.Lib.Thunk
open Pulse.Lib.Core
open Pulse.Lib.Pervasives
open Pulse.Lib.BigReference
open Pulse.Lib.Trade

assume val slimp : slprop -> slprop -> prop // pointwise implication
assume val slimp_refl (p:slprop) : squash (slimp p p)
assume val slimp_trans (#p #q #r:slprop) (hpq : squash (slimp p q)) (hqr: squash (slimp q r)) : squash (slimp p r)

assume val slimp_pure (#p #q: prop) (h: squash (p ==> q)) : squash (slimp (pure p) (pure q))

assume val slimp_star (#p #q #p' #q': slprop)
  (hp: squash (slimp p p'))
  (hq: squash (slimp q q')) :
  squash (slimp (p ** q) (p' ** q'))

assume val slimp_exists #t (#p #q: t -> slprop)
  (h : (x:t -> squash (slimp (p x) (q x)))) :
  squash (slimp (exists* x. p x) (exists* x. q x))

assume val slimp_elim #p #q (h: squash (slimp p q)) : stt_ghost unit [] p (fun _ -> q)

let slimp1 (#a:Type u#aa) (p q : a -> slprop) : prop = 
  forall (x:a).
    slimp (p x) (q x)

let is_mono (#a:Type u#aa) (f: (a -> slprop) -> (a -> slprop)) : prop =
  forall p q.
    slimp1 p q ==> slimp1 (f p) (f q)

noeq type bundled_stt (t: Type0) = {
  pre: slprop2_base;
  post: t -> slprop2_base;
  f: unit -> stt t (up2 pre) (fun x -> up2 (post x));
}

let apply #t (f: bundled_stt t) = f.f ()

noeq type thunk_data (t: Type0) : Type u#2 =
  | Forced : t -> thunk_data t
  | Closure : bundled_stt t -> thunk_data t

let thunk (t: Type) = ref (thunk_data t)

let thunk_data_live #t (d: thunk_data t) (p: t -> slprop) : slprop =
  match d with
  | Forced x -> p x
  | Closure f ->  
    up2 f.pre ** pure (forall x. slimp (up2 (f.post x)) (p x))

let thunk_to #t (c: thunk t) (p: t -> slprop) : slprop =
  exists* v. pts_to c v ** thunk_data_live v p

let slimp_thunk_data_live #t (c: thunk_data t) #p #q (h: (x:t -> squash (slimp (p x) (q x)))) :
    squash (slimp (thunk_data_live c p) (thunk_data_live c q)) =
  match c returns squash (slimp (thunk_data_live c p) (thunk_data_live c q)) with
  | Forced x -> h x
  | Closure f ->
    slimp_star (slimp_refl _) (slimp_pure (introduce _ ==> _ with hp. introduce forall x. _ with slimp_trans _ (h x)))

let slimp_thunk_to #t (c: thunk t) #p #q (h: (x:t -> squash (slimp (p x) (q x)))) :
    squash (slimp (thunk_to c p) (thunk_to c q)) =
  slimp_exists (fun v ->
    slimp_star (slimp_refl _) (slimp_thunk_data_live v h))

let thunk_to_mono #a #t (c: thunk t) (p: ((a->slprop) -> a-> t-> slprop)) (h: (x: t -> squash (is_mono (fun f y -> p f y x)))) :
    squash (is_mono (fun f y -> thunk_to c (p f y))) =
  introduce forall f g. _ with
  introduce _ ==> _ with _.
  introduce forall y. _ with
  slimp_thunk_to _ (fun x ->
    Classical.Sugar.forall_elim g (Classical.Sugar.forall_elim f (h x)))

let slprop2_is_slprop2 (p: slprop2) : squash (is_slprop2 p) = ()
let slprop2_is_slprop2' #t (p: t -> slprop2) (x: t) : squash (is_slprop2 (p x)) = ()

```pulse
fn down2_func (#t: Type0) (#pre: slprop2) (#post: t -> slprop2) (f: unit -> stt t pre (fun x -> post x)) ()
  requires up2 (down2 pre)
  returns x: t
  ensures up2 (down2 (post x))
{
  rewrite up2 (down2 pre) as pre;
  let x = f ();
  rewrite post x as up2 (down2 (post x));
  x
}
```

let alloc_thunk_lem #t (p: t -> slprop2) : squash (forall x. slimp (up2 (down2 (p x))) (p x)) =
  introduce forall x. _ with slimp_refl (p x)

```pulse
fn alloc_thunk #t (#p: t -> slprop2) (#res: slprop2) (f: unit -> stt t res (fun x -> p x))
  requires res
  returns c: thunk t
  ensures thunk_to c p
{
  let c = alloc (Closure { pre = _; post = _; f = down2_func #t #res #p f });
  rewrite res as up2 (down2 res);
  alloc_thunk_lem p;
  fold thunk_data_live (Closure { pre = _; post = _; f = down2_func #t #res #p f }) p;
  fold thunk_to c p;
  c
}
```

let forced_thunk_to #t (c: thunk t) (x: t) =
  pts_to c (Forced x)

```pulse
ghost fn end_force_thunk #t (#p: t -> slprop) (#x: t) (c: thunk t)
  requires forced_thunk_to c x ** p x
  ensures thunk_to c p
{
  unfold forced_thunk_to;
  fold thunk_data_live (Forced x) p;
  fold thunk_to c p;
}
```

```pulse
fn free_forced_thunk #t (c: thunk t) #x
  requires forced_thunk_to c x
  ensures emp
{
  unfold forced_thunk_to;
  free c;
}
```

```pulse
fn force_thunk #t (#p: t -> slprop) c
  requires thunk_to c p
  returns x:t
  ensures p x ** forced_thunk_to c x
{
  unfold thunk_to c p;
  let d = !c;
  match d {
    Forced x -> {
      assert thunk_data_live (Forced x) p;
      unfold thunk_data_live;
      assert p x;
      fold forced_thunk_to c x;
      x;
    }
    Closure f -> {
      assert thunk_data_live (Closure f) p;
      unfold thunk_data_live;
      let x = apply f;
      assert pure (forall (x: t). slimp (up2 (f.post x)) (p x));
      slimp_elim #(up2 (f.post x)) #(p x) ();
      assert p x;
      c := Forced x;
      fold forced_thunk_to c x;
      x;
    }
  }
}
```
