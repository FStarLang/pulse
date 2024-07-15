module Pulse.Lib.Thunk
open Pulse.Lib.Pervasives
open Pulse.Lib.Box

//
// Assume interface for slprop implication (i.e., implication at every heap).
//

assume val slimp : slprop -> slprop -> prop
assume val slimp_refl (p:slprop) : squash (slimp p p)
assume val slimp_trans (#p #q #r:slprop) (hpq : squash (slimp p q)) (hqr: squash (slimp q r)) : squash (slimp p r)
assume val slimp_pure (#p #q: prop) (h: squash (p ==> q)) : squash (slimp (pure p) (pure q))
assume val slimp_star (#p #q #p' #q': slprop) (hp: squash (slimp p p')) (hq: squash (slimp q q')) : squash (slimp (p ** q) (p' ** q'))
assume val slimp_exists #t (#p #q: t -> slprop) (h : (x:t -> squash (slimp (p x) (q x)))) : squash (slimp (exists* x. p x) (exists* x. q x))
assume val slimp_elim #p #q (h: squash (slimp p q)) : stt_ghost unit [] p (fun _ -> q)


//
// Construct a type `dynamic : Type0` which can store any value (of types in *any* universe).
// Elimination requires the `Dv` effect.  Obviously neither `dynamic` nor `to_dynamic` are injective.
//

noeq type value_type_bundle = { t: Type0; x: t }

let raw_dynamic (t: Type u#a) : Type0 = unit -> Dv (b:value_type_bundle {b.t == (unit -> Dv t)})
let to_raw_dynamic (#t: Type u#a) (x: t) : raw_dynamic t = fun _ -> { t = unit -> Dv t; x = fun _ -> x }

let dynamic : Type0 = unit -> Dv value_type_bundle
let to_dynamic (#t: Type u#a) (x: t) : dynamic = to_raw_dynamic x
let dynamic_has_ty (t: Type u#a) (y: dynamic) = exists (x: t). y == to_dynamic x

let elim_subtype_of s (t: Type { subtype_of s t }) (x: s): t = x

let of_dynamic (t: Type u#a) (y: dynamic { dynamic_has_ty t y }) : Dv t =
  let y : raw_dynamic t = elim_subtype_of _ _ y in
  let b = y () in
  let c : unit -> Dv t = b.x in
  c ()


//
// Define the `thunk` type and associated API.
//

let slimp1 (#a:Type u#aa) (p q : a -> slprop) : prop = 
  forall (x:a).
    slimp (p x) (q x)

let is_mono (#a:Type u#aa) (f: (a -> slprop) -> (a -> slprop)) : prop =
  forall p q.
    slimp1 p q ==> slimp1 (f p) (f q)

noeq type thunk_data (t: Type0) : Type0 =
  | Forced : t -> thunk_data t
  | Closure : dynamic -> thunk_data t

let thunk (t: Type0) = box (thunk_data t)

let closure_prop #t (pre: slprop) (p : t->slprop) (g: dynamic) : prop =
  exists post. slimp1 post p /\ dynamic_has_ty (unit -> stt t pre (fun x -> post x)) g

let slimp1_refl #a (p: a -> slprop) : squash (slimp1 p p) =
  introduce forall x. _ with slimp_refl _

let slimp1_trans #a (#p #q #r : a -> slprop) (hpq : squash (slimp1 p q)) (hqr : squash (slimp1 q r)) : squash (slimp1 p r) =
  introduce forall x. _ with slimp_trans #(p x) #(q x) #(r x) () ()

let thunk_data_live #t (d: thunk_data t) (p: t -> slprop) : slprop =
  match d with
  | Forced x -> p x
  | Closure g -> exists* pre. id pre ** pure (closure_prop pre p g)

let thunk_to #t (c: thunk t) (p: t -> slprop) : slprop =
  exists* v. pts_to c v ** thunk_data_live v p

let elim_exists #motive #a (#p : a->Type) (maj: squash (exists x. p x)) (elim: (x: a {p x} -> GTot (squash motive))) : squash motive =
  Classical.exists_elim motive maj elim

let elim_forall #a (#p : a->Type) (maj: squash (forall x. p x)) (x: a) : squash (p x) =
  Classical.Sugar.forall_elim x maj

let slimp_thunk_data_live #t (c: thunk_data t) #p #q (h: squash (slimp1 p q)) :
    squash (slimp (thunk_data_live c p) (thunk_data_live c q)) =
  match c returns squash (slimp (thunk_data_live c p) (thunk_data_live c q)) with
  | Forced x -> elim_forall h x
  | Closure f ->
    slimp_exists (fun _ -> slimp_star (slimp_refl _) (slimp_pure (introduce _ ==> _ with hp. elim_exists hp (fun post ->
      slimp1_trans #_ #post #p #q () ()))))

let slimp_thunk_to #t (c: thunk t) #p #q (h: squash (slimp1 p q)) :
    squash (slimp (thunk_to c p) (thunk_to c q)) =
  slimp_exists (fun v ->
    slimp_star (slimp_refl _) (slimp_thunk_data_live v h))

let slimp_thunk_to' #t (c: thunk t) #p #q (h: (x:t -> squash (slimp (p x) (q x)))) :
    squash (slimp (thunk_to c p) (thunk_to c q)) =
  slimp_thunk_to c (introduce forall (x:t). slimp (p x) (q x) with h x)

let thunk_to_mono #a #t (c: thunk t) (p: ((a->slprop) -> a-> t-> slprop)) (h: (x: t -> squash (is_mono (fun f y -> p f y x)))) :
    squash (is_mono (fun f y -> thunk_to c (p f y))) =
  introduce forall f g. _ with
  introduce _ ==> _ with _.
  introduce forall y. _ with
  slimp_thunk_to' _ (fun x ->
    Classical.Sugar.forall_elim g (Classical.Sugar.forall_elim f (h x)))

```pulse
fn alloc_thunk #t (#p: t -> slprop) (#res: slprop) (f: unit -> stt t res (fun x -> p x))
  requires res
  returns c: thunk t
  ensures thunk_to c p
{
  let g = to_dynamic f;
  let c = alloc (Closure #t g);
  slimp1_refl (fun x -> p x);
  rewrite res as id res;
  fold thunk_data_live (Closure #t g) p;
  fold thunk_to c p;
  c;
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

let indef_desc #t (#p : t -> prop) (h: squash (exists x. p x)) : GTot (x:t{ p x }) =
  IndefiniteDescription.indefinite_description_ghost t p

let indef_desc_prop #t (#p : t -> prop) (h: squash (exists x. p x)) : squash (p (indef_desc h)) =
  ()

let call_dynamic t pre post (g: dynamic { dynamic_has_ty (unit -> stt t pre (fun x -> post x)) g }) () : stt t pre (fun x -> post x) =
  hide_div (fun _ -> of_dynamic (unit -> stt t pre (fun x -> post x)) g ())

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
      with pre. assert id #slprop pre;
      let post = indef_desc (() <: squash (closure_prop pre p f));
      rewrite id pre as pre;
      let x = call_dynamic t pre post f ();
      slimp_elim #(post x) #(p x) ();
      c := Forced x;
      fold forced_thunk_to c x;
      x;
    }
  }
}
```
