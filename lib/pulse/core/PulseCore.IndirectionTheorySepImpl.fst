module PulseCore.IndirectionTheorySepImpl
open PulseCore.IndirectionTheory
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module T = FStar.Tactics
module PM = PulseCore.MemoryAlt
module RTC = FStar.ReflexiveTransitiveClosure
module HS = PulseCore.HeapSig
module E = PulseCore.HeapExtension
module B = PulseCore.BaseHeapSig
module IT = PulseCore.IndirectionTheory
open FStar.Ghost {erased, hide, reveal}

let address = erased nat
let pulse_mem : Type u#4 = PM.mem u#0
let pulse_core_mem : Type u#4 = PM.pulse_heap_sig.sep.core
let pulse_heap_sig : HS.heap_sig u#3 = PM.pulse_heap_sig

[@@erasable]
noeq type istore_val_ (x: Type u#4) =
  | None
  | Inv : x -> istore_val_ x
  | Pred : x -> istore_val_ x

let istore_val_le #t (x y: istore_val_ t) : prop =
  match x, y with
  | None, _ -> True
  | Inv p, Inv q -> p == q
  | Pred p, Pred q -> p == q
  | _ -> False

let map_istore_val #x #y (f: x->y) (v: istore_val_ x) : istore_val_ y =
  match v with
  | None -> None
  | Pred p -> Pred (f p)
  | Inv p -> Inv (f p)

[@@erasable]
let invariants (x:Type u#4) : Type u#4 = address ^-> istore_val_ x

let fmap #a #b (f:a -> b) 
: (invariants a ^-> invariants b)
= F.on_dom (invariants a) fun x ->
    F.on_dom address fun a ->
      map_istore_val f (x a)

let f_ext #t #s (f g: t ^-> s) (h: (x:t -> squash (f x == g x))) : squash (f == g) =
  introduce forall x. f x == g x with h x;
  F.extensionality _ _ f g

let fmap_id (a:Type) (x:invariants a)
: squash (fmap (id #a) == id #(invariants a))
= f_ext (fmap (id #a)) (id #(invariants a)) fun x ->
    f_ext (fmap (id #a) x) (id x) fun _ -> ()


let fmap_comp (a:Type) (b:Type) (c:Type) (b2c:b -> c) (a2b:a -> b)
: (squash (compose (fmap b2c) (fmap a2b) ==
            fmap (compose b2c a2b)))
= let lhs = compose (fmap b2c) (fmap a2b) in
  let rhs = fmap (compose b2c a2b) in
  f_ext lhs rhs fun x -> f_ext (lhs x) (rhs x) fun _ -> ()

noeq
type rest : Type u#4 = {
  pulse_heap : pulse_heap_sig.sep.core;
  saved_credits : erased nat;
}

let functor_heap : functor u#3 invariants = {
  fmap = fmap;
  fmap_id = fmap_id;
  fmap_comp = fmap_comp;
  tt = prop;
  t_bot = False;
  other = rest;
}

let istore : Type u#4 = knot_t functor_heap

let preworld = istore & rest
let world_pred : Type u#4 = preworld ^-> prop

let approx n : (world_pred ^-> world_pred) = approx n

let pulse_heap_le (a b: pulse_heap_sig.sep.core) : prop =
  exists c. pulse_heap_sig.sep.disjoint a c /\ b == pulse_heap_sig.sep.join a c

let istore_val = istore_val_ world_pred

let read_istore (is: istore) a : istore_val = snd (up is) a
let read (w: preworld) a = read_istore (fst w) a

let level_istore (is: istore) : nat = level is
let level_ (w: preworld) : nat = level_istore (fst w)

let approx_def n (p: world_pred) w :
    Lemma (approx n p w == (if level_ w >= n then False else p w))
      [SMTPat (approx n p w)] =
  assert_norm (approx n p w == (if level_ w >= n then False else p w))

let istore_le (x y: istore) : prop =
  level_istore x == level_istore y /\
  forall a. istore_val_le (read_istore x a) (read_istore y a)

let world_le (a b: preworld) : prop =
  let ai, ar = a in
  let bi, br = b in
  istore_le ai bi /\
  pulse_heap_le ar.pulse_heap br.pulse_heap /\
  ar.saved_credits <= br.saved_credits

let world_pred_affine (p: world_pred) : prop =
  forall a b. world_le a b /\ p a ==> p b

let age_istore_to (is: istore) (n: nat) : istore =
  down (n, snd (up is))

let age_to_ (w: preworld) (n: nat) : preworld =
  (age_istore_to (fst w) n, snd w)

let hereditary (p: world_pred) : prop =
  forall (w: preworld) (n: nat).
    n < level_ w /\ p w ==>
    p (age_to_ w n)

let slprop_ok (p: world_pred) = hereditary p /\ world_pred_affine p

let fresh_addr (is: istore) (a: address) =
  forall (b: address). b >= a ==> None? (read_istore is b)

let istore_bounded (is: istore) =
  exists a. fresh_addr is a

let istore_val_ok (v: istore_val) =
  match v with
  | None -> True
  | Pred p -> slprop_ok p
  | Inv p -> slprop_ok p

let istore_ok (is: istore) : prop =
  istore_bounded is /\
  forall a. istore_val_ok (read_istore is a)

let world_ok (w: preworld) : prop =
  istore_ok (fst w)

let slprop = p:world_pred { slprop_ok p }

let world = w:preworld { world_ok w }

let read_age_istore_to (is: istore) n a : Lemma (read_istore (age_istore_to is n) a ==
    (map_istore_val (approx n) (read_istore is a)))
    [SMTPat (read_istore (age_istore_to is n) a)] =
  up_down n (snd (up is))

let read_age_to_ (w: preworld) n a :
    Lemma (read (age_to_ w n) a == map_istore_val (approx n) (read w a)) =
  ()

let level_age_istore_to_ is n : Lemma (level_istore (age_istore_to is n) == n) [SMTPat (level_istore (age_istore_to is n))] =
  up_down n (snd (up is))

let level_age_to_ w n : Lemma (level_ (age_to_ w n) == n) =
  ()

let age_to (w: world) (n: nat) : world =
  age_to_ w n

let istore_ext (i1: istore) (i2: istore { level_istore i1 == level_istore i2 })
    (h: (a:address -> squash (read_istore i1 a == read_istore i2 a))) : squash (i1 == i2) =
  f_ext (up i1)._2 (up i2)._2 (fun a -> h a);
  down_up i1;
  down_up i2

let world_ext (w1: preworld) (w2: preworld { level_ w1 == level_ w2 /\ snd w1 == snd w2 })
    (h: (a: address -> squash (read w1 a == read w2 a))) : squash (w1 == w2) =
  istore_ext (fst w1) (fst w2) h

let world_pred_ext (f g: world_pred) (h: (w:preworld -> squash (f w <==> g w))) : squash (f == g) =
  f_ext f g fun w ->
    h w;
    PropositionalExtensionality.apply (f w) (g w)

let approx_approx m n (p: world_pred) : Lemma (approx m (approx n p) == approx (min m n) p) [SMTPat (approx m (approx n p))] =
  world_pred_ext (approx m (approx n p)) (approx (min m n) p) fun w -> ()

let age_to_age_to (w: preworld) (m n: nat) :
    Lemma (requires n <= m) (ensures age_to_ (age_to_ w m) n == age_to_ w n)
      [SMTPat (age_to_ (age_to_ w m) n)] =
  world_ext (age_to_ (age_to_ w m) n) (age_to_ w n) fun a -> ()

let age_to_rest (w: world) (n: nat) : Lemma ((age_to w n)._2 == w._2) = ()

let level (w: world) : nat = level_ w

let age1_istore (is: istore) : istore =
  if level_istore is > 0 then age_istore_to is (level_istore is - 1) else is

let age1_ (w: preworld) : w':preworld { w' == (age1_istore (fst w), snd w) } =
  if level_ w > 0 then age_to_ w (level_ w - 1) else w

let age1 (w: world) : world = age1_ w

let credits (w: world) : GTot nat =
  w._2.saved_credits

let okay_istore = is:istore { istore_ok is }
noeq type mem = {
  invariants: okay_istore;
  pulse_heap : pulse_heap_sig.mem;
  saved_credits : erased nat;
  freshness_counter: (c:erased nat { fresh_addr invariants c });
}

let core_of (m: mem) : world =
  (m.invariants, ({ pulse_heap = pulse_heap_sig.sep.core_of m.pulse_heap; saved_credits = m.saved_credits } <: rest))

let eq_at (n:nat) (t0 t1:world_pred) =
  approx n t0 == approx n t1

let eq_at_mono (p q: world_pred) m n :
    Lemma (requires n <= m /\ eq_at m p q) (ensures eq_at n p q)
      [SMTPat (eq_at m p q); SMTPat (eq_at n p q)] =
  assert approx n p == approx n (approx m p);
  assert approx n q == approx n (approx m q)

let interp p w = p w

unfold
let istore_val_compat (x y: istore_val) =
  match x, y with
  | None, _ | _, None -> True
  | Pred p0, Pred p1 -> p0 == p1
  | Inv p0, Inv p1 -> p0 == p1
  | Inv _, Pred _ | Pred _, Inv _ -> False

let disjoint_istore (is0 is1:istore) =
  level_istore is0 == level_istore is1 /\
  (forall a. istore_val_compat (read_istore is0 a) (read_istore is1 a))

let disjoint_istore_read is0 is1 a :
    Lemma (requires disjoint_istore is0 is1)
      (ensures istore_val_compat (read_istore is0 a) (read_istore is1 a))
      [SMTPatOr [
        [SMTPat (disjoint_istore is0 is1); SMTPat (read_istore is0 a)];
        [SMTPat (disjoint_istore is0 is1); SMTPat (read_istore is1 a)];
      ]] =
  ()

let mk_istore n (is: address -> istore_val) : istore =
  let f' = F.on_dom address is in
  down (n, f')

let level_mk_istore n is : Lemma (level_istore (mk_istore n is) == n) [SMTPat (level_istore (mk_istore n is))] =
  let f' = F.on_dom address is in
  assert_norm (mk_istore n is == down (n, f'));
  up_down #_ #functor_heap n f'

let read_mk_istore n is a :
    Lemma (read_istore (mk_istore n is) a == map_istore_val (approx n) (is a))
      [SMTPat (read_istore (mk_istore n is) a)] =
  let is' = F.on_dom address is in
  assert_norm (mk_istore n is == down (n, is'));
  up_down #_ #functor_heap n is';
  assert_norm (fmap (approx n) is' a == map_istore_val (approx n) (is' a))

let empty_istore n : istore = mk_istore n fun _ -> None
let empty n : world = (empty_istore n, ({ pulse_heap = pulse_heap_sig.sep.empty; saved_credits = 0 } <: rest))

let age_to_empty (m n: nat) : Lemma (age_to (empty n) m == empty m) [SMTPat (age_to (empty n) m)] =
  world_ext (age_to (empty n) m) (empty m) fun a -> read_age_to_ (empty n) m a

let emp : slprop =
  F.on_dom preworld #(fun _ -> prop) fun w -> True

let pure p : slprop = F.on_dom _ fun w -> p

let join_istore (is0:istore) (is1:istore { disjoint_istore is0 is1 }) : istore =
  mk_istore (level_istore is0) fun a ->
    match read_istore is0 a, read_istore is1 a with
    | None, None -> None
    | Pred p, _ | _, Pred p -> Pred p
    | Inv p, _ | _, Inv p -> Inv p

let read_join_istore (is0:istore) (is1:istore { disjoint_istore is0 is1 }) a :
  Lemma (read_istore (join_istore is0 is1) a ==
    (match read_istore is0 a, read_istore is1 a with
    | None, None -> None
    | Pred p, _ | _, Pred p -> Pred (approx (level_istore is0) p)
    | Inv p, _ | _, Inv p -> Inv (approx (level_istore is0) p))) =
  ()

let join_istore_commutative (is0:istore) (is1:istore { disjoint_istore is0 is1 }) :
    Lemma (join_istore is0 is1 == join_istore is1 is0) =
  istore_ext (join_istore is0 is1) (join_istore is1 is0) fun a -> ()

let approx_read_istore (is: istore) a :
    Lemma (map_istore_val (approx (level_istore is)) (read_istore is a) == read_istore is a)
    [SMTPat (read_istore is a)] =
  let n, i = up is in down_up is; up_down n i

let join_istore_refl (is: istore) : Lemma (disjoint_istore is is /\ join_istore is is == is) =
  istore_ext (join_istore is is) is fun a -> ()

let join_istore_associative
    (is0:istore)
    (is1:istore)
    (is2:istore { 
      disjoint_istore is1 is2 /\
      disjoint_istore is0 (join_istore is1 is2)
    })
: Lemma (
    disjoint_istore is0 is1 /\
    disjoint_istore (join_istore is0 is1) is2 /\
    join_istore is0 (join_istore is1 is2) ==
    join_istore (join_istore is0 is1) is2
  )
=
  istore_ext (join_istore is0 (join_istore is1 is2)) (join_istore (join_istore is0 is1) is2) fun a -> ()

let istore_le_iff (is1 is2: istore) :
    Lemma (istore_le is1 is2 <==> exists is3. join_istore is1 is3 == is2) =
  introduce istore_le is1 is2 ==> exists is3. join_istore is1 is3 == is2 with _.
    istore_ext (join_istore is1 is2) is2 fun _ -> ()

let disjoint_worlds (w0 w1:preworld)
: prop 
= disjoint_istore w0._1 w1._1 /\
  pulse_heap_sig.sep.disjoint w0._2.pulse_heap w1._2.pulse_heap

let disjoint_world_sym (w0 w1:preworld)
: Lemma 
  (ensures disjoint_worlds w0 w1 <==> disjoint_worlds w1 w0)
= pulse_heap_sig.sep.disjoint_sym w0._2.pulse_heap w1._2.pulse_heap

let join_worlds (w0:preworld) (w1:preworld { disjoint_worlds w0 w1 })
: preworld
= (join_istore w0._1 w1._1, ({
    pulse_heap = pulse_heap_sig.sep.join w0._2.pulse_heap w1._2.pulse_heap;
    saved_credits = w0._2.saved_credits + w1._2.saved_credits } <: rest))

open FStar.IndefiniteDescription { indefinite_description_ghost, strong_excluded_middle }

let world_le_iff (w1 w2: preworld) :
    Lemma (world_le w1 w2 <==> exists w3. join_worlds w1 w3 == w2) =
  istore_le_iff (fst w1) (fst w2);
  introduce world_le w1 w2 ==> exists w3. join_worlds w1 w3 == w2 with _. (
    assert pulse_heap_le (snd w1).pulse_heap (snd w2).pulse_heap;
    let ph3 = indefinite_description_ghost _ fun ph3 ->
      (snd w2).pulse_heap == pulse_heap_sig.sep.join (snd w1).pulse_heap ph3 in
    let is3 = indefinite_description_ghost _ fun is3 ->
      fst w2 == join_istore (fst w1) is3 in
    let sc3: nat = (snd w2).saved_credits - (snd w1).saved_credits in
    let w3: preworld = (is3, ({ pulse_heap = ph3; saved_credits = sc3 } <: rest)) in
    assert join_worlds w1 w3 == w2
  )

let join_worlds_commutative (w0:preworld) (w1:preworld { disjoint_worlds w0 w1 })
: Lemma (disjoint_worlds w1 w0 /\ join_worlds w0 w1 == join_worlds w1 w0)
= disjoint_world_sym w0 w1;
  join_istore_commutative w0._1 w1._1;
  pulse_heap_sig.sep.join_commutative w0._2.pulse_heap w1._2.pulse_heap

let join_worlds_associative
    (w0:preworld)
    (w1:preworld)
    (w2:preworld { disjoint_worlds w1 w2 /\ disjoint_worlds w0 (join_worlds w1 w2) })
: Lemma (
    disjoint_worlds w0 w1 /\
    disjoint_worlds (join_worlds w0 w1) w2 /\
    join_worlds w0 (join_worlds w1 w2) ==
    join_worlds (join_worlds w0 w1) w2
  )
= join_istore_associative w0._1 w1._1 w2._1;
  pulse_heap_sig.sep.join_associative w0._2.pulse_heap w1._2.pulse_heap w2._2.pulse_heap

let age_to_disjoint_worlds (w1 w2: preworld) n :
    Lemma (requires disjoint_worlds w1 w2)
      (ensures disjoint_worlds (age_to_ w1 n) (age_to_ w2 n)) =
  ()

let age_to_istore_join (i1 i2: istore) n :
    Lemma (requires disjoint_istore i1 i2)
      (ensures disjoint_istore (age_istore_to i1 n) (age_istore_to i2 n) /\
        age_istore_to (join_istore i1 i2) n == join_istore (age_istore_to i1 n) (age_istore_to i2 n))
    [SMTPat (age_istore_to (join_istore i1 i2) n)] =
  istore_ext (age_istore_to (join_istore i1 i2) n) (join_istore (age_istore_to i1 n) (age_istore_to i2 n)) fun a -> ()

let age_to_join (w1 w2: preworld) n :
    Lemma (requires disjoint_worlds w1 w2)
      (ensures disjoint_worlds (age_to_ w1 n) (age_to_ w2 n) /\
        age_to_ (join_worlds w1 w2) n == join_worlds (age_to_ w1 n) (age_to_ w2 n))
    [SMTPat (age_to_ (join_worlds w1 w2) n)] =
  ()

let star_ (p1 p2: world_pred) : world_pred =
  F.on_dom preworld #(fun _ -> prop)
    fun w -> (exists w1 w2.
      disjoint_worlds w1 w2 /\ w == join_worlds w1 w2 /\ p1 w1 /\ p2 w2)

[@@"opaque_to_smt"] irreducible
let indefinite_description_ghost2 (a b: Type) (p: (a -> b -> prop) { exists x y. p x y })
  : GTot (x: (a&b) { p x._1 x._2 }) =
  let x = indefinite_description_ghost a fun x -> exists y. p x y in
  let y = indefinite_description_ghost b fun y -> p x y in
  (x, y)

let star__commutative (p1 p2:world_pred)
: Lemma (p1 `star_` p2 == p2 `star_` p1)
= FStar.Classical.forall_intro_2 disjoint_world_sym;
  FStar.Classical.forall_intro_2 join_worlds_commutative;
  world_pred_ext (p1 `star_` p2) (p2 `star_` p1) fun w -> ()

let star__assoc (x y z:world_pred)
: Lemma (star_ x (star_ y z) == star_ (star_ x y) z)
=
  introduce forall x y z w. star_ x (star_ y z) w ==> star_ (star_ x y) z w with introduce _ ==> _ with _. (
    let (w1, w23) = indefinite_description_ghost2 _ _ fun w1 w23 ->
      disjoint_worlds w1 w23 /\ w == join_worlds w1 w23 /\ x w1 /\ star_ y z w23 in
    let (w2, w3) = indefinite_description_ghost2 _ _ fun w2 w3 ->
      disjoint_worlds w2 w3 /\ w23 == join_worlds w2 w3 /\ y w2 /\ z w3 in
    join_worlds_associative w1 w2 w3;
    let w12 = join_worlds w1 w2 in
    assert star_ x y w12;
    let w' = join_worlds w12 w3 in
    assert star_ (star_ x y) z w';
    assert w == w'
  );
  world_pred_ext (star_ x (star_ y z)) (star_ (star_ x y) z) fun w ->
    star__commutative y z;
    star__commutative x y;
    star__commutative x (star_ y z);
    star__commutative (star_ x y) z;
    assert star_ x (star_ y z) == star_ (star_ z y) x;
    assert star_ (star_ x y) z == star_ z (star_ y x)

let star (p1 p2:slprop) : slprop =
  introduce forall a b. world_le a b /\ star_ p1 p2 a ==> star_ p1 p2 b with introduce _ ==> _ with _. (
    world_le_iff a b;
    let c = indefinite_description_ghost _ fun c -> b == join_worlds a c in
    let (a1, a2) = indefinite_description_ghost2 _ _ fun a1 a2 ->
      disjoint_worlds a1 a2 /\ a == join_worlds a1 a2 /\ p1 a1 /\ p2 a2 in
    assert b == join_worlds (join_worlds a1 a2) c;
    join_worlds_commutative (join_worlds a1 a2) c; 
    assert b == join_worlds c (join_worlds a1 a2);
    join_worlds_associative c a1 a2; 
    assert b == join_worlds (join_worlds c a1) a2;
    join_worlds_commutative c a1;
    assert b == join_worlds (join_worlds a1 c) a2;
    world_le_iff a1 (join_worlds a1 c);
    assert world_le a1 (join_worlds a1 c);
    assert p1 (join_worlds a1 c)
  );
  star_ p1 p2

let star_commutative (p1 p2:slprop)
: Lemma (p1 `star` p2 == p2 `star` p1)
= star__commutative p1 p2

let star_assoc (x y z:slprop)
: Lemma (star x (star y z) == star (star x y) z)
= star__assoc x y z

let disjoint_istore_empty is : squash (disjoint_istore (empty_istore (level_istore is)) is) = ()

let join_istore_empty is : squash (join_istore (empty_istore (level_istore is)) is == is) =
  istore_ext (join_istore (empty_istore (level_istore is)) is) is fun a -> ()

let disjoint_empty w : squash (disjoint_worlds w (empty (level_ w)) /\ disjoint_worlds (empty (level_ w)) w) =
  pulse_heap_sig.sep.join_empty w._2.pulse_heap;
  disjoint_world_sym w (empty (level_ w))

let join_empty w : squash (disjoint_worlds (empty (level_ w)) w /\ join_worlds (empty (level_ w)) w == w) =
  disjoint_empty w;
  pulse_heap_sig.sep.join_empty w._2.pulse_heap;
  pulse_heap_sig.sep.join_commutative w._2.pulse_heap pulse_heap_sig.sep.empty;
  join_istore_empty w._1;
  world_ext (join_worlds (empty (level_ w)) w) w fun a -> ()

let star_emp (x: slprop) : squash (star x emp == x) =
  world_pred_ext (star x emp) x fun w ->
    introduce x w ==> star x emp w with _. (
      let w2 = empty (level_ w) in
      join_empty w;
      join_worlds_commutative w2 w
    );
    introduce star x emp w ==> x w with _. (
      let (w1, w2) = indefinite_description_ghost2 _ _ fun w1 w2 ->
        disjoint_worlds w1 w2 /\ w == join_worlds w1 w2 /\ x w1 /\ emp w2 in
      world_le_iff w1 w
    )

let (exists*) #a f =
  F.on_dom preworld #(fun _ -> prop) fun w ->
    exists (x:a). f x w

let sep_laws (_:unit) : squash (
  PulseCore.Semantics.(
    associative star /\
    commutative star /\
    is_unit emp star
  )
) =
  let open PulseCore.Semantics in
  introduce forall x y. star x y == star y x with star_commutative x y; assert commutative star;
  introduce forall x y z. star (star x y) z == star x (star y z) with star_assoc x y z; assert associative star;
  introduce forall x. star x emp == x with star_emp x; assert is_unit emp star

let lift (p: PM.slprop) : slprop =
  F.on_dom preworld fun w -> pulse_heap_sig.interp p ((snd w).pulse_heap)

let lift_emp_eq () =
  world_pred_ext (lift PM.emp) emp fun w ->
    pulse_heap_sig.intro_emp (snd w).pulse_heap

let lift_pure_eq p =
  world_pred_ext (lift (PM.pure p)) (pure p) fun w ->
    pulse_heap_sig.pure_interp p (snd w).pulse_heap

// let lift_later_eq #_ = admit ()

let lift_star_eq p q =
  world_pred_ext (lift (PM.star p q)) (star (lift p) (lift q)) fun w ->
    pulse_heap_sig.star_equiv p q (snd w).pulse_heap;
    admit ()

let lift_exists_eq a f =
  world_pred_ext (lift (PM.h_exists f)) (exists* x. lift (f x)) fun w ->
    let f' : a -> GTot pulse_heap_sig.slprop = fun x -> f x in
    HS.interp_exists f';
    let m = (snd w).pulse_heap in
    assert pulse_heap_sig.interp (HS.exists_ f') m <==>
      (exists x. pulse_heap_sig.interp (f x) m);
    admit ()

let later (p: slprop) : slprop =
  introduce forall (w: preworld) (n: nat).
      n < level_ w /\ p (age1_ w) ==>
      p (age1_ (age_to_ w n)) with introduce _ ==> _ with _. (
    let n' = if n > 0 then n-1 else 0 in
    assert age_to_ (age1_ w) n' == age_to_ w n'
  );
  introduce forall a b. world_le a b /\ p (age1_ a) ==> p (age1_ b) with (
    world_le_iff a b;
    world_le_iff (age1_ a) (age1_ b)
  );
  F.on_dom preworld fun w -> p (age1_ w)

let timeless (p: slprop) = later p == p

let timeless_lift (p: PM.slprop) : squash (timeless (lift p)) =
  world_pred_ext (later (lift p)) (lift p) fun w -> ()

let timeless_pure (p: prop) : squash (timeless (pure p)) =
  world_pred_ext (later (pure p)) (pure p) fun w -> ()

let later_credit n : slprop =
  F.on_dom preworld #(fun _ -> prop) fun w -> (snd w).saved_credits >= n

let timeless_later_credit n : squash (timeless (later_credit n)) =
  world_pred_ext (later (later_credit n)) (later_credit n) fun w -> ()

let equiv p q : slprop =
  F.on_dom preworld #(fun _ -> prop) fun w -> eq_at (level_ w + 1) p q

let eq_at_elim n (p q: world_pred) (w: preworld) :
    Lemma (requires eq_at n p q /\ level_ w < n) (ensures p w <==> q w) =
  assert approx n p w == approx n q w

let later_emp () : squash (later emp == emp) =
  world_pred_ext (later emp) emp fun w -> ()

let rejuvenate1_istore (is: istore) (is': istore { istore_le is' (age1_istore is) }) :
    is'':istore { age1_istore is'' == is' /\ istore_le is'' is } =
  let is'' = mk_istore (level_istore is) fun a -> if None? (read_istore is' a) then None else read_istore is a in
  istore_ext (age1_istore is'') is' (fun a -> ());
  is''

let rejuvenate1_istore_sep (is is1': istore) (is2': istore { disjoint_istore is1' is2' /\ age1_istore is == join_istore is1' is2' }) :
    is'':(istore&istore) { age1_istore is''._1 == is1' /\ age1_istore is''._2 == is2'
      /\ disjoint_istore is''._1 is''._2 /\ is == join_istore is''._1 is''._2 } =
  let is1'' = rejuvenate1_istore is is1' in
  join_istore_commutative is1' is2';
  let is2'' = rejuvenate1_istore is is2' in
  assert disjoint_istore is1'' is2'';
  istore_ext is (join_istore is1'' is2'') (fun a -> ());
  (is1'', is2'')

let rejuvenate1 (w: preworld) (w': preworld { world_le w' (age1_ w) }) :
    w'':preworld { age1_ w'' == w' /\ world_le w'' w /\ snd w'' == snd w' } =
  (rejuvenate1_istore (fst w) (fst w'), snd w')

let rejuvenate1_sep (w w1': preworld) (w2': preworld { disjoint_worlds w1' w2' /\ age1_ w == join_worlds w1' w2' }) :
    w'':(preworld&preworld) { age1_ w''._1 == w1' /\ age1_ w''._2 == w2'
      /\ disjoint_worlds w''._1 w''._2 /\ w == join_worlds w''._1 w''._2 } =
  let (is1'', is2'') = rejuvenate1_istore_sep (fst w) (fst w1') (fst w2') in
  ((is1'', snd w1'), (is2'', snd w2'))

let later_star (p q: slprop) : squash (later (star p q) == star (later p) (later q)) =
  world_pred_ext (later (star p q)) (star (later p) (later q)) fun w ->
    introduce star p q (age1_ w) ==> star (later p) (later q) w with _. (
      let (w1', w2') = indefinite_description_ghost2 _ _ fun w1' w2' ->
        disjoint_worlds w1' w2' /\ age1_ w == join_worlds w1' w2' /\ p w1' /\ q w2' in
      let (w1, w2) = rejuvenate1_sep w w1' w2' in
      assert later p w1;
      assert later q w2
    )

let iref = address

let inv (i:iref) (p:slprop) : slprop =
  F.on_dom preworld #(fun _ -> prop) fun w ->
    exists p'.
      read w i == Inv p' /\
      eq_at (level_ w) p p'

module GS = FStar.GhostSet

let inames = GS.set iref
let inames_dec_eq : GS.decide_eq address = fun x y -> reveal x = reveal y
let single (i:iref) : inames = GS.singleton inames_dec_eq i
let add_inv (e:inames) (i:iref) : inames = GS.union (single i) e

let iname_ok (i: iref) (is: istore) =
  Inv? (read_istore is i)

let read_inv (i: iref) (is: okay_istore { iname_ok i is }) : slprop =
  let Inv p = read_istore is i in p

let read_inv_equiv i (w: world { level_ w > 0 }) (p: slprop) :
    Lemma (requires inv i p w)
      (ensures eq_at (level_ w) (read_inv i (fst w)) p) =
  ()

let inames_ok (e: inames) (is: istore) : prop =
  forall a. GS.mem a e ==> iname_ok a is

let istore_dom (is: istore) : inames =
  GS.comprehend fun a -> Inv? (read_istore is a)

let rec istore_invariant_ (ex: inames) (is: okay_istore) (f: address) : slprop =
  if reveal f = 0 then
    emp
  else
    let f': address = f - 1 in
    if GS.mem f' ex then
      istore_invariant_ ex is f'
    else
      match read_istore is f' with
      | Inv p -> later p `star` istore_invariant_ ex is f'
      | _ -> istore_invariant_ ex is f'

[@@"opaque_to_smt"] irreducible let some_fresh_addr (is: okay_istore) : a:address { fresh_addr is a } =
  indefinite_description_ghost address fun a -> fresh_addr is a

let istore_invariant (ex: inames) (is: okay_istore) : slprop =
  istore_invariant_ ex is (some_fresh_addr is)

// ----------------

// inv i p  @ w_n  // eq_at n p p'

// i -> Some p' /\ eq_at (n - 1) p p'   @ (agew1 w_n)

// p' (age1 w_n) ///because w_n is an iworld

// have p (age1 w_n) because level (age1 w_n) = n - 1

