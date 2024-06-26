(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module PulseCore.MemoryAlt
open FStar.Ghost
open FStar.PCM
module PST = PulseCore.HoareStateMonad
module U = FStar.Universe
module S = FStar.Set
module CM = FStar.Algebra.CommMonoid
module H = PulseCore.HeapSig
module E = PulseCore.HeapExtension
module B = PulseCore.BaseHeapSig
/// This module adds memory invariants to the heap to expose the
/// final interface for Pulse's PCM-based memory model.

(**** Basic memory properties *)
let small_sig : H.heap_sig u#(a + 1) = E.extend (B.base_heap u#a)
let sig : H.heap_sig u#(a + 2) = E.extend small_sig
(** Abstract type of memories *)
let mem  : Type u#(a + 3) = sig.mem

let is_ghost_action (m0 m1:mem u#a) : prop = sig.is_ghost_action m0 m1

let ghost_action_preorder (_:unit)
: Lemma (FStar.Preorder.preorder_rel is_ghost_action)
= sig.is_ghost_action_preorder ()
 
(**** Separation logic *)

(** The type of separation logic propositions. Based on Steel.Heap.slprop *)
let slprop : Type u#(a + 3) = erased sig.slprop
let reveal_slprop (p:slprop) : sig.slprop = sig.non_info_slprop p
let big_slprop : Type u#(a + 2) = erased sig.bprop
let cm_big_slprop : CM.cm big_slprop = H.cm_e_slprop small_sig
let down (s:slprop u#a) : big_slprop u#a = sig.down s
let up (s:big_slprop u#a) : slprop u#a = reveal_slprop <| sig.up s
let up_big_is_big_alt (b:big_slprop)
: Lemma (is_big (up b))
        [SMTPat (is_big (up b))]
= sig.up_down b
let up_big_is_big (b:big_slprop) : Lemma (is_big (up b)) = ()

let small_slprop : Type u#(a + 1) = erased small_sig.bprop
let cm_small_slprop : CM.cm small_slprop = H.cm_e_slprop B.base_heap
let down2 (s:slprop u#a) : small_slprop u#a = small_sig.down (sig.down s)
let up2 (s:small_slprop u#a) : slprop u#a = reveal_slprop <| sig.up (small_sig.up s)
let small_is_also_big (s:slprop)
: Lemma (is_small s ==> is_big s)
= sig.up_down (small_sig.up (small_sig.down (down s)))

let up2_small_is_small_alt (s:small_slprop)
: Lemma (ensures is_small (up2 s))
        [SMTPat (is_small (up2 s))]
= calc (==) {
    up2 (down2 (up2 s));
  (==) {}
    up2 (down2 (sig.up (small_sig.up s)));
  (==) {}
    up2 (small_sig.down (sig.down (sig.up (small_sig.up s))));
  (==) { sig.up_down (small_sig.up s) }
    up2 (small_sig.down (small_sig.up s));
  (==) { small_sig.up_down s }
    up2 s;
  }
let up2_small_is_small s = up2_small_is_small_alt s
(** Interpreting mem assertions as memory predicates *)
let interp (p:slprop u#a) (m:mem u#a) : prop = H.interpret p m

let equiv (p1 p2:slprop u#a) : prop = p1 == p2

(**
  An extensional equivalence principle for slprop
 *)

let slprop_extensionality (p q:slprop u#a)
: Lemma
    (requires p `equiv` q)
    (ensures p == q)
= ()

let slprop_equiv_refl (p:slprop)
: Lemma (p `equiv` p)
        [SMTPat (equiv p p)]
= ()
          
(** A memory maps a [ref]erence to its associated value *)
let core_ref : Type u#0 = PulseCore.Heap2.core_ref

(** [null] is a specific reference, that is not associated to any value
*)
let core_ref_null : core_ref = PulseCore.Heap2.core_ref_null

let core_ref_is_null (r:core_ref)
: b:bool { b <==> r == core_ref_null }
= PulseCore.Heap2.core_ref_is_null r


let emp_is_small () 
: Lemma (is_small sig.emp)
= E.up_emp B.base_heap;
  E.up_emp small_sig;
  small_sig.up_down B.base_heap.emp;
  sig.up_down small_sig.emp

let pure_is_small (p:prop) 
: Lemma (is_small (sig.pure p))
= E.up_pure B.base_heap p;
  E.up_pure small_sig p;
  small_sig.up_down (B.base_heap.pure p);
  sig.up_down (small_sig.pure p)

let emp
: vprop u#a
= emp_is_small(); sig.emp

let pure (p:prop)
: vprop u#a
= pure_is_small p; sig.pure p

let star  (p1 p2:slprop u#a)
: slprop u#a
= sig.star p1 p2

module F = FStar.FunctionalExtensionality
let h_exists (#a:Type u#b) (f: (a -> slprop u#a))
: slprop u#a
= H.exists_ #sig #a (fun x -> reveal_slprop (f x))

(***** Properties of separation logic equivalence *)
let emp_unit (p:slprop)
: Lemma (p `equiv` (p `star` emp))
= sig.emp_unit p

let pure_equiv (p q:prop)
: Lemma ((p <==> q) ==> (pure p `equiv` pure q))
= FStar.PropositionalExtensionality.apply p q

let pure_true_emp (_:unit)
: Lemma (pure True `equiv` emp)
= sig.pure_true_emp ()

(***** Properties of the separating conjunction *)
let star_commutative (p1 p2:slprop)
: Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))
= sig.star_commutative p1 p2

let star_associative (p1 p2 p3:slprop)
: Lemma ((p1 `star` (p2 `star` p3))
          `equiv`
          ((p1 `star` p2) `star` p3))
= sig.star_associative p1 p2 p3

let star_congruence (p1 p2 p3 p4:slprop)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv` p4)
          (ensures (p1 `star` p2) `equiv` (p3 `star` p4))
= ()

let big_star_congruence (p1 p2:big_vprop u#a)
: Lemma (is_big (p1 `star` p2))
= sig.star_congruence p1 p2

module T = FStar.Tactics.V2
let big_exists_congruence (#a:Type u#a) (p:a -> slprop u#b)
: Lemma
  (requires forall x. is_big (p x))
  (ensures is_big (h_exists p))
= introduce forall x. is_big (reveal_slprop (p x))
  with (  
    assert (is_big (p x))  
  );
  assert (H.is_boxable (H.exists_ #sig #a (fun x -> reveal_slprop (p x))))
    by (T.mapply (`E.exists_congruence))

let small_star_congruence (p1 p2:vprop u#a)
: Lemma (is_small (p1 `star` p2))
= small_is_also_big p1;
  small_is_also_big p2;
  calc (==) {
    reveal_slprop <| up2 (down2 (p1 `star` p2));
  (==) {}
    sig.up (small_sig.up (small_sig.down (sig.down (p1 `star` p2))));
  (==) { E.down_star p1 p2 }
    sig.up (small_sig.up (small_sig.down (down p1 `small_sig.star` down p2)));
  (==) { E.down_star #B.base_heap (down p1) (down p2) }
    sig.up (small_sig.up (down2 p1 `B.base_heap.star` down2 p2));
  (==) { E.up_star #B.base_heap (down2 p1) (down2 p2) }
    sig.up (small_sig.up (down2 p1) `small_sig.star` (small_sig.up (down2 p2)));
  (==) { E.up_star #small_sig (small_sig.up (down2 p1)) (small_sig.up (down2 p2)) }
    reveal_slprop (p1 `star` p2);
  }

let reveal_bprop (x:big_slprop) : small_sig.slprop = small_sig.non_info_slprop x

let down_exists_alt #a (p: a -> slprop)
: Lemma 
  (ensures down (h_exists p) ==
           hide <| H.exists_ #small_sig (fun x -> small_sig.non_info_slprop <| down (p x)))
= calc (==) {
    reveal_bprop (down (h_exists p));
  (==) {}
    sig.down (H.exists_ (fun x -> reveal_slprop (p x)));
  (==) { _ by (T.mapply (`E.down_exists)) }
    H.exists_ #small_sig (fun x -> sig.down (reveal_slprop (p x)));
  (==) { H.exists_extensionality #small_sig
          (fun x -> sig.down (reveal_slprop (p x)))
          (fun x -> small_sig.non_info_slprop <| down (p x)) }
    H.exists_ #small_sig (fun x -> small_sig.non_info_slprop <| down (p x));
  } 


let split_small (p:slprop u#a)
: Lemma (requires is_small p)
        (ensures H.is_boxable #small_sig (small_sig.non_info_slprop (down p)))
= small_is_also_big p;
  calc (==) {
   hide <| small_sig.up (small_sig.down (down p));
  (==) {  sig.up_down (small_sig.up (small_sig.down (down p))) }
   down (up (small_sig.up (small_sig.down (down p))));
  (==) { }
   down (up2 (down2 p));
  (==) {}
   down p;
  }

let small_exists_congruence (#a:Type u#a) (p:a -> slprop u#b)
: Lemma
  (requires forall x. is_small (p x))
  (ensures is_small (h_exists p))
= FStar.Classical.forall_intro small_is_also_big;
  big_exists_congruence #a p;
  assert (is_big (h_exists p));
  down_exists_alt #a p;
  assert (forall x. H.is_boxable #small_sig (small_sig.non_info_slprop (down (p x))))
      by (let _ = T.forall_intro () in
          T.mapply (`split_small));
  assert (H.is_boxable #small_sig
           (H.exists_ #small_sig (fun x -> small_sig.non_info_slprop <| down (p x))))
     by (T.mapply (`E.exists_congruence))
     
let h_exists_equiv (#a:Type) (p q : a -> slprop)
: Lemma
    (requires (forall x. p x `equiv` q x))
    (ensures (h_exists p == h_exists q))
= calc (==) {
    reveal_slprop <| h_exists p;
  (==) {}
    H.exists_ #sig #a (fun x -> reveal_slprop (p x));
  // (==) { _ by (T.mapply (`H.exists_extensionality)) } //this fails
  (==) { H.exists_extensionality #sig #a (fun x -> reveal_slprop (p x)) (fun x -> reveal_slprop (q x)) }
    H.exists_ #sig #a (fun x -> reveal_slprop (q x));
  (==) {}
    reveal_slprop <| h_exists q;
  }

let up_emp_big ()
: Lemma (up cm_big_slprop.unit == emp)
= E.up_emp small_sig

let down_emp_big ()
: Lemma (down emp == cm_big_slprop.unit)
= E.down_emp small_sig

let up_star_big (p q:big_slprop)
: Lemma (up (p `cm_big_slprop.mult` q) == up p `star` up q)
= E.up_star #small_sig p q

let down_star_big (p q:big_vprop)
: Lemma (down (p `star` q) == down p `cm_big_slprop.mult` down q)
= E.down_star #small_sig p q

let up2_emp ()
: Lemma (up2 cm_small_slprop.unit == emp)
= E.up_emp B.base_heap;
  E.up_emp small_sig

let down2_emp ()
: Lemma (down2 emp == cm_small_slprop.unit)
= E.down_emp B.base_heap;
  E.down_emp small_sig

let up2_star (p q:small_slprop)
: Lemma (up2 (p `cm_small_slprop.mult` q) == up2 p `star` up2 q)
= calc (==) {
    reveal_slprop <| up2 (p `cm_small_slprop.mult` q);
  (==) {}
    sig.up (small_sig.up (p `B.base_heap.star` q));
  (==) { E.up_star #B.base_heap p q }
    sig.up (small_sig.up p `small_sig.star` small_sig.up q);
  (==) { E.up_star #small_sig (small_sig.up p) (small_sig.up q) }
    reveal_slprop <| up2 p `star` up2 q;
  }

let reveal_sprop (b:small_slprop) : B.base_heap.slprop = B.base_heap.non_info_slprop b
let down2_star (p q:vprop)
: Lemma (down2 (p `star` q) == down2 p `cm_small_slprop.mult` down2 q)
= calc (==) {
    reveal_sprop <| down2 (p `star` q);
  (==) {}
    small_sig.down (sig.down (p `star` q));
  (==) { E.down_star #small_sig p q }
    small_sig.down ((down p) `small_sig.star` (down q));
  (==) { E.down_star #B.base_heap (down p) (down q) }
    reveal_sprop <| down2 p `B.base_heap.star` down2 q;
  }

(**** Memory invariants *)

(** Invariants have a name *)
let iname : eqtype = sig.iname
let inames_ok (e:inames) (m:mem) : prop = H.inames_ok e m

(** The empty set of invariants is always empty *)
let inames_ok_empty (m:mem)
: Lemma (ensures inames_ok Set.empty m)
          [SMTPat (inames_ok Set.empty m)]
= ()

(**
  This separation logic proposition asserts that all the invariants whose names are in [e]
  are in effect and satisfied on the heap inside the memory [m]
*)
let mem_invariant (e:inames) (m:mem u#a)
: slprop u#a
= sig.mem_invariant e m

let full_mem_pred: mem -> prop = sig.full_mem_pred 

let iref : Type0 = erased (E.iiref small_sig)
let reveal_iref (i:iref) : sig.iref = 
  let x : erased (sig.iref) = hide (reveal i) in
  sig.non_info_iref x
let iname_of (i:iref) : GTot iname = sig.iname_of i

let inv (i:iref) (p:slprop u#a) : slprop u#a = sig.inv (reveal_iref i) p

let coerce_action
    (#a:Type u#x)
    (#mg:bool)
    (#ex:inames)
    (#pre:sig.slprop)
    (#post:a -> GTot (sig.slprop))
    (#pre':slprop u#a)
    (#post':a -> slprop u#a)
    (_:squash (pre == reveal pre' /\ (forall x. post x == reveal (post' x))))
    ($act:H._action_except (sig u#a) a mg ex pre post)
: _pst_action_except a mg ex pre' post'
= fun frame m0 -> act (reveal_slprop frame) m0 

let coerce_action_back
    (#a:Type u#x)
    (#mg:bool)
    (#ex:inames)
    (#pre':slprop u#a)
    (#post':a -> slprop u#a)
    (pre:sig.slprop)
    (post:a -> GTot (sig.slprop))
    (_:squash (pre == reveal pre' /\ (forall x. post x == reveal (post' x))))
    ($act:_pst_action_except a mg ex pre' post')
: H._action_except (sig u#a) a mg ex pre post
= fun frame m0 -> act frame m0 

let dup_inv (e:inames) (i:iref) (p:slprop u#a)
: pst_ghost_action_except unit e 
    (inv i p) 
    (fun _ -> inv i p `star` inv i p)
= coerce_action () <| E.dup_inv #(small_sig u#a) e (reveal_iref i) (reveal_slprop p)

let new_invariant (e:inames) (p:slprop { is_big p })
: pst_ghost_action_except iref e
    p
    (fun i -> inv i p)
= fun frame m0 -> 
    let i, m1 = E.new_invariant #(small_sig u#a) e (reveal_slprop p) (reveal_slprop frame) m0 in
    hide i, m1

let with_invariant_alt
    (#h:H.heap_sig u#a)
    (#a:Type u#aa)
    (#fp:(E.extend h).slprop)
    (#fp':(a -> (E.extend h).slprop))
    (#opened_invariants:H.inames (E.extend h))
    (#p:(E.extend h).slprop)
    (#maybe_ghost:bool)
    (i:(E.extend h).iref{not (Set.mem ((E.extend h).iname_of i) opened_invariants)})
    ($f:H._action_except (E.extend h) a maybe_ghost
      (Set.add ((E.extend h).iname_of i) opened_invariants) 
      (p `(E.extend h).star` fp)
      (fun x -> p `(E.extend h).star` fp' x))
: H._action_except (E.extend h) a maybe_ghost opened_invariants 
      ((E.extend h).inv i p `(E.extend h).star` fp)
      (fun x -> (E.extend h).inv i p `(E.extend h).star` fp' x)
= E.with_invariant #h #a #fp #fp' #opened_invariants #p #maybe_ghost i f

let with_invariant (#a:Type u#x)
                   (#fp:slprop u#a)
                   (#fp':a -> slprop u#a)
                   (#opened_invariants:inames)
                   (#p:slprop u#a)
                   (#maybe_ghost:bool)
                   (i:iref{not (mem_inv opened_invariants i)})
                   (f:_pst_action_except a maybe_ghost
                        (add_inv opened_invariants i) 
                        (p `star` fp)
                        (fun x -> p `star` fp' x))
: _pst_action_except a maybe_ghost opened_invariants 
      (inv i p `star` fp)
      (fun x -> inv i p `star` fp' x)
= coerce_action () <|
  with_invariant_alt 
    #(small_sig u#a) #a
    #(reveal_slprop fp) 
    #(fun x -> reveal_slprop (fp' x)) 
    #opened_invariants #(reveal_slprop p) #maybe_ghost
    (reveal_iref i)
    (coerce_action_back _ (fun x -> p `star` reveal_slprop (fp' x)) () f)

let lift_action_alt
    (#h:H.heap_sig u#h)
    (#a:Type u#a)
    (#mg:bool)
    (#ex:H.inames (E.extend h))
    (#pre:erased h.slprop)
    (#post:a -> GTot h.slprop)
    (action:H._action_except h a mg (E.lower_inames ex) pre post)
: H._action_except (E.extend h)
    a mg ex 
    ((E.extend h).up pre)
    (fun x -> (E.extend h).up (post x))
= E.lift_action_alt #h #a #mg #ex #(h.non_info_slprop pre) #post action

let distinct_invariants_have_distinct_names
      (e:inames)
      (p:slprop u#m)
      (q:slprop u#m { p =!= q })
      (i j: iref)
: pst_ghost_action_except u#0 u#m 
    (squash (iname_of i =!= iname_of j))
    e 
    (inv i p `star` inv j q)
    (fun _ -> inv i p `star` inv j q)
= coerce_action 
    #_ 
    #_
    #_
    #_
    #_
    #(inv i p `star` inv j q)
    #(fun _ -> inv i p `star` inv j q)
     () <|
  E.distinct_invariants_have_distinct_names #(small_sig u#m) e (reveal_slprop p) (reveal_slprop q) (reveal_iref i) (reveal_iref j)

let invariant_name_identifies_invariant_alt
      (e:inames)
      (p q:slprop u#m)
      (i:iref)
      (j:iref { iname_of i == iname_of j } )
: pst_ghost_action_except (squash (reveal_slprop p == reveal_slprop q /\ eq2 #(E.iiref small_sig) (reveal_iref i) (reveal_iref j))) e
   (inv i p `star` inv j q)
   (fun _ -> inv i p `star` inv j q)
= coerce_action 
    #(squash (reveal_slprop p == reveal_slprop q /\ reveal_iref i == reveal_iref j))
    #_
    #_
    #_
    #_
    #(inv i p `star` inv j q)
    #(fun _ -> inv i p `star` inv j q)
     () <|
  E.invariant_name_identifies_invariant #(small_sig u#m) e (reveal_slprop p) (reveal_slprop q) (reveal_iref i) (reveal_iref j)

let invariant_name_identifies_invariant
      (e:inames)
      (p q:slprop u#m)
      (i:iref)
      (j:iref { iname_of i == iname_of j } )
: pst_ghost_action_except (squash (p == q /\ i == j)) e
   (inv i p `star` inv j q)
   (fun _ -> inv i p `star` inv j q)
= fun frame m0 -> 
    let x, m1 = invariant_name_identifies_invariant_alt e p q i j frame m0 in
    (), m1

let rec coerce_ctx (ctx:erased (list iref))
: erased (list sig.iref)
= match reveal ctx with
  | [] -> []
  | hd::tl -> hide (reveal hd :: coerce_ctx tl)

let rec coerce_ctx_mem (ctx:erased (list iref))
: Lemma (forall (i:E.iiref small_sig). List.Tot.memP i (coerce_ctx ctx) <==> List.Tot.memP (hide i) ctx)
= match ctx with
  | [] -> ()
  | hd::tl -> 
    let _ = coerce_ctx_mem tl in
    ()

let fresh_invariant_alt (e:inames) (p:big_vprop u#m) (ctx:erased (list iref))
: pst_ghost_action_except (i:E.iiref small_sig { E.fresh_wrt (coerce_ctx ctx) i }) e
       p
       (fun i -> inv i p)
= coerce_action 
    #(i:E.iiref small_sig { E.fresh_wrt (coerce_ctx ctx) i})
    #_
    #_
    #(reveal_slprop p)
    #(fun i -> sig.inv i (reveal_slprop p))
    #p
    #(fun i -> inv i p)
  () <|
  E.fresh_invariant #(small_sig u#m) e (reveal_slprop p) (coerce_ctx ctx)

let fresh_invariant (e:inames) (p:big_vprop u#m) (ctx:erased (list iref))
: pst_ghost_action_except (i:iref { fresh_wrt ctx i }) e
       p
       (fun i -> inv i p)
= fun frame m0 -> 
    let x, m1 = fresh_invariant_alt e p ctx frame m0 in
    coerce_ctx_mem ctx;
    hide x, m1

(* Some generic actions and combinators *)

let pst_frame
      (#a:Type)
      (#maybe_ghost:bool)
      (#opened_invariants:inames)
      (#pre:slprop)
      (#post:a -> slprop)
      (frame:slprop)
      ($f:_pst_action_except a maybe_ghost opened_invariants pre post)
: _pst_action_except a maybe_ghost opened_invariants (pre `star` frame) (fun x -> post x `star` frame)
= coerce_action () <|
  HeapSig.frame #_ #_ #_ #_
      #(reveal_slprop pre)
      #(fun x -> post x)
      (reveal_slprop frame)
      (coerce_action_back _ _ () f)

let witness_h_exists (#opened_invariants:_) (#a:_) (p:a -> slprop)
: pst_ghost_action_except (erased a) opened_invariants
           (h_exists p)
           (fun x -> p x)
= calc (==) {
    reveal (h_exists p);
  (==) {}
    reveal (H.exists_ (fun x -> reveal_slprop (p x)));
  (==) { H.exists_extensionality (fun x -> reveal (p x)) (fun x -> reveal_slprop (p x)) }
    H.exists_ (fun x -> reveal (p x));
  };
  coerce_action () <|
  HeapSig.witness_exists #_ #_ #_ (fun x -> p x)


let intro_exists (#opened_invariants:_) (#a:_) (p:a -> slprop) (x:erased a)
: pst_ghost_action_except unit opened_invariants
      (p x)
      (fun _ -> h_exists p)
= coerce_action () <|
  HeapSig.intro_exists #_ #_ #_ (fun x -> reveal_slprop (p x)) x

let lift_h_exists (#opened_invariants:_) (#a:Type u#a) (p:a -> slprop u#m)
  : pst_ghost_action_except unit opened_invariants
           (h_exists p)
           (fun _a -> h_exists #(U.raise_t u#a u#b a) (U.lift_dom p))
 = calc (==) {
    reveal_slprop <| h_exists #(U.raise_t u#a u#b a) (U.lift_dom p);
  (==) { _ by (T.trefl()) }
    reveal_slprop <| hide <| HeapSig.exists_ #sig #(U.raise_t u#a u#b a) (fun x -> reveal_slprop (U.lift_dom p x));
  (==) {}
    HeapSig.exists_ #sig #(U.raise_t u#a u#b a) (fun x -> reveal_slprop (U.lift_dom p x));
  (==) { H.exists_extensionality #sig
            (fun x -> reveal_slprop (U.lift_dom p x))
            (HeapSig.lift_dom_ghost (fun x -> reveal_slprop (p x))) }
    HeapSig.exists_ #sig #(U.raise_t u#a u#b a) (HeapSig.lift_dom_ghost (fun x -> reveal_slprop (p x)));
   }; 
   coerce_action () <|
   HeapSig.lift_h_exists #_ #_ #_ (fun x -> reveal_slprop (p x))


let elim_pure (#opened_invariants:_) (p:prop)
: pst_ghost_action_except (u:unit{p}) opened_invariants (pure p) (fun _ -> emp)
= coerce_action () <|
  HeapSig.elim_pure #_ #_ p

let intro_pure (#opened_invariants:_) (p:prop) (x:squash p)
: pst_ghost_action_except unit opened_invariants emp (fun _ -> pure p)
= coerce_action () <|
  HeapSig.intro_pure #_ #_ p x
  
let drop (#opened_invariants:_) (p:slprop)
: pst_ghost_action_except unit opened_invariants p (fun _ -> emp)
= coerce_action () <|
  HeapSig.drop #_ #_ (reveal_slprop p)

let lift_ghost
      (#a:Type)
      #opened_invariants #p #q
      (ni_a:non_info a)
      (f:erased (pst_ghost_action_except a opened_invariants p q))
: pst_ghost_action_except a opened_invariants p q
= coerce_action () <|
  HeapSig.lift_ghost #_ #_ #_ #(reveal_slprop p) #(fun x -> q x) ni_a
    (coerce_action_back _ _ () f)

(* Concrete references to "small" types *)
let pts_to (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v:a) : vprop u#a
 = up2 (B.base_heap.pts_to #a #pcm r v)

let wrap (#h:H.heap_sig u#a) (p:erased h.slprop) : h.slprop = h.non_info_slprop p


// let coerce_action_alt
//     (#a:Type u#x)
//     (#mg:bool)
//     (#ex:inames)
//     (#pre:erased (slprop u#a))
//     (#post:a -> GTot (slprop u#a))
//     (#pre':erased (slprop u#a))
//     (#post':a -> GTot (slprop u#a))
//     (_:squash (pre == pre' /\ (forall x. post x == post' x)))
//     ($act:_pst_action_except a mg ex pre post)
// : _pst_action_except a mg ex pre' post'
// = act

(** Splitting a permission on a composite resource into two separate permissions *)
let split_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (e:inames)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit e 
     (pts_to r (v0 `op pcm` v1))
     (fun _ -> pts_to r v0 `star` pts_to r v1)
= up2_star (B.base_heap.pts_to #a #pcm r v0) (B.base_heap.pts_to #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (pts_to r (v0 `op pcm` v1))) () <|
  lift_action_alt #small_sig <|
  lift_action_alt #B.base_heap <|
  B.share #(E.lower_inames #(B.base_heap u#a) (E.lower_inames #(small_sig u#a) e)) #a #pcm r v0 v1
  

(** Combining separate permissions into a single composite permission*)
let gather_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (e:inames)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a)
: pst_ghost_action_except (squash (composable pcm v0 v1)) e
    (pts_to r v0 `star` pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))
= up2_star (B.base_heap.pts_to #a #pcm r v0) (B.base_heap.pts_to #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (pts_to r v0 `star` pts_to r v1)) () <|
  lift_action_alt #small_sig <|
  lift_action_alt #B.base_heap <|
  B.gather #(E.lower_inames #(B.base_heap u#a) (E.lower_inames #(small_sig u#a) e)) #a #pcm r v0 v1

let alloc_action (#a:Type u#a) (#pcm:pcm a) (e:inames) (x:a{pcm.refine x})
: pst_action_except (ref a pcm) e
    emp
    (fun r -> pts_to r x)
= up2_emp ();
  coerce_action #_ #_ #_ #(reveal_slprop emp) #(fun r -> up2 (B.base_heap.pts_to #a #pcm r x)) () <|
  lift_action_alt #small_sig <|
  lift_action_alt #B.base_heap <|
  B.extend #(E.lower_inames #(B.base_heap u#a) (E.lower_inames #(small_sig u#a) e)) #a #pcm x

let select_refine (#a:Type u#a) (#p:pcm a)
                  (e:inames)
                  (r:ref a p)
                  (x:erased a)
                  (f:(v:a{compatible p x v}
                      -> GTot (y:a{compatible p y v /\
                                  FStar.PCM.frame_compatible p x v y})))
: pst_action_except (v:a{compatible p x v /\ p.refine v}) e
    (pts_to r x)
    (fun v -> pts_to r (f v))
= coerce_action #(v:a{compatible p x v /\ p.refine v}) #_ #_ #(reveal_slprop (pts_to r x)) #(fun v -> up2 (B.base_heap.pts_to #a #p r (f v))) #(pts_to r x) #(fun v -> pts_to r (f v)) () <|
  lift_action_alt #small_sig <|
  lift_action_alt #B.base_heap <|
  B.read #(E.lower_inames #(B.base_heap u#a) (E.lower_inames #(small_sig u#a) e)) #a #p r x f

let upd_gen (#a:Type u#a) (#p:pcm a) (e:inames) (r:ref a p) (x y:Ghost.erased a)
            (f:FStar.PCM.frame_preserving_upd p x y)
: pst_action_except unit e
    (pts_to r x)
    (fun _ -> pts_to r y)
= coerce_action #_ #_ #_ #(reveal_slprop (pts_to r x)) () <|
  lift_action_alt #small_sig <|
  lift_action_alt #B.base_heap <|
  B.write #(E.lower_inames #(B.base_heap u#a) (E.lower_inames #(small_sig u#a) e)) #a #p r x y f

let pts_to_not_null_action 
      (#a:Type u#a) (#pcm:pcm a)
      (e:inames)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r))) e
    (pts_to r v)
    (fun _ -> pts_to r v)
= coerce_action #_ #_ #_ #(reveal_slprop (pts_to r v)) () <|
  lift_action_alt #small_sig <|
  lift_action_alt #B.base_heap <|
  B.pts_to_not_null_action #(E.lower_inames #(B.base_heap u#a) (E.lower_inames #(small_sig u#a) e)) #a #pcm r v 


(* Ghost references to "small" types *)
[@@erasable]
let core_ghost_ref : Type0 = H.core_ghost_ref
let ghost_pts_to (#a:Type u#a) (#p:pcm a) (r:ghost_ref p) (v:a)
: vprop u#a
= up2 (B.base_heap.ghost_pts_to false #a #p r v)

let ghost_alloc
    (#e:_)
    (#a:Type u#a)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: pst_ghost_action_except
    (ghost_ref pcm)
    e
    emp 
    (fun r -> ghost_pts_to r x)
= up2_emp ();
  coerce_action #_ #_ #_ #(reveal_slprop emp) #(fun r -> up2 (B.base_heap.ghost_pts_to false #a #pcm r x)) () <|
  lift_action_alt #small_sig <|
  lift_action_alt #B.base_heap <|
  B.ghost_extend false #(E.lower_inames #(B.base_heap u#a) (E.lower_inames #(small_sig u#a) e)) #a #pcm x

let ghost_read
    #e
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: pst_ghost_action_except
    (erased (v:a{compatible p x v /\ p.refine v}))
    e
    (ghost_pts_to r x)
    (fun v -> ghost_pts_to r (f v))
= coerce_action #(erased (v:a{compatible p x v /\ p.refine v})) #_ #_
                #(reveal_slprop (ghost_pts_to r x)) 
                #(fun v -> up2 (B.base_heap.ghost_pts_to false #a #p r (f v)))
                #(ghost_pts_to r x)
                #(fun v -> ghost_pts_to r (f v))
                () <|
  lift_action_alt #small_sig <|
  lift_action_alt #B.base_heap <|
  B.ghost_read #(E.lower_inames #(B.base_heap u#a) (E.lower_inames #(small_sig u#a) e)) #false #a #p r x f

let ghost_write
    #e
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_ghost_action_except unit e
    (ghost_pts_to r x)
    (fun _ -> ghost_pts_to r y)
= coerce_action #_ #_ #_ #(reveal_slprop (ghost_pts_to r x)) () <|
  lift_action_alt #small_sig <|
  lift_action_alt #B.base_heap <|
  B.ghost_write #(E.lower_inames #(B.base_heap u#a) (E.lower_inames #(small_sig u#a) e)) #false #a #p r x y f


let ghost_share
    #e
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit e
    (ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pts_to r v0 `star` ghost_pts_to r v1)
= up2_star (B.base_heap.ghost_pts_to false #a #pcm r v0) (B.base_heap.ghost_pts_to false #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (ghost_pts_to r (v0 `op pcm` v1))) () <|
  lift_action_alt #small_sig <|
  lift_action_alt #B.base_heap <|
  B.ghost_share #(E.lower_inames #(B.base_heap u#a) (E.lower_inames #(small_sig u#a) e)) #false #a #pcm r v0 v1


let ghost_gather
    #e
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: pst_ghost_action_except
    (squash (composable pcm v0 v1)) e
    (ghost_pts_to r v0 `star` ghost_pts_to r v1)
    (fun _ -> ghost_pts_to r (op pcm v0 v1))
= up2_star (B.base_heap.ghost_pts_to false #a #pcm r v0) (B.base_heap.ghost_pts_to false #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (ghost_pts_to r v0 `star` ghost_pts_to r v1)) () <|
  lift_action_alt #small_sig <|
  lift_action_alt #B.base_heap <|
  B.ghost_gather #(E.lower_inames #(B.base_heap u#a) (E.lower_inames #(small_sig u#a) e)) #false #a #pcm r v0 v1


(* Concrete references to "big" types *)
let big_pts_to (#a:Type u#(a + 1)) (#pcm:_) (r:ref a pcm) (v:a)
: big_vprop u#a
= up (small_sig.pts_to #a #pcm r v)

(** Splitting a permission on a composite resource into two separate permissions *)
let big_split_action
      (#a:Type u#(a + 1))
      (#pcm:pcm a)
      (e:inames)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit e
    (big_pts_to r (v0 `op pcm` v1))
    (fun _ -> big_pts_to r v0 `star` big_pts_to r v1)
= up_star_big (small_sig.pts_to #a #pcm r v0) (small_sig.pts_to #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (big_pts_to r (v0 `op pcm` v1))) () <|
  lift_action_alt #small_sig <|
  E.split_action #B.base_heap #_ #pcm (E.lower_inames #(small_sig u#a) e) r v0 v1

let big_gather_action
      (#a:Type u#(a + 1))
      (#pcm:pcm a)
      (e:inames)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:FStar.Ghost.erased a)
: pst_ghost_action_except (squash (composable pcm v0 v1)) e
    (big_pts_to r v0 `star` big_pts_to r v1)
    (fun _ -> big_pts_to r (op pcm v0 v1))
= up_star_big (small_sig.pts_to #a #pcm r v0) (small_sig.pts_to #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (big_pts_to r v0 `star` big_pts_to r v1)) () <|
  lift_action_alt #small_sig <|
  E.gather_action #B.base_heap #_ #pcm (E.lower_inames #(small_sig u#a) e) r v0 v1

let big_alloc_action
      (#a:Type u#(a + 1))
      (#pcm:pcm a)
      (e:inames)
      (x:a{pcm.refine x})
: pst_action_except (ref a pcm) e
    emp
    (fun r -> big_pts_to r x)
= up_emp_big ();
  coerce_action #_ #_ #_ #(reveal_slprop emp) #(fun r -> up (small_sig.pts_to #a #pcm r x)) () <|
  lift_action_alt #small_sig <|
  E.alloc_action #B.base_heap #_ #pcm (E.lower_inames #(small_sig u#a) e) x

let big_select_refine
      (#a:Type u#(a + 1))
      (#p:pcm a)
      (e:inames)
      (r:ref a p)
      (x:erased a)
      (f:(v:a{compatible p x v}
          -> GTot (y:a{compatible p y v /\
                      FStar.PCM.frame_compatible p x v y})))
: pst_action_except (v:a{compatible p x v /\ p.refine v}) e
    (big_pts_to r x)
    (fun v -> big_pts_to r (f v))
= coerce_action #(v:a{compatible p x v /\ p.refine v}) #_ #_
      #(reveal_slprop (big_pts_to r x))
      #(fun v -> up (small_sig.pts_to #a #p r (f v)))
      #(big_pts_to r x)
      #(fun v -> big_pts_to r (f v))
      () <|
  lift_action_alt #small_sig <|
  E.select_refine #B.base_heap #_ #p (E.lower_inames #(small_sig u#a) e) r x f

let big_upd_gen
    (#a:Type u#(a + 1))
    (#p:pcm a)
    (e:inames)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_action_except unit e
    (big_pts_to r x)
    (fun _ -> big_pts_to r y)
= coerce_action #_ #_ #_ #(reveal_slprop (big_pts_to r x)) () <|
  lift_action_alt #small_sig <|
  E.upd_gen #B.base_heap #_ #p (E.lower_inames #(small_sig u#a) e) r x y f

let big_pts_to_not_null_action 
      (#a:Type u#(a + 1))
      (#pcm:pcm a)
      (e:inames)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r))) e
    (big_pts_to r v)
    (fun _ -> big_pts_to r v)
= coerce_action #_ #_ #_ #(reveal_slprop (big_pts_to r v)) () <|
  lift_action_alt #small_sig <|
  E.pts_to_not_null_action #B.base_heap #_ #pcm (E.lower_inames #(small_sig u#a) e) r v

(* Ghost references to "big" types *)
let big_ghost_pts_to (#a:Type u#(a + 1)) (#p:pcm a) (r:ghost_ref p) (v:a)
: big_vprop u#a
= up (small_sig.ghost_pts_to false #a #p r v)

let big_ghost_alloc
    (#o:_)
    (#a:Type u#(a + 1))
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: pst_ghost_action_except
    (ghost_ref pcm)
    o
    emp 
    (fun r -> big_ghost_pts_to r x)
= up_emp_big ();
  coerce_action #_ #_ #_ #(reveal_slprop emp) #(fun r -> up (small_sig.ghost_pts_to false #a #pcm r x)) () <|
  lift_action_alt #small_sig <|
  E.ghost_alloc #B.base_heap #_ #pcm (E.lower_inames #(small_sig u#a) o) x

let big_ghost_read
    #o
    (#a:Type u#(a + 1))
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: pst_ghost_action_except
    (erased (v:a{compatible p x v /\ p.refine v}))
    o
    (big_ghost_pts_to r x)
    (fun v -> big_ghost_pts_to r (f v))
= coerce_action #(erased (v:a{compatible p x v /\ p.refine v})) #_ #_
                #(reveal_slprop (big_ghost_pts_to r x)) 
                #(fun v -> up (small_sig.ghost_pts_to false #a #p r (f v)))
                #(big_ghost_pts_to r x)
                #(fun v -> big_ghost_pts_to r (f v))
                () <|
  lift_action_alt #small_sig <|
  E.ghost_read #B.base_heap #_ #p (E.lower_inames #(small_sig u#a) o) r x f

let big_ghost_write
    #o
    (#a:Type u#(a + 1))
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_ghost_action_except unit o 
    (big_ghost_pts_to r x)
    (fun _ -> big_ghost_pts_to r y)
= coerce_action #_ #_ #_ #(reveal_slprop (big_ghost_pts_to r x)) () <|
  lift_action_alt #small_sig <|
  E.ghost_write #B.base_heap #_ #p (E.lower_inames #(small_sig u#a) o) r x y f

let big_ghost_share
    #e
    (#a:Type u#(a + 1))
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit e
    (big_ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> big_ghost_pts_to r v0 `star` big_ghost_pts_to r v1)
= up_star_big (small_sig.ghost_pts_to false #a #pcm r v0) (small_sig.ghost_pts_to false #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (big_ghost_pts_to r (v0 `op pcm` v1))) () <|
  lift_action_alt #small_sig <|
  E.ghost_share #B.base_heap #_ #pcm (E.lower_inames #(small_sig u#a) e) r v0 v1


let big_ghost_gather
    #e
    (#a:Type u#(a + 1))
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: pst_ghost_action_except
    (squash (composable pcm v0 v1)) e
    (big_ghost_pts_to r v0 `star` big_ghost_pts_to r v1)
    (fun _ -> big_ghost_pts_to r (op pcm v0 v1))
= up_star_big (small_sig.ghost_pts_to false #a #pcm r v0) (small_sig.ghost_pts_to false #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (big_ghost_pts_to r v0 `star` big_ghost_pts_to r v1)) () <|
  lift_action_alt #small_sig <|
  E.ghost_gather #B.base_heap #_ #pcm (E.lower_inames #(small_sig u#a) e) r v0 v1

  (* References for objects in universes a+2, "non-boxable" pts_to *)
let nb_pts_to (#a:Type u#(a + 2)) (#pcm:_) (r:ref a pcm) (v:a)
: slprop u#a
= sig.pts_to #a #pcm r v

(** Splitting a permission on a composite resource into two separate permissions *)
let nb_split_action
      (#a:Type u#(a + 2))
      (#pcm:pcm a)
      (e:inames)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit e
    (nb_pts_to r (v0 `op pcm` v1))
    (fun _ -> nb_pts_to r v0 `star` nb_pts_to r v1)
= coerce_action #_ #_ #_ #(reveal_slprop (nb_pts_to r (v0 `op pcm` v1))) () <|
  E.split_action #small_sig #_ #pcm e r v0 v1


(** Combining separate permissions into a single composite permission *)
let nb_gather_action
      (#a:Type u#(a + 2))
      (#pcm:pcm a)
      (e:inames)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:FStar.Ghost.erased a)
: pst_ghost_action_except (squash (composable pcm v0 v1)) e
    (nb_pts_to r v0 `star` nb_pts_to r v1)
    (fun _ -> nb_pts_to r (op pcm v0 v1))
= coerce_action #_ #_ #_ #(reveal_slprop (nb_pts_to r v0 `star` nb_pts_to r v1)) () <|
  E.gather_action #small_sig #_ #pcm e r v0 v1

let nb_alloc_action
      (#a:Type u#(a + 2))
      (#pcm:pcm a)
      (e:inames)
      (x:a{pcm.refine x})
: pst_action_except (ref a pcm) e
    emp
    (fun r -> nb_pts_to r x)
= coerce_action #_ #_ #_ #(reveal_slprop emp) #(fun r -> sig.pts_to #a #pcm r x) () <|
  E.alloc_action #small_sig #_ #pcm e x


let nb_select_refine
      (#a:Type u#(a + 2))
      (#p:pcm a)
      (e:inames)
      (r:ref a p)
      (x:erased a)
      (f:(v:a{compatible p x v}
          -> GTot (y:a{compatible p y v /\
                      FStar.PCM.frame_compatible p x v y})))
: pst_action_except (v:a{compatible p x v /\ p.refine v}) e
    (nb_pts_to r x)
    (fun v -> nb_pts_to r (f v))
= coerce_action #(v:a{compatible p x v /\ p.refine v}) #_ #_
      #(reveal_slprop (nb_pts_to r x))
      #(fun v -> nb_pts_to #a #p r (f v))
      #(nb_pts_to r x)
      #(fun v -> nb_pts_to r (f v))
      () <|
  E.select_refine #small_sig #_ #p e r x f

let nb_upd_gen
    (#a:Type u#(a + 2))
    (#p:pcm a)
    (e:inames)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_action_except unit e
    (nb_pts_to r x)
    (fun _ -> nb_pts_to r y)
= coerce_action #_ #_ #_ #(reveal_slprop (nb_pts_to r x)) () <|
  E.upd_gen #small_sig #_ #p e r x y f


let nb_pts_to_not_null_action 
      (#a:Type u#(a + 2))
      (#pcm:pcm a)
      (e:inames)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r))) e
    (nb_pts_to r v)
    (fun _ -> nb_pts_to r v)
= coerce_action #_ #_ #_ #(reveal_slprop (nb_pts_to r v)) () <|
  E.pts_to_not_null_action #small_sig #_ #pcm e r v

let nb_ghost_pts_to (#a:Type u#(a + 2)) (#p:pcm a) (r:ghost_ref p) (v:a)
: slprop u#a
= sig.ghost_pts_to false #a #p r v

let nb_ghost_alloc
    (#o:_)
    (#a:Type u#(a + 2))
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: pst_ghost_action_except
    (ghost_ref pcm)
    o
    emp 
    (fun r -> nb_ghost_pts_to r x)
= coerce_action #_ #_ #_ #(reveal_slprop emp) #(fun r -> sig.ghost_pts_to false #a #pcm r x) () <|
  E.ghost_alloc #small_sig #_ #pcm o x

let nb_ghost_read
    #o
    (#a:Type u#(a + 2))
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: pst_ghost_action_except
    (erased (v:a{compatible p x v /\ p.refine v}))
    o
    (nb_ghost_pts_to r x)
    (fun v -> nb_ghost_pts_to r (f v))
= coerce_action #(erased (v:a{compatible p x v /\ p.refine v})) #_ #_
                #(reveal_slprop (nb_ghost_pts_to r x)) 
                #(fun v -> (sig.ghost_pts_to false #a #p r (f v)))
                #(nb_ghost_pts_to r x)
                #(fun v -> nb_ghost_pts_to r (f v))
                () <|
  E.ghost_read #small_sig #_ #p o r x f


let nb_ghost_write
    #o
    (#a:Type u#(a + 2))
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_ghost_action_except unit o 
    (nb_ghost_pts_to r x)
    (fun _ -> nb_ghost_pts_to r y)
= coerce_action #_ #_ #_ #(reveal_slprop (nb_ghost_pts_to r x)) () <|
  E.ghost_write #small_sig #_ #p o r x y f


let nb_ghost_share
    #o
    (#a:Type u#(a + 2))
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit o
    (nb_ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> nb_ghost_pts_to r v0 `star` nb_ghost_pts_to r v1)
= coerce_action #_ #_ #_ #(reveal_slprop (nb_ghost_pts_to r (v0 `op pcm` v1))) () <|
  E.ghost_share #small_sig #_ #pcm o r v0 v1


let nb_ghost_gather
    #o
    (#a:Type u#(a + 2))
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: pst_ghost_action_except
    (squash (composable pcm v0 v1)) o
    (nb_ghost_pts_to r v0 `star` nb_ghost_pts_to r v1)
    (fun _ -> nb_ghost_pts_to r (op pcm v0 v1))
= coerce_action #_ #_ #_ #(reveal_slprop (nb_ghost_pts_to r v0 `star` nb_ghost_pts_to r v1)) () <|
  E.ghost_gather #small_sig #_ #pcm o r v0 v1


