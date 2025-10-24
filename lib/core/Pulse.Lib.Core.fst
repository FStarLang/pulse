(*
   Copyright 2023 Microsoft Research

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
module Pulse.Lib.Core
module I = PulseCore.InstantiatedSemantics
module A = PulseCore.Atomic
module T = FStar.Tactics.V2
open PulseCore.InstantiatedSemantics
open PulseCore.FractionalPermission
open PulseCore.Observability
friend PulseCore.InstantiatedSemantics
module Sep = PulseCore.IndirectionTheorySep

let mkey = ()
let no_mkeys = ()

let allow_ambiguous = ()

let slprop = slprop
let timeless p = Sep.timeless p

let emp = emp
let timeless_emp = Sep.timeless_emp ()
let pure = pure
let timeless_pure p = Sep.timeless_pure p
let op_Star_Star = op_Star_Star
let timeless_star p q = Sep.timeless_star p q
let op_exists_Star = op_exists_Star
let exists_extensional (#a:Type u#a) (p q: a -> slprop)
  (_:squash (forall x. p x == q x))
  : Lemma (op_exists_Star p == op_exists_Star q)
  = introduce forall x. slprop_equiv (p x) (q x)
    with (
        slprop_equiv_refl (p x)
    );
    I.slprop_equiv_exists p q ()
let timeless_exists #a p =
  exists_extensional p (fun x -> p x) ();
  Sep.timeless_exists p;
  let unfold h: squash (Sep.timeless Sep.(exists* x. p x)) = () in
  let unfold h: squash (Sep.timeless (exists* x. p x)) = h in
  ()
let slprop_equiv = slprop_equiv
let elim_slprop_equiv #p #q pf = slprop_equiv_elim p q
let slprop_post_equiv = slprop_post_equiv
let prop_squash_idem (p:prop)
  : Tot (squash (squash p == p))
  = FStar.PropositionalExtensionality.apply p (squash p)

let intro_slprop_post_equiv
       (#t:Type u#a) 
       (p q: t -> slprop)
       (pf: (x:t -> slprop_equiv (p x) (q x)))
  : slprop_post_equiv p q
  = let pf : squash (forall x. slprop_equiv (p x) (q x)) = 
        introduce forall x. slprop_equiv (p x) (q x)
        with FStar.Squash.return_squash (pf x)
    in
    coerce_eq (prop_squash_idem _) pf

let elim_slprop_post_equiv (#t:Type u#a)
                          (p q: t -> slprop) 
                          (pf:slprop_post_equiv p q)
                          (x:t) 
: slprop_equiv (p x) (q x)
= let pf
    : squash (slprop_equiv (p x) (q x))
    = eliminate forall x. slprop_equiv (p x) (q x) with x
  in
  coerce_eq (prop_squash_idem _) pf

let slprop_equiv_refl (v0:slprop) 
  : slprop_equiv v0 v0
  = slprop_equiv_refl v0

let slprop_equiv_sym (v0 v1:slprop) (p:slprop_equiv v0 v1)
  : slprop_equiv v1 v0
  = slprop_equiv_elim v0 v1; p

let slprop_equiv_trans
      (v0 v1 v2:slprop)
      (p:slprop_equiv v0 v1)
      (q:slprop_equiv v1 v2)
  : slprop_equiv v0 v2
  = slprop_equiv_elim v0 v1;
    slprop_equiv_elim v1 v2;
    p

let slprop_equiv_unit (x:slprop)
  : slprop_equiv (emp ** x) x
  = slprop_equiv_unit x

let slprop_equiv_comm (p1 p2:slprop)
  : slprop_equiv (p1 ** p2) (p2 ** p1)
  = slprop_equiv_comm p1 p2

let slprop_equiv_assoc (p1 p2 p3:slprop)
  : slprop_equiv ((p1 ** p2) ** p3) (p1 ** (p2 ** p3))
  = slprop_equiv_assoc p1 p2 p3

let slprop_equiv_exists (#a:Type) (p q : a -> slprop)
  (_ : squash (forall x. slprop_equiv (p x) (q x)))
  : slprop_equiv (op_exists_Star p) (op_exists_Star q)
  = slprop_equiv_exists p q ()

let slprop_equiv_cong (p1 p2 p3 p4:slprop)
                     (f: slprop_equiv p1 p3)
                     (g: slprop_equiv p2 p4)
  : slprop_equiv (p1 ** p2) (p3 ** p4)
  = slprop_equiv_elim p1 p3;
    slprop_equiv_elim p2 p4;
    slprop_equiv_refl (p1 ** p2)

let slprop_equiv_ext p1 p2 _ = slprop_equiv_refl p1

(* Invariants, just reexport *)
module Act = PulseCore.Action

let iname = Act.iref
let deq_iname = Sep.deq_iref
instance non_informative_iname = {
  reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer iname;
}

let join_sub _ _ = ()
let join_emp is =
  GhostSet.lemma_equal_intro (join_inames is emp_inames) is;
  GhostSet.lemma_equal_intro (join_inames emp_inames is) is

let inv i p = Act.(inv i p)
let inames_live = Sep.inames_live
let add_already_there i is = GhostSet.lemma_equal_intro (add_inv is i) is

////////////////////////////////////////////////////////////////////
// stt a pre post: The main type of a pulse computation
////////////////////////////////////////////////////////////////////
let stt = I.stt
let return_stt_noeq = I.return
let bind_stt = I.bind
let frame_stt = I.frame
let sub_stt = I.sub
let conv_stt pf1 pf2 = I.conv #_ _ _ _ _ pf1 pf2
let hide_div = I.hide_div

////////////////////////////////////////////////////////////////////
// Atomic computations
////////////////////////////////////////////////////////////////////
let stt_atomic a #obs inames pre post = A.stt_atomic a #obs inames pre post
let lift_observability = A.lift_observability
let return_neutral = A.return_atomic
let return_neutral_noeq = A.return_atomic_noeq
let bind_atomic = A.bind_atomic
let frame_atomic = A.frame_atomic
let sub_atomic = A.sub_atomic
let sub_invs_atomic = A.sub_invs_stt_atomic
let lift_atomic = A.lift_atomic

////////////////////////////////////////////////////////////////////
// Ghost computations
////////////////////////////////////////////////////////////////////
let stt_ghost = A.stt_ghost
let bind_ghost = A.bind_ghost
(* lift_ghost_neutral takes a dictionary argument in Core, but just a revealer
function internally in the model, hence we project it away. *)
let lift_ghost_neutral #a #pre #post e ni_a = A.lift_ghost_neutral #a #pre #post e ni_a.reveal
let lift_neutral_ghost = A.lift_neutral_ghost
let frame_ghost = A.frame_ghost
let sub_ghost = A.sub_ghost
let sub_invs_ghost = A.sub_invs_stt_ghost

////////////////////////////////////////////////////////////////////
// Locations
////////////////////////////////////////////////////////////////////

let loc_id = unit
let process_of = id
let process_of_idem l = ()
let loc l = emp
let loc_get () = admit ()
let loc_dup l = admit ()
let loc_gather l = admit ()

let on l p = p
let on_intro p = admit ()
let on_elim p = admit ()

let placeless_emp = admit ()
let placeless_star _ _ = admit ()
let placeless_pure _ = admit ()
let placeless_exists _ = admit ()
let placeless_on _ _ = admit ()
let placeless_inv _ _ = admit ()

let ghost_impersonate l pre post f = admit ()

//////////////////////////////////////////////////////////////////////////
// Later
//////////////////////////////////////////////////////////////////////////

let later_credit = later_credit
let timeless_later_credit amt = Sep.timeless_later_credit amt
let later_credit_zero _ = PulseCore.InstantiatedSemantics.later_credit_zero ()
let later_credit_add a b = PulseCore.InstantiatedSemantics.later_credit_add a b

let rec later_credit_buy n =
  if n = 0 then
    (later_credit_zero (); coerce_eq () <| return_stt_noeq () fun _ -> later_credit n)
  else
    bind_stt (A.buy1 ()) fun _ ->
      slprop_equiv_unit (later_credit 1); slprop_equiv_elim (emp ** later_credit 1) (later_credit 1);
      coerce_eq () <| bind_stt #unit #unit #_ #_ #(fun _ -> later_credit n) (frame (later_credit 1) (later_credit_buy (n-1))) fun _ ->
        later_credit_add (n-1) 1;
        coerce_eq () <| return_stt_noeq () fun _ -> later_credit n

let later = later
let later_intro p = A.later_intro p
let later_elim p = A.later_elim p

let later_elim_timeless p = A.implies_elim (later p) p

let later_star = Sep.later_star
let later_exists #t f =
  let h: squash Sep.(later (exists* x. f x) `implies` exists* x. later (f x)) = Sep.later_exists #t f in
  let h: squash (later (exists* x. f x) `implies` exists* x. later (f x)) = h in
  A.implies_elim _ _
let exists_later #t f =
  let h: squash Sep.((exists* x. later (f x)) `implies` later (exists* x. f x)) = Sep.later_exists #t f in
  let h: squash ((exists* x. later (f x)) `implies` later (exists* x. f x)) = h in
  A.implies_elim _ _

//////////////////////////////////////////////////////////////////////////
// Equivalence
//////////////////////////////////////////////////////////////////////////
let rewrite_eq p q (pf:squash (p == q))
  : stt_ghost unit emp_inames p (fun _ -> q)
  = slprop_equiv_elim p q;
    A.noop q
let equiv = I.equiv
let equiv_dup a b = A.equiv_dup a b
let equiv_refl a = A.equiv_refl a
let equiv_comm a b = rewrite_eq (equiv a b) (equiv b a) (Sep.equiv_comm a b)
let equiv_trans a b c = A.equiv_trans a b c
let equiv_elim a b = A.equiv_elim a b
let equiv_elim_timeless a b = 
  rewrite_eq (equiv a b) (pure (eq2 #slprop a b)) (Sep.equiv_timeless a b)
let equiv_star_congr p q r = Sep.equiv_star_congr p q r
let later_equiv = Sep.later_equiv
//////////////////////////////////////////////////////////////////////////
// Higher-order ghost state
//////////////////////////////////////////////////////////////////////////

// TODO: these are write-once for now, though it's possible to construct fractional permission variables out of this
let slprop_ref = PulseCore.Action.slprop_ref
let null_slprop_ref = PulseCore.Action.null_slprop_ref
let slprop_ref_pts_to x y = PulseCore.Action.slprop_ref_pts_to x y
let placeless_slprop_ref_pts_to = admit ()
let slprop_ref_alloc x = A.slprop_ref_alloc x
let slprop_ref_share x #y = A.slprop_ref_share x y
let slprop_ref_gather x #y1 #y2 = A.slprop_ref_gather x y1 y2

////////////////////////////////////////////////////////////////////
// Invariants
////////////////////////////////////////////////////////////////////
let dup_inv = A.dup_inv
let new_invariant p #_ = A.new_invariant p
let fresh_invariant = A.fresh_invariant
let inames_live_inv = A.inames_live_inv
let inames_live_empty _ = rewrite_eq emp (inames_live emp_inames) (Sep.inames_live_empty ())
let share_inames_live i j = rewrite_eq (inames_live (GhostSet.union i j)) (inames_live i ** inames_live j) (Sep.inames_live_union i j)
let gather_inames_live i j = rewrite_eq (inames_live i ** inames_live j) (inames_live (GhostSet.union i j)) (Sep.inames_live_union i j)
let with_invariant = A.with_invariant
let with_invariant_g = A.with_invariant_g
let invariant_name_identifies_invariant #p #q i j = A.invariant_name_identifies_invariant p q i j

//////////////////////////////////////////////////////////////////////////
// Some basic actions and ghost operations
//////////////////////////////////////////////////////////////////////////

let fork pre #_ #l f = I.fork (f l)

let rewrite p q (pf:slprop_equiv p q)
  : stt_ghost unit emp_inames p (fun _ -> q)
  = slprop_equiv_elim p q;
    A.noop q

#push-options "--no_tactics"
let rewrite_by (p:slprop) (q:slprop) 
               (t:unit -> T.Tac unit)
               (_:unit { T.with_tactic t (slprop_equiv p q) })
  : stt_ghost unit emp_inames p (fun _ -> q)
  = let pf : squash (slprop_equiv p q) = T.by_tactic_seman t (slprop_equiv p q) in
    prop_squash_idem (slprop_equiv p q);
    rewrite p q (coerce_eq () pf)
#pop-options

let elim_pure_explicit p = A.elim_pure p
let elim_pure _ #p = A.elim_pure p
let intro_pure p _ = A.intro_pure p ()
let elim_exists #a p = A.elim_exists p
let intro_exists #a p e = A.intro_exists p e
let intro_exists_erased #a p e = A.intro_exists p e

let stt_ghost_reveal a x = A.ghost_reveal a x
let stt_admit _ _ _ = admit () //intentional
let stt_atomic_admit _ _ _ = admit () //intentional
let stt_ghost_admit _ _ _ = admit () //intentional

    
let assert_ (p:slprop) = A.noop p
let assume_ (p:slprop) = admit() //intentional
let drop_ (p:slprop) = A.drop p

let unreachable (#a:Type) (#p:slprop) (#q:a -> slprop) (_:squash False)
  : stt_ghost a emp_inames p q
  = let v = FStar.Pervasives.false_elim #a () in
    let m = A.return_ghost v q in
    coerce_eq () m

let elim_false (a:Type) (p:a -> slprop) =
  A.bind_ghost
    (A.noop (pure False))
    (fun _ -> A.bind_ghost (A.elim_pure False) unreachable )

let as_atomic #a pre post (e:stt a pre post) = admit () // intentional since it is an assumption

let unfold_check_opens = ()

let pulse_unfold = ()
let pulse_eager_unfold = ()
