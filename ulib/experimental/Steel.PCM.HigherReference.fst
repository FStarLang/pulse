(*
   Copyright 2020 Microsoft Research

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

module Steel.PCM.HigherReference
open Steel.PCM.Effect
open Steel.PCM.Effect.Atomic
open Steel.PCM.Memory
open FStar.Ghost
open FStar.Real
open Steel.PCM
open Steel.PCM.FractionalPermission
module Atomic = Steel.PCM.Effect.Atomic

let fractional (a:Type u#1) = option (a & perm)
#push-options "--query_stats"
let composable #a : symrel (fractional a) =
  fun (f0 f1:fractional a) ->
    match f0, f1 with
    | None, _
    | _, None -> True
    | Some (x0, p0), Some (x1, p1) -> x0==x1 /\ (sum_perm p0 p1).v <=. 1.0R
#pop-options
let compose #a (f0:fractional a) (f1:fractional a{composable f0 f1}) : fractional a =
  match f0, f1 with
  | None, f
  | f, None -> f
  | Some (x0, p0), Some (_, p1) -> Some (x0, sum_perm p0 p1)

let pcm_frac #a : pcm (fractional a) = {
  p = {
         composable = composable;
         op = compose;
         one = None
      };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ())
}

module Mem = Steel.PCM.Memory

let ref a = Mem.ref (fractional a) pcm_frac
let perm_ok p : prop = (p.v <=. 1.0R == true) /\ True
let pts_to_raw (#a:Type) (r:ref a) (p:perm) (v:erased a) = Mem.pts_to r (Some (Ghost.reveal v, p))
let pts_to #a r p v = pts_to_raw r p v `star` pure (perm_ok p)

assume
val sl_admit (#a:_) (#p:_) (q:a -> slprop)
  : SteelT a p q

assume
val sl_admit_atomic (#a:_) (#uses:_) (#p:_) (q:a -> slprop)
  : SteelAtomic a uses unobservable p q

assume
val sl_assert (p:slprop)
  : SteelT unit p (fun _ -> p)

assume
val sl_return (#a:_) (p:a -> slprop) (x:a)
  : SteelT a (p x) p

assume
val elim_pure (#uses:_) (p:prop)
  : SteelAtomic (_:unit{p}) uses unobservable
                (pure p)
                (fun _ -> emp)

let drop (p:slprop)
  : SteelT unit p (fun _ -> emp)
  = lift_atomic_to_steelT (fun _ ->
    Atomic.change_slprop _ _ (fun m -> emp_unit p; affine_star p emp m))

let comm (#opened_invariants:inames)
         (#p #q:slprop) (_:unit)
  : SteelAtomic unit opened_invariants unobservable
                (p `star` q)
                (fun x -> q `star` p)
  = Atomic.change_slprop _ _ (fun m -> Mem.star_commutative p q)

let intro_perm_ok #uses (p:perm{perm_ok p}) (q:slprop)
  : SteelAtomic unit uses unobservable
                q
                (fun _ -> q `star` pure (perm_ok p))
  = Atomic.change_slprop _ _
    (fun m -> emp_unit q; pure_star_interp q (perm_ok p) m)

let elim_perm_ok #uses (p:perm)
  : SteelAtomic (q:perm{perm_ok q /\ q == p}) uses unobservable
                (pure (perm_ok p))
                (fun _ -> emp)
  = let _ = elim_pure (perm_ok p) in
    Atomic.return_atomic p

let intro_pts_to (p:perm{perm_ok p}) #a #uses (#v:erased a) (r:ref a) (_:unit)
  : SteelAtomic unit uses unobservable
                (pts_to_raw r p v)
                (fun _ -> pts_to r p v)
  = intro_perm_ok p _

let intro_pure (#a:_) (#p:a -> slprop) (q:perm { perm_ok q }) (x:a)
  : SteelT a (p x) (fun y -> p y `star` pure (perm_ok q))
  = Atomic.lift_atomic_to_steelT (fun _ -> intro_perm_ok q _);
    sl_return _ x

let drop_l_atomic #uses (#p #q:slprop)  ()
  : SteelAtomic unit uses unobservable (p `star` q) (fun _ -> q)
  = Atomic.change_slprop _ _ (affine_star p q)

let elim_pure_atomic #uses  (#p:perm -> slprop) (q:perm)
  : SteelAtomic (q':perm{perm_ok q' /\ q == q'}) uses unobservable
                (p q `star` pure (perm_ok q))
                (fun q' -> p q')
  = comm();
    let q' = Atomic.frame _ (fun _ -> elim_perm_ok q) in
    h_assert_atomic (emp `star` p q);
    drop_l_atomic ();
    Atomic.return_atomic q'

let elim_perm_ok_star (#p:slprop) (q:perm)
  : SteelT (_:unit{perm_ok q}) (p `star` pure (perm_ok q))
           (fun _ -> p)
  = let _ = Atomic.lift_atomic_to_steelT (fun () -> elim_pure_atomic #Set.empty #(fun _ -> p) q) in
    sl_return _ ()

let alloc #a x =
  let v = Some (x, full_perm) in
  assert (Steel.PCM.composable pcm_frac v None);
  assert (compatible pcm_frac v v);
  let x = Steel.PCM.Effect.alloc v in
  intro_pure full_perm x

let read (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : SteelT a (pts_to r p v) (fun x -> pts_to r p x)
  = let v1 : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, p)) in
    elim_perm_ok_star p;
    let v2 = Steel.PCM.Effect.read r v1 in
    let Some (x, _) = v2 in
    intro_pure p x

let read_refine (#a:Type) (#p:perm) (q:a -> slprop) (r:ref a)
  : SteelT a (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)
  = sl_admit _

let write (#a:Type) (#v:erased a) (r:ref a) (x:a)
  : SteelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm x)
  = let v_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, full_perm)) in
    let v_new : fractional a = Some (x, full_perm) in
    elim_perm_ok_star full_perm;
    Steel.PCM.Effect.write r v_old v_new;
    intro_pure full_perm ()

let free (#a:Type) (#v:erased a) (r:ref a)
  : SteelT unit (pts_to r full_perm v) (fun _ -> emp)
  = let v_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, full_perm)) in
    elim_perm_ok_star full_perm;
    Steel.PCM.Effect.free r v_old;
    drop _

(* move these to Mem *)
let mem_share_atomic_raw (#a:Type) (#uses:_) (#p:perm{perm_ok p}) (r:ref a)
                         (v0:erased a)
  : action_except unit uses (pts_to_raw r p v0)
                            (fun _ -> pts_to_raw r (half_perm p) v0 `star` pts_to_raw r (half_perm p) v0)
  = let v = Ghost.hide (Some (Ghost.reveal v0, half_perm p)) in
    Mem.split_action uses r v v

let share_atomic_raw #a #uses (#p:perm) (r:ref a{perm_ok p}) (v0:erased a)
  : SteelAtomic unit uses unobservable
                (pts_to_raw r p v0)
                (fun _ -> pts_to_raw r (half_perm p) v0 `star` pts_to_raw r (half_perm p) v0)
  = as_atomic_action (mem_share_atomic_raw r v0)

let share (#a:Type) #uses (#p:perm) (#v:erased a) (r:ref a)
  : SteelAtomic unit uses unobservable
               (pts_to r p v)
               (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)
  = let p = elim_pure_atomic #_ #(fun q -> pts_to_raw r q v) p in
    share_atomic_raw r v;
    h_assert_atomic (pts_to_raw r (half_perm p) v `star` pts_to_raw r (half_perm p) v);
    Steel.PCM.Effect.Atomic.frame _
                                  (intro_pts_to (half_perm p) r);
    h_assert_atomic (pts_to r (half_perm p) v `star` pts_to_raw r (half_perm p) v);
    comm ();
    h_assert_atomic (pts_to_raw r (half_perm p) v `star` pts_to r (half_perm p) v);
    Steel.PCM.Effect.Atomic.frame #unit #uses #unobservable
                                  #(pts_to_raw r (half_perm p) v)
                                  #(fun _ -> pts_to r (half_perm p) v)
                                  (pts_to r (half_perm p) v)
                                  (intro_pts_to (half_perm p) r)

let mem_gather_atomic_raw (#a:Type) (#uses:_) (#p0 #p1:perm) (r:ref a) (v0:erased a) (v1:erased a)
  : action_except (_:unit{v0==v1 /\ perm_ok (sum_perm p0 p1)}) uses
                  (pts_to_raw r p0 v0 `star` pts_to_raw r p1 v1)
                  (fun _ -> pts_to_raw r (sum_perm p0 p1) v0)
  = let v0 = Ghost.hide (Some (Ghost.reveal v0, p0)) in
    let v1 = Ghost.hide (Some (Ghost.reveal v1, p1)) in
    Mem.gather_action uses r v0 v1

let gather_atomic_raw (#a:Type) (#uses:_) (#p0 #p1:perm) (r:ref a) (v0:erased a) (v1:erased a)
  : SteelAtomic  (_:unit{v0==v1 /\ perm_ok (sum_perm p0 p1)}) uses unobservable
                 (pts_to_raw r p0 v0 `star` pts_to_raw r p1 v1)
                 (fun _ -> pts_to_raw r (sum_perm p0 p1) v0)
  = as_atomic_action (mem_gather_atomic_raw r v0 v1)

let gather (#a:Type) (#uses:_) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  = let p0 = Steel.PCM.Effect.Atomic.frame _ (fun _ -> elim_pure_atomic p0) in
    comm();
    let p1 = Steel.PCM.Effect.Atomic.frame _ (fun _ -> elim_pure_atomic p1) in
    comm();
    h_assert_atomic (pts_to_raw r p0 v0 `star` pts_to_raw r p1 v1);
    let _ = gather_atomic_raw r v0 v1 in
    intro_pts_to (sum_perm p0 p1) r ()

let ghost_read_refine = admit()
