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

module QuickSort.Task.NuPool

open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT

open Pulse.Lib.InvList

open Codeable
module T = NuPool.Code
open NuPool.Code
module TC = FStar.Tactics.Typeclasses
open NuPool.Autocode
open Quicksort.Base
open Pulse.Lib.Par.Pledge

let quicksort_post a lo hi s0 lb rb : vprop =
  op_exists_Star #(Seq.seq int) (FunctionalExtensionality.on (Seq.seq int) (fun s -> A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s)))
  
assume (* XXX, should be OK *)
SmallPtsToRange : forall t (a : A.array t) lo hi s. is_small (A.pts_to_range a lo hi s)

assume  (* XXX *)
val codeable_pool_alive (p:T.pool) (f:perm) : codeable (poolcode Codeable.small_code) (T.pool_alive #f p)

assume  (* XXX *)
val codeable_pool_done (p:T.pool) : codeable (poolcode Codeable.small_code) (T.pool_done p)

val cod1 (p:T.pool) (f:perm) (a:A.array int) (lo:nat) (hi:nat{lo <= hi}) (pivot:int) (s : erased (Seq.seq int)) (lb rb : erased int)
: codeable (poolcode Codeable.small_code)
           (T.pool_alive #(half_perm f) p ** A.pts_to_range a lo hi s ** pure (pure_pre_quicksort a lo hi lb pivot s))

let cod1 p f a lo hi pivot s lb rb =
  codeable_star _ _ _
  (codeable_star _ _ _
    (codeable_pool_alive p (half_perm f))
    (codeable_base _ _ <| codeable_small _ _))
  (codeable_base _ _ <| codeable_small _ (pure_is_small _))

val codeable_qs_post (a:A.array int) (lo:nat) (hi:nat{lo <= hi}) (s0 : erased (Seq.seq int)) (lb rb : erased int)
: codeable (poolcode Codeable.small_code)
           (quicksort_post a lo hi s0 lb rb)

let codeable_qs_post a lo hi s0 lb rb =
  let open FStar.Tactics.V2 in
  coerce_eq (_ by (trefl())) <|
    codeable_exists2
      Codeable.small_code
      (Seq.seq int)
      (fun s -> A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s))
      (fun (x: Seq.seq int) -> codeable_star _ _ _
                                  (codeable_base _ _ <| codeable_small _ _)
                                  (codeable_base _ _ <| codeable_small _ <| pure_is_small _)
                                  )

val cod2 (p:T.pool) (f:perm) (a:A.array int) (lo:nat) (hi:nat{lo <= hi}) (s : erased (Seq.seq int)) (lb rb : erased int)
: codeable (poolcode Codeable.small_code)
           (pledge [] (T.pool_done p) (T.pool_alive #(half_perm f) p ** quicksort_post a lo hi s lb rb))
           
let cod2 p f a lo hi s lb rb =
  let open FStar.FunctionalExtensionality in
  codeable_pledge _
    _ (codeable_pool_done p)
    _ (codeable_star _ _ _
       (codeable_pool_alive p (half_perm f))
       (codeable_qs_post a lo hi s lb rb))

open FStar.Tactics.V2

let op_exists_star_on_lem
  (a : Type)
  (f : a -> vprop)
  : Lemma (op_exists_Star #a f == op_exists_Star #a (FunctionalExtensionality.on a f))
          [SMTPat (op_exists_Star #a f)]
  = admit() (* XXX *)

let op_exists_star_on_lem2
  (a : Type)
  (f : a -> vprop)
  : Lemma (op_exists_Star #a (FunctionalExtensionality.on a f) == op_exists_Star #a f)
          [SMTPat (op_exists_Star #a f)]
  = op_exists_star_on_lem a f

let vprop_equiv_refl' (v0 v1 :vprop) (_ : squash (v0 == v1)) : vprop_equiv v0 v1 = vprop_equiv_refl v0

let tac1 () : Tac unit =
  apply (`vprop_equiv_refl');
  apply_lemma (`op_exists_star_on_lem)
let tac2 () : Tac unit =
  apply (`vprop_equiv_refl');
  apply_lemma (`op_exists_star_on_lem2)

```pulse
fn rec t_quicksort
  (p : T.pool{p.base == small_code})
  (#f : perm)
  (a : A.array int)
  (lo : nat) (hi : (hi:nat{lo <= hi}))
  (#lb #rb : erased int)
  (#s0 : erased (Seq.seq int))
  requires
    T.pool_alive #f p **
    A.pts_to_range a lo hi s0 **
    pure (pure_pre_quicksort a lo hi lb rb s0)
  ensures 
    pledge [] (T.pool_done p) (
      T.pool_alive #f p **
      quicksort_post a lo hi s0 lb rb
    )
{
  if (lo < hi - 1)
  {
    let r = partition_wrapper a lo hi lb rb;
    let pivot = r._3;
    with s1. assert (A.pts_to_range a lo r._1 s1);
    with s2. assert (A.pts_to_range a r._1 r._2 s2);
    with s3. assert (A.pts_to_range a r._2 hi s3);

    T.share_alive p f;

    T.spawn_ p #(half_perm f)
      #(T.pool_alive #(half_perm f) p ** A.pts_to_range a lo r._1 s1 ** pure (pure_pre_quicksort a lo r._1 lb pivot s1))
      #(cod1 p f a lo r._1 pivot s1 lb rb)
      #(pledge [] (T.pool_done p) (T.pool_alive #(half_perm f) p ** quicksort_post a lo r._1 s1 lb pivot))
      #(cod2 p f a lo r._1 s1 lb pivot)
      (fun () -> t_quicksort p #(half_perm f) a lo r._1 #lb #pivot);

    t_quicksort p #(half_perm f) a r._2 hi #pivot #rb;
    
    return_pledge [] (T.pool_done p) (A.pts_to_range a r._1 r._2 s2);
    squash_pledge _ _ _;
    join_pledge _ _;
    join_pledge _ _;

    ghost fn rewrite_pf ()
      // NB: These two vprops have to be in exactly this shape, as the Pulse checker
      // will not commute or in anyway modify each side of the pledge. The function
      // above must also be in this exact shape. To obtain the shape, I just manually looked
      // at the context. Automation should likely help here.
      requires
        (T.pool_alive #(half_perm f) p ** quicksort_post a lo r._1 s1 lb pivot) **
        A.pts_to_range a r._1 r._2 s2 **
        (T.pool_alive #(half_perm f) p ** quicksort_post a r._2 hi s3 pivot rb)
      ensures
        T.pool_alive #f p **
        quicksort_post a lo hi s0 lb rb
    {
      (* Functional correctness *)

      unfold quicksort_post;
      unfold quicksort_post;

      (* Removing the on_domain *)
      rewrite_by
        (op_exists_Star #(Seq.seq int) (FunctionalExtensionality.on (Seq.seq int) (fun s -> A.pts_to_range a lo r._1 s ** pure (pure_post_quicksort a lo r._1 lb pivot s1 s))))
        (op_exists_Star #(Seq.seq int) (fun s -> A.pts_to_range a lo r._1 s ** pure (pure_post_quicksort a lo r._1 lb pivot s1 s)))
        tac2
        ();
      rewrite_by
        (op_exists_Star #(Seq.seq int) (FunctionalExtensionality.on (Seq.seq int) (fun s -> A.pts_to_range a r._2 hi s ** pure (pure_post_quicksort a r._2 hi pivot rb s3 s))))
        (op_exists_Star #(Seq.seq int) (fun s -> A.pts_to_range a r._2 hi s ** pure (pure_post_quicksort a r._2 hi pivot rb s3 s)))
        tac2
        ();

      quicksort_proof a lo r._1 r._2 hi lb rb pivot #s0 s1 s2 s3;

      rewrite_by
        (op_exists_Star #(Seq.seq int) (fun s -> A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s)))
        (op_exists_Star #(Seq.seq int) (FunctionalExtensionality.on (Seq.seq int) (fun s -> A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s))))
        tac1
        ();

      fold (quicksort_post a lo hi s0 lb rb);

      (* Permission accounting *)
      T.gather_alive p f;
    };
    rewrite_pledge0 _ _ rewrite_pf;

    ()
  } else {
    rewrite_by
      (op_exists_Star #(Seq.seq int) (fun s -> A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s)))
      (op_exists_Star #(Seq.seq int) (FunctionalExtensionality.on (Seq.seq int) (fun s -> A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s))))
      tac1
      ();
    return_pledge [] (T.pool_done p) (
      T.pool_alive #f p **
      (op_exists_Star #(Seq.seq int) (FunctionalExtensionality.on (Seq.seq int) (fun s -> A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s))))
    );
  }
}
```

```pulse
fn rec quicksort
  (nthr : pos)
  (a : A.array int)
  (lo : nat) (hi : (hi:nat{lo <= hi}))
  (#lb #rb : erased int)
  (#s0 : erased (Seq.seq int))
  requires
    A.pts_to_range a lo hi s0 **
    pure (pure_pre_quicksort a lo hi lb rb s0)
  ensures
    quicksort_post a lo hi s0 lb rb
{
  let p = T.setup_pool #Codeable.small_code nthr;
  T.share_alive p _;
  t_quicksort p a lo hi #lb #rb;
  T.await_pool p _;
  T.gather_alive p _;
  T.teardown_pool p;
  drop_ (T.pool_done p);
}
```
