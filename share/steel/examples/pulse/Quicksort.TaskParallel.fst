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

module QuickSort.TaskParallel
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
open Pulse.Lib.InvList

module T = TaskPool
open QuickSortParallel
open Pulse.Lib.Par.Pledge

let quicksort_post a lo hi s0 lb rb : vprop =
  exists* s. (A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s))

```pulse
fn rec t_quicksort
  (p : T.pool)
  (f : perm)
  (a: A.array int)
  (lo: nat) (hi:(hi:int{-1 <= hi - 1 /\ lo <= hi}))
  (lb rb: int)
  (#s0: Ghost.erased (Seq.seq int))
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
    T.share_alive p (half_perm f);

    t_quicksort p (half_perm (half_perm f)) a r._2 hi pivot rb;
    T.spawn_ p #(half_perm f) (fun () -> t_quicksort p (half_perm (half_perm f)) a lo r._1 lb pivot);
    
    return_pledge [] (T.pool_done p) (T.pool_alive #(half_perm f) p ** A.pts_to_range a r._1 r._2 s2);
    squash_pledge [] (T.pool_done p) _;
    join_pledge #[] #(T.pool_done p) _ _;
    join_pledge #[] #(T.pool_done p) _ _;
    
    ghost fn
    rewrite_pf
      (_:unit)
      requires
        (T.pool_alive #(half_perm (half_perm f)) p ** quicksort_post a lo r._1 s1 lb pivot) **
        (T.pool_alive #(half_perm f) p             ** A.pts_to_range a r._1 r._2 s2) **
        (T.pool_alive #(half_perm (half_perm f)) p ** quicksort_post a r._2 hi s3 pivot rb)
      ensures
        T.pool_alive #f p **
        quicksort_post a lo hi s0 lb rb
    {
      unfold quicksort_post;
      unfold quicksort_post;
      quicksort_proof a lo r._1 r._2 hi lb rb pivot #s0 s1 s2 s3;
      fold (quicksort_post a lo hi s0 lb rb);

      T.gather_alive p (half_perm f);
      T.gather_alive p f;
    };
    rewrite_pledge0 #[] #(T.pool_done p)
        // NB: These two vprops have to be in exactly this shape, as the Pulse checker
        // will not commute or in anyway modify each side of the pledge. The function
        // above must also be in this exact shape. To obtain the shape, I just manually looked
        // at the context. Automation should likely help here.
        (
          (T.pool_alive #(half_perm (half_perm f)) p ** quicksort_post a lo r._1 s1 lb pivot) **
          (T.pool_alive #(half_perm f) p             ** A.pts_to_range a r._1 r._2 s2) **
          (T.pool_alive #(half_perm (half_perm f)) p ** quicksort_post a r._2 hi s3 pivot rb)
        )
        (
          T.pool_alive #f p **
          quicksort_post a lo hi s0 lb rb
        )
        rewrite_pf;

    ()
  } else {
    return_pledge [] (T.pool_done p) (
      T.pool_alive #f p **
      (exists* s. A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s))
    );
  }
}
```

```pulse
fn rec quicksort
  (a: A.array int)
  (lo: nat) (hi:(hi:int{-1 <= hi - 1 /\ lo <= hi}))
  (lb rb: int)
  (#s0: Ghost.erased (Seq.seq int))
  requires
    A.pts_to_range a lo hi s0 **
    pure (pure_pre_quicksort a lo hi lb rb s0)
  ensures
    quicksort_post a lo hi s0 lb rb
{
  assume_ (pure (comp_perm (half_perm full_perm) == half_perm full_perm)); // F* limitation, real arith

  let p = T.setup_pool 8;
  T.share_alive p full_perm;
  t_quicksort p (half_perm full_perm) a lo hi lb rb #s0;

  let i = split_pledge #[] #(T.pool_done p) (T.pool_alive #(half_perm full_perm) p) (quicksort_post a lo hi s0 lb rb);

  rewrite
    pledge (add_one i []) (T.pool_done p) (T.pool_alive #(half_perm full_perm) p)
  as
    pledge (add_one i []) (T.pool_done p) (T.pool_alive #(comp_perm (half_perm full_perm)) p);

  T.teardown_pool' #(add_one i []) p (half_perm full_perm);
  redeem_pledge (add_one i []) (T.pool_done p) (quicksort_post a lo hi s0 lb rb);
  drop_ (T.pool_done p);
}
```
