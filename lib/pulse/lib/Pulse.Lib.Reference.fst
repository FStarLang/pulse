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

module Pulse.Lib.Reference
open Pulse.Lib.Core
open Pulse.Main
module H = Pulse.Lib.HigherReference
module U = FStar.Universe
let ref a = H.ref (U.raise_t a)

let pts_to
    (#a:Type u#0)
    (r:ref a)
    (#[exact (`full_perm)] [@@@equate_by_smt] p:perm)
    ([@@@equate_by_smt] v:a)
  = H.pts_to r #p (U.raise_val v)

```pulse
fn alloc' (#a:Type u#0) (v:a)
requires emp
returns r:ref a
ensures pts_to r v
{
  let r = H.alloc (U.raise_val v);
  fold (pts_to r #full_perm v);
  r
}
```
let alloc = alloc'

```pulse
fn read (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
requires pts_to r #p n
returns x:a
ensures pts_to r #p n ** pure (eq2 #a (reveal n) x)
{
  unfold (pts_to r #p n);
  let k = H.( !r );
  fold (pts_to r #p n);
  U.downgrade_val k
}
```
let ( ! ) #a r #n #p = read #a r #n #p

```pulse
fn write (#a:Type) (r:ref a) (x:a) (#n:erased a)
requires pts_to r #full_perm n
ensures pts_to r #full_perm x
{
  unfold (pts_to r #full_perm n);
  H.(r := (U.raise_val x));
  fold (pts_to r #full_perm x)
}
```
let ( := ) #a r x #n = write #a r x #n

```pulse
fn free' #a (r:ref a) (#n:erased a)
requires pts_to r #full_perm n
ensures emp
{
  unfold (pts_to r #full_perm n);
  H.free r;
}
```
let free = free'

```pulse
ghost
fn share' (#a:Type) (r:ref a) (#v:erased a) (#p:perm)
requires pts_to r #p v
ensures pts_to r #(half_perm p) v ** pts_to r #(half_perm p) v
{
  unfold pts_to r #p v;
  H.share r;
  fold pts_to r #(half_perm p) v;
  fold pts_to r #(half_perm p) v
}
```
let share = share'

```pulse
ghost
fn raise_inj (a:Type u#0) (x0 x1:a)
requires pure (U.raise_val u#0 u#1 x0 == U.raise_val u#0 u#1 x1)
ensures pure (x0 == x1)
{
  assert pure (U.downgrade_val (U.raise_val u#0 u#1 x0) == x0);
  assert pure (U.downgrade_val (U.raise_val u#0 u#1 x1) == x1);
}
```

```pulse
ghost
fn gather' (#a:Type) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
requires pts_to r #p0 x0 ** pts_to r #p1 x1
ensures pts_to r #(sum_perm p0 p1) x0 ** pure (x0 == x1)
{
  unfold pts_to r #p0 x0;
  unfold pts_to r #p1 x1;
  H.gather r;
  fold (pts_to r #(sum_perm p1 p0) x0);
  let qq = sum_perm p0 p1; //hack! prevent the unifier from structurally matching sum_perm p0 p1 with sum_perm p1 p0
  rewrite (pts_to r #(sum_perm p1 p0) x0)
       as (pts_to r #qq x0);
  raise_inj a x0 x1;
}
```
let gather = gather'

let share2 (#a:Type) (r:ref a) (#v:erased a)
: stt_ghost unit
  (pts_to r v)
  (fun _ -> pts_to r #one_half v ** pts_to r #one_half v)
= share #a r #v

let gather2 (#a:Type) (r:ref a) (#x0 #x1:erased a)
: stt_ghost unit
      (pts_to r #one_half x0 ** pts_to r #one_half x1)
      (fun () -> pts_to r x0  ** pure (x0 == x1))
= gather r


let read_atomic (r:ref U32.t) (#n:erased U32.t) (#p:perm)
: stt_atomic U32.t emp_inames
    (pts_to r #p n)
    (fun x -> pts_to r #p n ** pure (reveal n == x))
= Pulse.Lib.Core.as_atomic _ _ (read r #n #p)

let write_atomic (r:ref U32.t) (x:U32.t) (#n:erased U32.t)
= Pulse.Lib.Core.as_atomic _ _ (write r x #n)

```pulse
fn cas_impl
    (r:ref U32.t)
    (u v:U32.t)
    (#i:erased U32.t)
requires
  pts_to r i
returns b:bool
ensures
  cond b (pts_to r v ** pure (reveal i == u)) 
         (pts_to r i)
{
  let u' = read r;
  if (u = u')
  {
    write r v;
    fold (cond true (pts_to r v ** pure (reveal i == u)) (pts_to r i));
    true
  }
  else
  {
    fold cond false (pts_to r v ** pure (reveal i == u)) (pts_to r i);
    false
  }
}
```

let cas r u v #i = Pulse.Lib.Core.as_atomic _ _ (cas_impl r u v #i)


```pulse
fn
raise_exists (#a:Type u#0) (frame:vprop) (p: U.raise_t u#0 u#1 a -> vprop)
requires frame ** (exists* (x:a). p (U.raise_val x))
ensures frame ** (exists* (x:U.raise_t a). p x)
{
  ()
}
```

let with_local
    (#a:Type0)
    (init:a)
    (#pre:vprop)
    (#ret_t:Type)
    (#post:ret_t -> vprop)
    (body:(r:ref a) -> stt ret_t (pre ** pts_to r init)
                                 (fun v -> post v ** op_exists_Star (pts_to r #full_perm)))
: stt ret_t pre post
= let body (r:H.ref (U.raise_t a))
    : stt ret_t (pre ** H.pts_to r #full_perm (U.raise_val init))
                (fun v -> post v ** (exists* (x:U.raise_t a). H.pts_to r #full_perm x)) 
    = let m
        : stt ret_t (pre ** H.pts_to r #full_perm (U.raise_val init))
                    (fun v -> post v ** (exists* (x:a). H.pts_to r #full_perm (U.raise_val x)))
        = body r
      in
      let m0 (v:ret_t)
        : stt ret_t 
            (post v ** (exists* (x:a). H.pts_to r #full_perm (U.raise_val x)))
            (fun v -> post v ** (exists* (x:U.raise_t a). H.pts_to r #full_perm x))
        = bind_stt (raise_exists (post v) (H.pts_to r #full_perm))
                   (fun _ -> return_stt_noeq v (fun v -> post v ** (exists* (x:U.raise_t a). H.pts_to r #full_perm x)))
      in
      bind_stt m m0
  in
  H.with_local (U.raise_val init) body

```pulse
ghost
fn pts_to_injective_eq'
  (#a:Type0)
  (#p #q:perm)
  (#v0 #v1:a)
  (r:ref a)
requires
  pts_to r #p v0 ** pts_to r #q v1
ensures
  pts_to r #p v0 ** pts_to r #q v1 ** pure (v0 == v1)
{
  unfold pts_to r #p v0;
  unfold pts_to r #q v1;
  H.pts_to_injective_eq r;
  fold pts_to r #p v0;
  fold pts_to r #q v1;
  raise_inj _ v0 v1;
}
```
let pts_to_injective_eq = pts_to_injective_eq'

```pulse
ghost
fn pts_to_perm_bound' (#a:_) (#p:_) (r:ref a) (#v:a)
requires pts_to r #p v
ensures pts_to r #p v ** pure (p `lesser_equal_perm` full_perm)
{
  unfold pts_to r #p v;
  H.pts_to_perm_bound r;
  fold pts_to r #p v;
}
```
let pts_to_perm_bound = pts_to_perm_bound'

```pulse
fn replace' (#a:Type0) (r:ref a) (x:a) (#v:erased a)
  requires pts_to r v
  returns y:a
  ensures pts_to r x ** pure (y == reveal v)
{
  let y = !r;
  r := x;
  y
}
```

let replace = replace'
