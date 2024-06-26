(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at


   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.SpinLockToken

open Pulse.Lib.Pervasives
open Pulse.Lib.Stick

module T = Pulse.Lib.InvToken
module L = Pulse.Lib.SpinLock

noeq
type lock (v:vprop) : Type u#4 = {
  l : L.lock;

  i : iref;

  t1 : T.token (L.iref_of l) (L.iref_v_of l v);
  t2 : T.token i (exists* (p:perm). L.lock_active #p l)
}

```pulse
fn new_lock (v:vprop { is_big v })
  requires v
  returns _:lock v
  ensures emp
{
  let l = L.new_lock v;
  L.elim_alive_into_inv_and_active l v #1.0R;
  elim_stick _ _;
  let t1 = T.witness (L.iref_of l);
  let i = new_invariant (exists* (p:perm). L.lock_active #p l);
  let t2 = T.witness i;
  let l = { l; i; t1; t2 };
  l
}
```

let lock_acquired (#v:vprop) (l:lock v) : vprop =
  L.lock_acquired l.l

```pulse
fn lock_alive (#v:vprop) (l:lock v)
  requires emp
  ensures exists* (p:perm). L.lock_alive l.l #p v
{
  T.recall l.t2;
  with_invariants l.i
    returns _:unit
    ensures inv l.i (exists* (p:perm). L.lock_active #p l.l) **
            (exists* (p:perm). L.lock_active #p l.l) {
    L.share_lock_active l.l
  };

  T.recall l.t1;
  with p. assert (L.lock_active #p l.l);
  L.elim_inv_and_active_into_alive l.l v #p;
  elim_stick _ _;
  drop_ (inv _ _)
}
```

```pulse
fn acquire (#v:vprop) (l:lock v)
  requires emp
  ensures v ** lock_acquired l
{
  lock_alive l;
  with p. assert (L.lock_alive l.l #p v);
  L.acquire l.l;
  fold (lock_acquired l);
  drop_ (L.lock_alive l.l #p v)
}
```

```pulse
fn release (#v:vprop) (l:lock v)
  requires v ** lock_acquired l
  ensures emp
{
  lock_alive l;
  with p. assert (L.lock_alive l.l #p v);
  unfold (lock_acquired l);
  L.release l.l;
  drop_ (L.lock_alive l.l #p v)
}
```
