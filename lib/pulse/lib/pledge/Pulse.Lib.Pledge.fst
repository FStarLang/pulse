(*
   Copyright REDACTED

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

module Pulse.Lib.Pledge

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module GR = Pulse.Lib.GhostReference

open FStar.Tactics.V2

let slprop_equiv_refl_eq (v1 v2 : slprop) (_ : squash (v1 == v2)) : slprop_equiv v1 v2 =
  slprop_equiv_refl v1

let __tac () : Tac unit =
  apply (`slprop_equiv_refl_eq)

let pledge is f v = (==>*) #is f (f ** v)

let pledge_sub_inv is1 is2 (f:slprop) (v:slprop) = trade_sub_inv _ _

```pulse
ghost
fn return_pledge (f v : slprop)
  requires v
  ensures pledge emp_inames f v
{
  ghost
  fn aux ()
    requires v ** f
    ensures f ** v
  {
    ()
  };
  intro_trade #emp_inames f (f ** v) v aux;
  fold ((==>*) #emp_inames f (f ** v));
  fold pledge;
}
```

```pulse
ghost
fn make_pledge
  (is:inames) (f v extra:slprop)
  ($k:unit -> stt_ghost unit is (f ** extra) (fun _ -> f ** v))
  requires extra
  ensures pledge is f v
{
  ghost
  fn aux ()
    requires extra ** f
    ensures f ** v
    opens is
  {
    k ()
  };

  intro_trade #is f (f ** v) extra aux;
  fold ((==>*) #is f (f ** v));
  fold pledge;
}
```

```pulse
ghost
fn redeem_pledge (is:inames) (f v:slprop)
  requires f ** pledge is f v
  ensures f ** v
  opens is
{
  unfold pledge;
  unfold ((==>*) #is f (f ** v));
  elim_trade #is f (f ** v);
}
```

// ```pulse
// ghost
// fn pledge_invs_aux (is:invlist) (f:slprop) (v:slprop)
//   requires pledge is f v
//   ensures pledge is f v ** invlist_inv is
// {
//   unfold pledge;
//   unfold ((==>*) #is f (f ** v));
//   trade_invs ();
//   fold ((==>*) #is f (f ** v));
//   fold pledge
// }
// ```

// let pledge_invs = pledge_invs_aux

```pulse
ghost
fn squash_pledge (is:inames) (f:slprop) (v1:slprop)
  requires pledge is f (pledge is f v1)
  ensures pledge is f v1
{
  ghost
  fn aux ()
    requires f ** pledge is f (pledge is f v1)
    ensures f ** v1
    opens is
  {
    redeem_pledge is f (pledge is f v1);
    redeem_pledge is f v1
  };
  make_pledge is f v1 (pledge is f (pledge is f v1)) aux
}
```

```pulse
ghost
fn bind_pledge
  (#is:inames)
  (#f #v1 #v2 extra:slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k (f ** extra ** v1) (fun _ -> f ** pledge is f v2))
  requires pledge is f v1 ** extra
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires f ** (extra ** pledge is f v1)
    ensures f ** pledge is f v2
    opens is
  {
    redeem_pledge is f v1;
    k ()
  };

  make_pledge is f (pledge is f v2) (extra ** pledge is f v1) aux;
  squash_pledge is f v2
}
```

```pulse
ghost
fn bind_pledge'
  (#is:inames)
  (#f #v1 #v2 extra:slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k (extra ** v1) (fun _ -> pledge is f v2))
  requires pledge is f v1 ** extra
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires f ** extra ** v1
    ensures f ** pledge is f v2
    opens is
  {
    k ()
  };
  bind_pledge #is #f #v1 #v2 extra aux
}
```

```pulse
ghost
fn rewrite_pledge_full
  (#is:inames)
  (#f v1 v2:slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k (f ** v1) (fun _ -> f ** v2))
  requires pledge is f v1
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires f ** pledge is f v1
    ensures f ** v2
    opens is
  {
    redeem_pledge is f v1;
    k ()
  };
  
  make_pledge is f v2 (pledge is f v1) aux;
}
```

```pulse
ghost
fn rewrite_pledge
  (#is:inames)
  (#f v1 v2:slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k v1 (fun _ -> v2))
  requires pledge is f v1
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires f ** v1
    ensures f ** v2
    opens is
  {
    k ()
  };

  rewrite_pledge_full #is #f v1 v2 aux  
}
```

```pulse
ghost
fn join_pledge
  (#is:inames)
  (#f v1 v2:slprop)
  requires pledge is f v1 ** pledge is f v2
  ensures pledge is f (v1 ** v2)
{
  ghost
  fn aux ()
    requires f ** (pledge is f v1 ** pledge is f v2)
    ensures f ** (v1 ** v2)
    opens is
  {
    redeem_pledge is f v1;
    redeem_pledge is f v2;
  };
  
  make_pledge is f (v1 ** v2) (pledge is f v1 ** pledge is f v2) aux;
}
```

```pulse
ghost
fn squash_pledge'
  (is1 is2 is:inames)
  (f v1:slprop)
  requires pure (inames_subset is1 is) **
           pure (inames_subset is2 is) **
           pledge is1 f (pledge is2 f v1)
  ensures pledge is f v1
{
  ghost
  fn aux ()
    requires f ** (pledge is1 f (pledge is2 f v1))
    ensures f ** v1
    opens is
  {
    redeem_pledge is1 f (pledge is2 f v1);
    redeem_pledge is2 f v1
  };
  
  make_pledge is f v1 (pledge is1 f (pledge is2 f v1)) aux
}
```
