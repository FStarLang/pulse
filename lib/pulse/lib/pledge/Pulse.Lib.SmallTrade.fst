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

module Pulse.Lib.SmallTrade

open FStar.Ghost
open Pulse.Lib.Core
open Pulse.Lib.InvList

module T = FStar.Tactics

type small_slprop = v:slprop { is_slprop2 v }

let trade_elim_t (is:invlist) (hyp:slprop) (extra:small_slprop) (concl:slprop) : Type u#4 =
  unit -> stt_ghost unit (invlist_names is) (invlist_inv is ** extra ** hyp) (fun _ -> invlist_inv is ** concl)

let trade_elim_exists (is:invlist) (hyp:slprop) (extra:small_slprop) (concl:slprop) : slprop =
  pure (squash (trade_elim_t is hyp extra concl))

let __trade (#is:invlist) (hyp concl:slprop) : small_slprop =
  exists* (extra:small_slprop). extra ** trade_elim_exists is hyp extra concl

let trade #is hyp concl : slprop = __trade #is hyp concl

let trade_is_slprop2 (#is:invlist) (hyp concl:slprop)
  : Lemma (is_slprop2 (trade #is hyp concl)) = ()

```pulse
ghost
fn intro_trade
  (#is:invlist)
  (hyp concl:slprop)
  (extra:slprop { is_slprop2 extra })
  (f_elim:unit -> (
    stt_ghost unit (invlist_names is)
    (invlist_inv is ** extra ** hyp)
    (fun _ -> invlist_inv is ** concl)
  ))
  requires extra
  ensures trade #is hyp concl
{
  fold (trade_elim_exists is hyp extra concl);
  assert (extra ** trade_elim_exists is hyp extra concl); // FIXME: why is this needed? somehow guiding the prover?
  fold (__trade #is hyp concl);
  fold (trade #is hyp concl)
}
```

```pulse
ghost
fn intro_trade_invs
  (#is:invlist)
  (hyp concl:slprop)
  (extra:slprop { is_slprop2 extra })
  (f_elim:unit -> (
    stt_ghost unit emp_inames
      (invlist_v is ** extra ** hyp)
      (fun _ -> invlist_v is ** concl)
  ))
  requires extra
  ensures trade #is hyp concl
{
  ghost
  fn aux ()
    requires invlist_inv is ** extra ** hyp
    ensures invlist_inv is ** concl
    opens (invlist_names is)
  {
    ghost
    fn aux ()
      requires invlist_v is ** (extra ** hyp)
      ensures invlist_v is ** concl
    {
      f_elim ()
    };
    with_invlist is aux
  };

  intro_trade hyp concl extra aux
}
```

let sqeq (p : Type) (_ : squash p) : erased p =
  FStar.IndefiniteDescription.elim_squash #p ()

let psquash (a:Type u#a) : prop = squash a

```pulse
ghost
fn pextract (a:Type u#4) (_:squash a)
requires emp
returns i:a
ensures emp
{
  let pf = elim_pure_explicit (psquash a);
  let pf : squash a = FStar.Squash.join_squash pf;
  let i = sqeq a pf;
  let i = reveal i;
  i
}
```

```pulse
ghost
fn deconstruct_trade (is:invlist) (hyp concl:slprop)
  requires trade #is hyp concl
  returns res:(extra:erased small_slprop & trade_elim_t is hyp (reveal extra) concl)
  ensures reveal (dfst res)
{
  unfold (trade #is hyp concl);
  unfold (__trade #is hyp concl);
  with (extra:small_slprop). assert (extra ** trade_elim_exists is hyp extra concl);
  unfold (trade_elim_exists is hyp (reveal extra) concl);
  let pf : squash (psquash (trade_elim_t is hyp (reveal extra) concl)) =
    elim_pure_explicit (psquash (trade_elim_t is hyp (reveal extra) concl));
  let pf : squash (trade_elim_t is hyp (reveal extra) concl) =
    FStar.Squash.join_squash pf;
  let f = pextract (trade_elim_t is hyp (reveal extra) concl) pf;
  let res =
    (| (extra <: erased small_slprop), f |) <: (p:erased small_slprop & trade_elim_t is hyp (reveal p) concl);
  rewrite extra as (dfst res);
  res
}
```

```pulse
ghost
fn elim_trade
  (#is:invlist)
  (hyp concl:slprop)
  requires invlist_inv is ** trade #is hyp concl ** hyp
  ensures invlist_inv is ** concl
  opens (invlist_names is)
{
  let res = deconstruct_trade is hyp concl;
  let f = dsnd res;
  f ()
}
```

```pulse
ghost
fn trade_sub_inv
  (#is1:invlist)
  (#is2:invlist { invlist_sub is1 is2 })
  (hyp concl:slprop)
  requires trade #is1 hyp concl
  ensures trade #is2 hyp concl
{
  let res = deconstruct_trade is1 hyp concl;

  ghost
  fn aux ()
    requires invlist_inv is2 ** dfst res ** hyp
    ensures invlist_inv is2 ** concl
    opens (invlist_names is2)
  {
    invlist_sub_inv is1 is2;
    let f = dsnd res;
    f ();
    Pulse.Lib.Priv.Trade0.elim_stick (invlist_inv is1) (invlist_inv is2)
  };
  
  intro_trade #is2 hyp concl (reveal (dfst res)) aux
}
```

```pulse
ghost
fn trade_map
  (#os : invlist)
  (p q r : slprop)
  (f : unit -> stt_ghost unit emp_inames q (fun _ -> r))
  requires trade #os p q
  ensures trade #os p r
{
  ghost
  fn aux ()
    requires (invlist_inv os ** trade #os p q) ** p
    ensures  (invlist_inv os ** r)
    opens (invlist_names os)
  {
    elim_trade #os p q;
    f ();
  };
  intro_trade #os p r (trade #os p q) aux;
}
```

```pulse
ghost
fn trade_compose
  (#os : invlist)
  (p q r : slprop)
  requires trade #os p q ** trade #os q r
  ensures trade #os p r
{
  ghost
  fn aux ()
    requires (invlist_inv os ** (trade #os p q ** trade #os q r)) ** p
    ensures  (invlist_inv os ** r)
    opens (invlist_names os)
  {
    elim_trade #os p _;
    elim_trade #os _ _;
  };
  slprop2_star (trade #os p q) (trade #os q r);
  intro_trade #os p r (trade #os p q ** trade #os q r) aux;
}
```
