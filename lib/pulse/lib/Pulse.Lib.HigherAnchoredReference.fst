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

module Pulse.Lib.HigherAnchoredReference
open Pulse.Lib.Core
open Pulse.Main
open FStar.PCM
module FRAP = Pulse.Lib.FractionalAnchoredPreorder

let ref (a:Type u#1) (p:preorder a) (anc:anchor_rel p) =
  ghost_pcm_ref (FRAP.pcm #a #p #anc)

let revealer_ref (a:Type) (p : preorder a) (anc : anchor_rel p) 
: Pulse.Lib.NonInformative.revealer (ref a p anc)
= fun (r:erased (ref a p anc)) -> reveal r

let ref_non_informative (a:Type) (p : preorder a) (anc : anchor_rel p)
: NonInformative.non_informative (ref a p anc)
= let open Pulse.Lib.NonInformative in
  { reveal = revealer_ref a p anc }

let perm_of #a (#p:preorder a) (#anc:anchor_rel p) (av:FRAP.avalue anc)
: option perm 
= fst (fst av)

let has_value  #a (#p:preorder a) (#anc:anchor_rel p) (av:FRAP.avalue anc)
: bool
= Cons? (snd av)

let value_of #a (#p:preorder a) (#anc:anchor_rel p)
      (av:FRAP.avalue anc { has_value av })
: a
= PulseCore.Preorder.curval (snd av)

let owns_pred
    (#a:Type u#1)
    (#p:preorder a)
    (#anc:anchor_rel p)
    (f:perm)
    (n:a)
    (with_anchor:bool)
    (av:FRAP.avalue anc)
: prop
= (with_anchor <==> FRAP.has_anchor (fst av)) /\
  perm_of av == Some f /\
  has_value av /\
  n == value_of av

let owns_pred_without_anchor
    (#a:Type u#1)
    (#p:preorder a)
    (#anc:anchor_rel p)
    (n:a)
    (av:FRAP.avalue anc)
: Lemma
  (requires owns_pred full_perm n false av)
  (ensures FRAP.avalue_owns_anchored av)
= ()

let owns_pred_with_anchor
    (#a:Type u#1)
    (#p:preorder a)
    (#anc:anchor_rel p)
    (n:a)
    (av:FRAP.avalue anc)
: Lemma
  (requires owns_pred full_perm n true av)
  (ensures FRAP.avalue_owns av)
= ()

let split_fraction 
    (#a:Type u#1)
    (#p:preorder a)
    (#anc:anchor_rel p)
    (f0 f1:perm)
    (n:a)
    (av:FRAP.avalue anc {
      owns_pred (sum_perm f0 f1) n false av
    })
: res:(FRAP.avalue anc & FRAP.avalue anc) {
    owns_pred f0 n false (fst res) /\
    owns_pred f0 n false (snd res) /\
    FRAP.avalue_composable (fst res) (snd res) /\
    FRAP.compose_avalue (fst res) (snd res) == av
  } 
= admit()

let split_anchor
    (#a:Type u#1)
    (#p:preorder a)
    (#anc:anchor_rel p)
    (f:perm)
    (n:a)
    (av:FRAP.avalue anc {
      owns_pred f n true av
    })
: res:(FRAP.avalue anc & FRAP.avalue anc) {
    owns_pred f0 n false (fst res) /\
    owns_pred f0 n false (snd res) /\
    FRAP.avalue_composable (fst res) (snd res) /\
    FRAP.compose_avalue (fst res) (snd res) == av
  } 
= admit()

let split_fraction_lemma
    (#a:Type u#1)
    (#p:preorder a)
    (#anc:anchor_rel p)
    (f0 f1:perm)
    (n:a)
    (av:FRAP.avalue anc)
: Lemma
  (requires owns_pred (sum_perm f0 f1) n false av)
  (ensures True)
= admit()

let owns #a #p #anc
    (r:ref a p anc)
    (#[T.exact (`full_perm)] f:perm)
    (n:a)
    (with_anchor:bool)
: vprop
= exists* v. 
    ghost_pcm_pts_to r v **
    pure (Owns? v /\ owns_pred f n with_anchor (Owns?._0 v))


let pts_to
  (#a:Type) (#p:_) (#anc:anchor_rel p)
  (r:ref a p anc)
  (#[T.exact (`full_perm)] f:perm)
  (n:a)
  = exists* (hist : PulseCore.Preorder.vhist p).
      ghost_pcm_pts_to #_ #_ r (FRAP.Owns ((Some f, None), hist)) **
      pure (Cons? hist /\ Cons?.hd hist == n)

let anchored
  (#a:Type) (#p:_) (#anc:anchor_rel p)
  (r:ref a p anc)
  (n:a)
  = exists* (hist : PulseCore.Preorder.vhist p).
      ghost_pcm_pts_to #_ #_ r (FRAP.Owns ((None, None), hist)) **
      pure (Cons? hist /\ Cons?.hd hist == n)

```pulse
ghost
fn alloc' (#a:Type u#1) (x:a) (#p:preorder a) (#anc:anchor_rel p)
  requires pure (anc x x)
  returns r:ref a p anc
  ensures pts_to_anchored r x
{
  let r = Pulse.Lib.Core.ghost_alloc #_ #(FRAP.pcm #a #p #anc)
             (FRAP.Owns (FRAP.initial_value x));
  fold (pts_to_anchored r #full_perm x);
  r
}
```
let alloc = alloc'

// #set-options "--debug Pulse.Lib.AnchoredReference --debug_level SMTQuery --split_queries always --log_failing_queries"

let v_owns #a #p #anc (k : knowledge #a #p anc{Owns? k}) : GTot a =
  match k with
  | Owns av -> PulseCore.Preorder.curval (snd av)

let extract #a (#p : pcm a) (x:a) (v:a{compatible p x v})
: GTot (y:a{compatible p y v /\ frame_compatible p x v y})
=
  x

```pulse
ghost
fn read' (#a:Type u#1) (#p:preorder a) (#anc:anchor_rel p) (r : ref a p anc) (#f:perm) (#v:erased a)
  requires pts_to r #f v
  returns  w :  (w:a{p v w})
  ensures  pts_to r #f w
{
  unfold (pts_to r #f v);
  with vv. assert (ghost_pcm_pts_to r vv);
  let res = Pulse.Lib.Core.ghost_read r vv (fun _ -> vv);
  let b = FRAP.Owns? res;
  if b {
    let w = v_owns res;
    fold (pts_to r #f v);
    w
  } else {
    unreachable ()
  }
}
```
let read #a #p #anc = read' #a #p #anc

#set-options "--print_implicits"
```pulse
ghost
fn write' (#a:Type u#1) (#p:preorder a) (#anc:anchor_rel p) (r : ref a p anc) (#f:perm) (#v:erased a) (v':erased a{p v v'})
  requires pts_to r #f v
  returns  _:unit
  ensures  pts_to r #f v'
{
  admit();
  // unfold (pts_to r #f v);
  // with vv. assert (ghost_pcm_pts_to r vv);
  // let b = FRAP.Owns? vv;
  // if b {
  //   let hist = (match vv with | Owns (_, hist) -> hist);
  //   Pulse.Lib.Core.ghost_write r vv (FRAP.Owns ((Some f, None), v' :: hist)) (magic());
  //   rewrite ghost_pcm_pts_to r (reveal (hide (FRAP.Owns ((Some f, None), v' :: hist))))
  //        as ghost_pcm_pts_to r (FRAP.Owns ((Some f, None), v' :: hist));
  //   fold (pts_to r #f v');
  //   show_proof_state;
  //   ()
  // } else {
  //   unreachable ()
  // };
}
```
let write = admit()
