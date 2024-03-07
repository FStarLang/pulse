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

let pts_to_anchored
  (#a:Type) (#p:_) (#anc:anchor_rel p)
  (r:ref a p anc)
  (#[T.exact (`full_perm)] f:perm)
  (n:a)
  = pure (anc n n) ** 
    (assume (anc n n); // limitation, should be true by the previous resource
     ghost_pcm_pts_to #_ #_ r (FRAP.Owns ((Some f, Some n), [n])))

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
