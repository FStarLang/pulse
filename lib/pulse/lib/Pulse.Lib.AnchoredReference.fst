module Pulse.Lib.AnchoredReference

open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
open FStar.Preorder
open Pulse.Lib.FractionalAnchoredPreorder

module U32 = FStar.UInt32
module T = FStar.Tactics
module FRAP = Pulse.Lib.FractionalAnchoredPreorder

[@@erasable]
let ref ([@@@unused]a:Type u#0) (p : preorder a) (anc : anchor_rel p) : Type u#0
  = ghost_pcm_ref (FRAP.pcm #a #p #anc)

let revealer_ref (a:Type u#0) (p : preorder a) (anc : anchor_rel p) 
: Pulse.Lib.NonInformative.revealer (ref a p anc)
= fun (r:erased (ref a p anc)) -> reveal r

let ref_non_informative (a:Type u#0) (p : preorder a) (anc : anchor_rel p)
: NonInformative.non_informative (ref a p anc)
= let open Pulse.Lib.NonInformative in
  { reveal = revealer_ref a p anc }

let pts_to_full #a #p #anc
    (r:ref a p anc) 
    (#[T.exact (`full_perm)] p:perm)
    (n:a)
: vprop
= ghost_pcm_pts_to_full r p n
