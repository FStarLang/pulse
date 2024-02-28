(*
   Copyright 2021 Microsoft Research

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
module Pulse.Lib.FractionalPreorder

open FStar.PCM
open FStar.Preorder
open PulseCore.Preorder
open PulseCore.FractionalPermission

module L = FStar.List.Tot

type pcm_carrier (#a:Type) (p:preorder a) = option perm & hist p

let pcm_composable (#a:Type) (p:preorder a) : symrel (pcm_carrier p) =
  fun x0 x1 ->
  match x0, x1 with
  | (None, t0), (None, t1) -> t0 `extends` t1 \/ t1 `extends` t0
  | (Some _, t0), (None, t1) -> t0 `extends` t1
  | (None, t0), (Some _, t1) -> t1 `extends` t0
  | (Some p0, t0), (Some p1, t1) ->
    t0 == t1 /\
    sum_perm p0 p1 `lesser_equal_perm` full_perm

let pcm_op (#a:Type) (p:preorder a)
  (x:pcm_carrier p)
  (y:pcm_carrier p { pcm_composable p x y })
  : pcm_carrier p =

  match x, y with
  | (None, t0), (None, t1) -> None, p_op p t0 t1
  | (Some _, _), (None, _) -> x
  | (None, _), (Some _, _) -> y
  | (Some p0, t0), (Some p1, t1) -> Some (sum_perm p0 p1), t0

let pcm_one (#a:Type) (p:preorder a) : pcm_carrier p = None, []

let fp_pcm' (#a:Type) (p:preorder a) : pcm' (pcm_carrier p) = {
  composable = pcm_composable p;
  op = pcm_op p;
  one = pcm_one p;
}

let fp_lem_commutative (#a:Type) (p:preorder a) : lem_commutative (fp_pcm' p) =
  fun x y -> ()

let fp_lem_assoc_l (#a:Type) (p:preorder a) : lem_assoc_l (fp_pcm' p) =
  fun x y z -> ()

let fp_lem_assoc_r (#a:Type) (p:preorder a) : lem_assoc_r (fp_pcm' p) =
  fun x y z -> ()

let rec extends_nil (#a:Type) (#p:preorder a) (l:hist p)
  : Lemma (l `extends` []) =

  match l with
  | [] -> ()
  | _::tl -> extends_nil #a #p tl

let fp_lem_is_unit (#a:Type) (p:preorder a) : FStar.PCM.lem_is_unit (fp_pcm' p) =
  fun x ->
  match x with
  | Some _, t -> extends_nil t
  | None, t -> p_op_nil p t

let fp_pcm (#a:Type) (p:preorder a) : pcm (pcm_carrier p) = {
  p = fp_pcm' p;
  comm = fp_lem_commutative p;
  assoc = fp_lem_assoc_l p;
  assoc_r = fp_lem_assoc_r p;
  is_unit = fp_lem_is_unit p;
  refine = (fun (p, _) -> p == Some full_perm);
}
