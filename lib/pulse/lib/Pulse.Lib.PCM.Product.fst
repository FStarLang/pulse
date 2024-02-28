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
module Pulse.Lib.PCM.Product

module PCM = FStar.PCM

type carrier (a b:Type) = a & b

let composable (#a #b:Type) (pcm_a:PCM.pcm a) (pcm_b:PCM.pcm b)
  : PCM.symrel (carrier a b) =
  
  fun p1 p2 ->
  PCM.composable pcm_a (fst p1) (fst p2) /\
  PCM.composable pcm_b (snd p1) (snd p2)

let op (#a #b:Type) (pcm_a:PCM.pcm a) (pcm_b:PCM.pcm b)
  (p1:carrier a b)
  (p2:carrier a b { composable pcm_a pcm_b p1 p2 })
  : carrier a b =
  
  PCM.op pcm_a (fst p1) (fst p2), PCM.op pcm_b (snd p1) (snd p2)

let one (#a #b:Type) (pcm_a:PCM.pcm a) (pcm_b:PCM.pcm b) =
  pcm_a.p.one, pcm_b.p.one

let pcm_prod (#a #b:Type) (pcm_a:PCM.pcm a) (pcm_b:PCM.pcm b) : PCM.pcm (carrier a b) =
  {
    p = {
      composable = composable pcm_a pcm_b;
      op = op pcm_a pcm_b;
      one = one pcm_a pcm_b;
    };
    comm = (fun p1 p2 ->
      pcm_a.comm (fst p1) (fst p2); pcm_b.comm (snd p1) (snd p2)
    );
    assoc = (fun p1 p2 p3 ->
      pcm_a.assoc (fst p1) (fst p2) (fst p3);
      pcm_b.assoc (snd p1) (snd p2) (snd p3)
    );
    assoc_r = (fun p1 p2 p3 ->
      pcm_a.assoc_r (fst p1) (fst p2) (fst p3);
      pcm_b.assoc_r (snd p1) (snd p2) (snd p3)
    );
    is_unit = (fun p ->
      pcm_a.is_unit (fst p);
      pcm_b.is_unit (snd p)
    );
    refine = (fun p ->
      pcm_a.refine (fst p) /\
      pcm_b.refine (snd p)
    );
  }

let compatible_intro (#a #b:Type) (pcm_a:PCM.pcm a) (pcm_b:PCM.pcm b)
  (x y:carrier a b)
  : Lemma
      (requires
        PCM.compatible pcm_a (fst x) (fst y) /\
        PCM.compatible pcm_b (snd x) (snd y))
      (ensures PCM.compatible (pcm_prod pcm_a pcm_b) x y) =

  let open PCM in
  eliminate exists frame_a. composable pcm_a (fst x) frame_a /\ op pcm_a frame_a (fst x) == fst y
  returns compatible (pcm_prod pcm_a pcm_b) x y
  with _. eliminate exists frame_b. composable pcm_b (snd x) frame_b /\ op pcm_b frame_b (snd x) == snd y
          returns _
          with _. compatible_intro (pcm_prod pcm_a pcm_b) x y (frame_a, frame_b)

let mk_frame_preserving_upd (#a #b:Type) (#pcm_a:PCM.pcm a) (#pcm_b:PCM.pcm b)
  (#x1 #y1:a)
  (upd_a:PCM.frame_preserving_upd pcm_a x1 y1)
  (#x2 #y2:b)
  (upd_b:PCM.frame_preserving_upd pcm_b x2 y2)
  : PCM.frame_preserving_upd (pcm_prod pcm_a pcm_b) (x1, x2) (y1, y2) =

  fun (v1, v2) ->
  let r = upd_a v1, upd_b v2 in
  compatible_intro pcm_a pcm_b (y1, y2) r;
  r
