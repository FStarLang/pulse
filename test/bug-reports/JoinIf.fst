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

module JoinIf
#lang-pulse
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
open FStar.UInt32

let sorted (s0 s:Seq.seq U32.t) =
   (forall (i:nat). i < Seq.length s - 1 ==> U32.v (Seq.index s i) <= U32.v (Seq.index s (i + 1))) /\
   (forall (i:nat). i < Seq.length s0 ==> (exists (j:nat). j < Seq.length s /\ U32.v (Seq.index s0 i) == U32.v (Seq.index s j)))

//Pulse does not yet implement join point inference
[@@expect_failure [228]]

fn sort3_alt (a:array U32.t)
             (#s:(s:Ghost.erased (Seq.seq U32.t) {Seq.length s == 3}))
   requires (A.pts_to a s)
   ensures 
      exists* s'. (
         A.pts_to a s' **
         pure (sorted s s')
      )
{
   let mut x = a.(0sz);
   let mut y = a.(1sz);
   let mut z = a.(2sz);
   let vx = !x;
   let vy = !y;
   if (vy <^ vx) 
   {
      x := vy;
      y := vx;
   };
   let vx = !x;
   let vz = !z;
   if (vz <^ vx)
   {
      x := vz;
      z := vx;
   };
   let vy = !y;
   let vz = !z;
   if (vz <^ vy)
   {
      y := vz;
      z := vy;
   };
   (a.(0sz) <- x);
   (a.(1sz) <- y);
   (a.(2sz) <- z);
   ()
}


//But, an explicitly annotated version doesn't work either
[@@expect_failure]
fn sort3_alt (a:array U32.t)
             (#s:(s:Ghost.erased (Seq.seq U32.t) {Seq.length s == 3}))
   requires (A.pts_to a s)
   ensures 
      exists* s'. (
         A.pts_to a s' **
         pure (sorted s s')
      )
{
   let mut x = a.(0sz);
   let mut y = a.(1sz);
   let mut z = a.(2sz);
   let vx = !x;
   let vy = !y;
   if (vy <^ vx) //Fails to typecheck the join annotation, claiming vy has type vy has type stt U32.t ... instead of just U32.t
   ensures (
    R.pts_to x (if vy <^ vx then vy else vx) **
    R.pts_to y (if vy <^ vx then vx else vy)
   )
   {
      x := vy;
      y := vx;
   };
   let vx = !x;
   let vz = !z;
   if (vz <^ vx)
   ensures (
    R.pts_to x (if vz <^ vx then vz else vx) **
    R.pts_to z (if vz <^ vx then vx else vz)
   )
   {
      x := vz;
      z := vx;
   };
   let vy = !y;
   let vz = !z;
   if (vz <^ vy)
   ensures (
    R.pts_to y (if vz <^ vy then vz else vy) `star`
    R.pts_to z (if vz <^ vy then vy else vz)
   )
   {
      y := vz;
      z := vy;
   };
   (a.(0sz) <- x);
   (a.(1sz) <- y);
   (a.(2sz) <- z);
   ()
}
