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

module IntroGhost
#lang-pulse
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

(* 
  invariant pattern makes the condition var b 
  a ghost var, making it impossible to infer the
  entry condition to the loop because the condition
  var outside the loop is not ghost
*)
let my_inv (b:bool) (r:R.ref int) : slprop
  = exists* v.
      R.pts_to r v ** 
      pure ( b == (v = 0) )
    

[@@expect_failure]

fn invar_introduces_ghost (r:R.ref int)
  requires R.pts_to r 0
  ensures R.pts_to r 1
{
  r := 0;

  fold (my_inv true r);

  while (let vr = !r; (vr = 0))
  invariant b. my_inv b r  // FAILS: trying to prove: my_inv (reveal (hide true)) r
                           // but typing context has: my_inv true r
  {
    r := 1;
  };

  ()
}


(* 
  intro exists* pattern exhibits the 
  same issue as the invariant pattern 
*)
[@@expect_failure]

fn exists_introduces_ghost (r:R.ref int)
  requires R.pts_to r 0
  ensures R.pts_to r 0
{
  r := 0;

  fold (my_inv true r);

  introduce exists* b. (my_inv b r) with _;  // FAILS: trying to prove: my_inv (reveal (hide true)) r
                                            // but typing context has: my_inv true r
  ()
}


(* 
  building on above example: providing a witness 
  helps but then we lose access to the witness
*)
[@@expect_failure]

fn exists_with_witness_introduces_ghost (r:R.ref int)
  requires R.pts_to r 0
  ensures R.pts_to r 0
{
  r := 0;

  fold (my_inv true r);

  introduce exists* b. (my_inv b r) with true; // this is OK but then we lose access
                                              // to witness b=true

  assert (my_inv true r); // FAILS
  unfold (my_inv true r);
  ()
}


(* 
  building on above example: this checks! 
  use the with...assert... pattern to maintain the witness 
*)

fn with_assert_OK (r:R.ref int)
  requires R.pts_to r 0
  ensures R.pts_to r 0
{
  r := 0;

  fold (my_inv true r);

  with b. assert (my_inv b r); // similar to above but we don't lose access
                               // to witness b=true because with...assert... 
                               // puts b=true into the typing context

  assert (my_inv true r);
  unfold (my_inv true r);
  ()
}
