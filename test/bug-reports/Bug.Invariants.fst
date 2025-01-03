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

module Bug.Invariants
#lang-pulse
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32


atomic
fn return_atomic
      (x:ref U32.t)
requires emp ** pts_to x 1ul
returns n:U32.t
ensures emp ** pts_to x 1ul
{
    read_atomic x;
}



atomic
fn return_atomic2 (x:ref U32.t)
requires emp ** pts_to x 1ul
returns n:U32.t
ensures emp ** pts_to x 1ul
{
    0ul;
}




ghost
fn ghost_step ()
requires emp
ensures emp
{
    ()
}


assume
val atomic_step (_:unit) : stt_atomic unit emp_inames emp (fun _ -> emp)


fn ghost_then_atomic ()
requires emp
ensures emp
{
    ghost_step();
    atomic_step();
}


assume
val atomic_step_res (_:unit) : stt_atomic bool emp_inames emp (fun _ -> emp)


fn ghost_then_atomic_bool ()
requires emp
returns b:bool
ensures emp
{
    ghost_step();
    atomic_step_res();
}



fn ghost_then_atomic_bool2 ()
requires emp
returns b:bool
ensures emp
{
    ghost_step();
    let b = atomic_step_res();
    ghost_step();
    b
}



fn return_with_invariant
      (p:slprop)
      (i:iname)
requires inv i p
returns x:bool
ensures inv i p
{
    with_invariants i { 
      atomic_step_res();
    }
}



fn return_with_invariant2
      (x:ref U32.t)
      (i:iname)
requires inv i (pts_to x 1ul)
returns _:U32.t
ensures inv i (pts_to x 1ul)
{
    with_invariants i {
        later_elim_timeless _;
        let r = read_atomic x;
        later_intro (pts_to x 1ul);
        r
    }
}



fn test_invariant_annot (x:ref U32.t) (i:iname) (y:ref U32.t)
requires inv i (pts_to x 0ul) ** pts_to y 'w
ensures inv i (pts_to x 0ul) ** pts_to y 0ul
{
    let n = 
        with_invariants i
        returns r:U32.t
        ensures later (pts_to x 0ul) ** pure (r == 0ul) ** pts_to y 'w
        opens [i] {
            later_elim_timeless _;
            let r = read_atomic x;
            later_intro (pts_to x 0ul);
            r
        };
    y := n;
}

