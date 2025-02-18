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
module Example.MutableSlice
#lang-pulse
open Pulse
open Pulse.Lib.Trade
open Pulse.Lib.MutableSlice.Util
module A = Pulse.Lib.Array
module UInt8 = FStar.UInt8
module S = Pulse.Lib.Slice
module Trade = Pulse.Lib.Trade.Util

fn test (arr: A.array UInt8.t)
    requires pts_to arr seq![0uy; 1uy; 2uy; 3uy; 4uy; 5uy]
    returns res: UInt8.t
    ensures exists* s. pts_to arr s ** pure (s `Seq.equal` seq![0uy; 5uy; 4uy; 5uy; 4uy; 5uy]) {
  A.pts_to_len arr;
  let slice = from_array arr 6sz;
  let s' = split slice 2sz;
  match s' {
    Mktuple2 s1 s2 -> {
      pts_to_len s1;
      share s2;
      let s2' = subslice_trade s2 1sz 4sz;
      let x = s2'.(len s1);
      s1.(1sz) <- x;
      elim_trade _ _;
      gather s2;
      let s' = split s2 2sz;
      match s' {
        Mktuple2 s3 s4 -> {
          pts_to_len s3;
          pts_to_len s4;
          let s4' = to_slice s4;
          S.pts_to_len s4';
          copy s3 s4';
          Trade.elim (pts_to s4' _) _;
          let y = s3.(0sz);
          let z = s4.(0sz);
          join s3 s4 s2;
          join s1 s2 slice;
          to_array slice;
          (x `UInt8.add` y `UInt8.add` z)
        }
      }
    }
  }
}
