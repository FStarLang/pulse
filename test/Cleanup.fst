module Cleanup
#lang-pulse
open Pulse
module V = Pulse.Lib.Vec

fn without_cleanup (x: bool) {
  let v = V.alloc 1uy 10sz;
  if (x) {
    V.free v;
    return;
  };
  V.free v;
}

fn with_cleanup (x: bool) {
  let v = V.alloc 1uy 10sz;
  cleanup (V.pts_to v (Seq.create 10 1uy)) { V.free v };
  if (x) {
    return;
  };
}