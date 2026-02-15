module ArrayPtsTo
#lang-pulse
open Pulse
module A = Pulse.Lib.Array.PtsTo

fn test (a: A.array UInt32.t) (#s: Ghost.erased (Seq.seq UInt32.t) { Seq.length s == 2 })
  requires A.pts_to a s
  returns r: UInt32.t
  ensures exists* s'. A.pts_to a s' ** pure (s' `Seq.equal` Seq.upd s 0 42ul)
  ensures rewrites_to r (Seq.index s 1)
{
  a.(0sz) <- 42ul;
  a.(1sz)
}
