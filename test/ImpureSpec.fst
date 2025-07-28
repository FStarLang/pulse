module ImpureSpec
open Pulse
open Pulse.Lib.Trade
#lang-pulse

fn test1 () {
  let mut x = 2;
  let mut y = x;
  assert pure (!(!y) == 2);
}

// #push-options "--print_implicits"
// fn test2 (p: array int -> slprop) {
//   let mut a = [| 0; 2sz |];
//   let mut b = [| 0; 2sz |];
//   pts_to_len a;
//   pts_to_len b;
//   let mut i = 0;
//   assert pure (length a == 2 /\ !i < length a /\
//       length a == length b /\
//       (forall (j: SizeT.t). SizeT.v j < !i ==> a.(j) == b.(j))) ** ((exists* v. a |-> v) @==> p a)
//                                         Seq.index va (SizeT.v j) == Seq.index vb (SizeT.v j)
// }
//
// [@@pulse_unfold]
// let live #t (x:t) {| pts_to t |} = exists* vx. x |-> vx
//
//
// preserves live x
// requires live y
// ensures pure (!x > 42 + old(!x))
//
//
// ensures no_extrude (exists* vx. x |-> Frac p vx)
// ensures live #p vx
// ensures pure (!x > 10)
//
//
// live x ** pure (!x > 42)
// --->
// (exists* vx. x |-> vx) ** pure (!x > 42)
// --->
// exists* vx. ((x |-> vx) ** pure (vx > 42))
//
