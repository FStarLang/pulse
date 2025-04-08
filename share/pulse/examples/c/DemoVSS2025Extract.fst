module Demo.VSS2025Extract
#lang-pulse
open FStar.Mul
open Pulse.Lib
open Pulse.Lib.Pervasives

// Fibonacci numbers
noextract
let rec fib (n:nat) : nat =
  if n <= 1 then 1
  else fib (n - 1) + fib (n - 2)

let rec fib_mono (n:nat) (m:nat { m <= n})
  : Lemma
    (ensures fib m <= fib n)
  = if n = m then ()
    else fib_mono (n - 1) m

open FStar.UInt32
open Pulse.Lib.BoundedIntegers
module U32 = FStar.UInt32

fn fibonacci32 (k:U32.t)
  requires pure (0ul < k /\ fib (v k) < pow2 32)
  returns r:U32.t
  ensures pure (v r == fib (v k))
{
  let mut i = 1ul;
  let mut j = 1ul;
  let mut ctr = 1ul;
  while (
    let c = !ctr;
    (c < k)
  )
  invariant b . 
    exists* (vi vj vctr:U32.t). 
     pts_to i vi **
     pts_to j vj **
     pts_to ctr vctr **
     pure (1ul <= vctr /\
           vctr <= k /\
           fib (v (vctr - 1ul)) == v vi/\
           fib (v vctr) == v vj /\
           b == (vctr < k))
  {
     let vi = !i;
     let vj = !j;
     let c = !ctr;
     fib_mono (v k) (v c + 1);
     ctr := c + 1ul;
     i := vj;
     j := vi + vj;
  };
  !j
}
