module Demo.VSS2025
open FStar.Mul

/// F* enables basic functional programming, like F# or OCaml etc.
let rec map (f:'a -> 'b) (l:list 'a)
  : list 'b
  = match l with
    | [] -> []
    | hd::tl -> f hd :: map f tl

let rec foldr (f:'a -> 'b -> 'b) (l:list 'a) (x:'b)
= match l with
  | [] -> x
  | hd::tl -> f hd (foldr f tl x)

/// But, you can prove properties about your code
/// This assert is checked at compile time
let _ = assert (map (fun x -> x + 1) [1;2;3] == [2;3;4])

/// E.g., this fails to compile
[@@expect_failure]
let _ = assert (map (fun x -> x / 2) [1;2;3] == [2;3])

let ( <.> ) (g:'b -> 'c) (f:'a -> 'b) : 'a -> 'c
= fun x -> g (f x)

let rec map_fold_fusion (l:list 'a) (g: 'a -> 'b) (f: 'b -> 'c -> 'c) (i:'c)
: Lemma (foldr f (map g l) i == foldr (f <.> g) l i)
= match l with
  | [] -> ()
  | hd::tl -> map_fold_fusion tl g f i

////////////////////////////////////////////////////////////////////////////////////////
// PULSE
// Programming and proving with mutable stae and shared memory concurrency
////////////////////////////////////////////////////////////////////////////////////////

#lang-pulse
open Pulse.Lib
open Pulse.Lib.Pervasives

fn incr (x:ref int)
requires pts_to x 'i
ensures pts_to x ('i + 1)
{
    let v = !x;
    x := v + 1;
}

fn swap #a (x y:ref a)
requires pts_to x 'v0 ** pts_to y 'v1
ensures pts_to x 'v1 ** pts_to y 'v0
{
    let v0 = !x;
    let v1 = !y;
    x := v1;
    y := v0;
}

// Mutable references are stack allocated and reclaimed implicitly
fn alloc_and_swap ()
requires emp
ensures emp
{
  let mut x = 0;
  let mut y = 1;
  swap x y;
}

// Heap allocated references are called boxes
fn alloc_box ()
requires emp
returns r:(Box.box int & Box.box int)
ensures Box.pts_to r._1 0 ** Box.pts_to r._2 1
{
  let x = Box.alloc 0;
  let y = Box.alloc 1;
  (x, y)
} 

fn free_box (r:Box.box int)
requires Box.pts_to r 'v
ensures emp
{
  Box.free r
}

fn swap_box (r0 r1:Box.box int)
requires Box.pts_to r0 'v0 ** Box.pts_to r1 'v1
ensures Box.pts_to r0 'v1 ** Box.pts_to r1 'v0
{
  Box.to_ref_pts_to r0;
  Box.to_ref_pts_to r1;
  swap (Box.box_to_ref r0) (Box.box_to_ref r1);
  Box.to_box_pts_to r0;
  Box.to_box_pts_to r1;
}

///////////////////////////////////////////////////////////////
// Pure F* functions are refined by imperative Pulse programs
///////////////////////////////////////////////////////////////
let max_spec x y = if x < y then y else x

fn max #p #q (x y:ref int)
requires pts_to x #p 'vx ** pts_to y #q 'vy
returns n:int
ensures 
  pts_to x #p 'vx **
  pts_to y #q 'vy **
  pure (n == max_spec 'vx 'vy)
{
    let vx = !x;
    let vy = !y;
    if (vx > vy) { vx } else { vy }
}

fn multiply_by_repeated_addition (x y:nat)
    requires emp
    returns z:nat
    ensures pure (z == x * y)
{
    let mut ctr = 0;
    let mut acc = 0;
    while (
        let c = !ctr;
        (c < x)
    )
    invariant guard_condition.
    exists* c a.
        pts_to ctr c **
        pts_to acc a **
        pure (c <= x /\
              a == (c * y) /\
              guard_condition == (c < x))
    {
        let a = !acc;
        let c = !ctr;
        acc := a + y;
        ctr := c + 1;
    };
    let res = !acc;
    res
}

// Fibonacci numbers
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
