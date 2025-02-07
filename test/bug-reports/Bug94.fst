module Bug94

#lang-pulse
open Pulse

[@@expect_failure [19]]
fn foo ()
  requires emp
  ensures  emp
{
  let x : nat = -1;
  ()
}

[@@expect_failure [189]]
fn foo (y:string)
  requires emp
  ensures  emp
{
  let x : nat = y;
  ()
}

let divide
  (a: erased int)
  (b: erased int { reveal b <> 0 })
  : GTot (erased int) = a / b

[@@expect_failure [19]]
fn divide_test ()
  requires emp
  ensures emp
{
    let hundred = divide 100;
    ();
    let unknown = hundred 0;
    ()
}
