module Bug357

#lang-pulse
open Pulse.Nolib

type t2 =
  | C : x:int -> y:int{x > y} -> t2

assume val foo : t2 -> slprop

fn test1 (x : t2)
  requires foo x
  ensures  foo x
{
  match x {
    norewrite C y z -> {
      let foo = z;
      rewrite each x as C y z;
      ();
    }
  }
}

fn test11 (x : t2)
  requires foo x
  ensures  foo x
{
  match x {
    y -> {
      ();
    }
  }
}

fn test2 (x : t2)
  requires foo x
  ensures  foo x
{
  match x {
    C y z -> {
      ();
    }
  }
}

fn test3 (x : t2)
  requires foo x
  ensures  foo x
{
  norewrite let C y z = x;
  ();
}

fn test4 (x : t2)
  requires foo x
  ensures  foo x
{
  let C y z = x;
  ();
}
