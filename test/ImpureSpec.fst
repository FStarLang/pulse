module ImpureSpec
open Pulse
#lang-pulse

fn test1 () {
  let mut x = 2;
  let mut y = x;
  assert pure (!(!y) == 2);
}
