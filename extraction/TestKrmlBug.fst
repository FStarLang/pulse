module TestKrmlBug
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box
module SZ = FStar.SizeT
module AVL = Pulse.Lib.AVLTree
module T = Pulse.Lib.Spec.AVLTree

// Wraps an AVL tree in a heap-allocated box
type my_tree = box (AVL.tree_t SZ.t unit)

fn my_create (_u: unit)
  requires emp
  returns r: AVL.tree_t SZ.t unit
  ensures AVL.is_tree r T.Leaf
{
  AVL.create SZ.t unit
}
