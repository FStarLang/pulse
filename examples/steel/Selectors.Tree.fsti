module Selectors.Tree

open Selectors.Tree.Core
open Steel.Memory
open Steel.SelEffect

module Spec = FStar.Trees

(**** High-level operations on trees *)

val append_left (#a: Type0) (ptr: t a) (v: a)
    : SteelSel (t a)
      (linked_tree ptr)
      (fun ptr' ->  linked_tree ptr')
      (requires (fun h0 -> True))
      (ensures (fun h0 ptr' h1 -> v_linked_tree ptr' h1 == Spec.append_left (v_linked_tree ptr h0) v))

val append_right (#a: Type0) (ptr: t a) (v: a)
    : SteelSel (t a)
      (linked_tree ptr)
      (fun ptr' ->  linked_tree ptr')
      (requires (fun h0 -> True))
      (ensures (fun h0 ptr' h1 ->
        v_linked_tree ptr' h1 == Spec.append_right (v_linked_tree ptr h0) v
      ))

val height (#a: Type0) (ptr: t a)
    : SteelSel nat (linked_tree ptr) (fun _ -> linked_tree ptr)
    (requires fun _ -> True)
    (ensures fun h0 x h1 ->
        v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
        Spec.height (v_linked_tree ptr h0) == x)

val member (#a: eqtype) (ptr: t a) (v: a)
    : SteelSel bool (linked_tree ptr) (fun _ -> linked_tree ptr)
    (requires fun _ -> True)
    (ensures fun h0 b h1 ->
        v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
        (Spec.mem (v_linked_tree ptr h0) v <==> b))

val rotate_left (#a: Type) (ptr: t a)
    : SteelSel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
    (requires fun _ -> True)
    (ensures (fun h0 ptr' h1 ->
        Some (v_linked_tree ptr' h1) == Spec.rotate_left (v_linked_tree ptr h0)))
        
