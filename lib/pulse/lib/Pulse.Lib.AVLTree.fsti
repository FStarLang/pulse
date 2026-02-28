(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: Sheera Shamsu
*)

//Pulse AVL tree interface. Inspired from Steel. The FStar spec file is adopted from Steel
//----------------------------------------------------------------------------------------------------------
module Pulse.Lib.AVLTree
#lang-pulse
open Pulse.Lib.Pervasives

module T = Pulse.Lib.Spec.AVLTree
module G = FStar.Ghost

val tree_t  (k:Type u#0) (v:Type u#0): Type u#0

val is_tree #k #v ([@@@mkey] ct:tree_t k v) (ft:T.tree k v)
: Tot slprop (decreases ft)

fn height (#k:Type0) (#v:Type0) (x:tree_t k v) (#ft:G.erased (T.tree k v))
  preserves is_tree x ft
  returns  n : nat
  ensures pure (n == T.height ft)

fn is_empty (#k:Type) (#v:Type) (x:tree_t k v) (#ft:G.erased(T.tree k v))
  preserves is_tree x ft
  returns  b : bool
  ensures pure (b <==> (T.is_empty ft))

fn create (k:Type0) (v:Type0)
  returns  x : tree_t k v
  ensures  is_tree x T.Leaf

fn mem (#k:eqtype) (#v:Type0) (x:tree_t k v) (key: k) (#ft:G.erased (T.tree k v))
  preserves is_tree x ft
  returns  b : bool
  ensures pure (b <==> (T.mem ft key))

fn insert_avl
  (#k:Type0) (#v:Type0) (cmp: T.cmp k) (tree:tree_t k v) (key: k) (val_: v)
  (#l: G.erased(T.tree k v))
  requires is_tree tree l
  returns  y : tree_t k v
  ensures  is_tree y (T.insert_avl cmp l key val_)

fn delete_avl
  (#k:Type0) (#v:Type0) (cmp: T.cmp k) (tree:tree_t k v) (key: k)
  (#l: G.erased(T.tree k v))
  requires is_tree tree l
  returns  y : tree_t k v
  ensures  is_tree y (T.delete_avl cmp l key)

fn find_min (#k:Type0) (#v:Type0) (cmp: T.cmp k) (x:tree_t k v) (#ft:G.erased (T.tree k v){T.Node? ft})
  requires is_tree x ft
  returns y:(k & v)
  ensures is_tree x ft ** pure (y == T.tree_min ft)

fn find_max (#k:Type0) (#v:Type0) (cmp: T.cmp k) (x:tree_t k v) (#ft:G.erased (T.tree k v){T.Node? ft})
  requires is_tree x ft
  returns y:(k & v)
  ensures is_tree x ft ** pure (y == T.tree_max ft)

fn find_le (#k:Type0) (#v:Type0) (cmp: T.cmp k) (x:tree_t k v) (key:k) (#ft:G.erased (T.tree k v))
  preserves is_tree x ft
  returns y:option (k & v)
  ensures pure (y == T.find_le cmp ft key)

fn find_ge (#k:Type0) (#v:Type0) (cmp: T.cmp k) (x:tree_t k v) (key:k) (#ft:G.erased (T.tree k v))
  preserves is_tree x ft
  returns y:option (k & v)
  ensures pure (y == T.find_ge cmp ft key)

fn free (#k:Type0) (#v:Type0) (x:tree_t k v) (#ft:G.erased (T.tree k v))
  requires is_tree x ft
  ensures emp
