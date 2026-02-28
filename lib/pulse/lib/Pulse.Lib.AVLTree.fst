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
//Pulse AVL tree implementation. Inspired from Steel. The FStar spec file is adopted from Steel
//----------------------------------------------------------------------------------------------------------
module Pulse.Lib.AVLTree
#lang-pulse
open Pulse.Lib.Pervasives

module T = Pulse.Lib.Spec.AVLTree

module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }

noeq
type node (k:Type0) (v:Type0) = {
    key : k;
    value : v;
    left : tree_t k v;
    right : tree_t k v;
}

and node_ptr (k:Type0) (v:Type0) = box (node k v)

//A nullable pointer to a node
and tree_t (k:Type0) (v:Type0) = option (node_ptr k v)

let rec is_tree #k #v ct ft = match ft with
  | T.Leaf -> pure (ct == None)
  | T.Node nd_key nd_val left' right' ->
    exists* (p:node_ptr k v) (lct:tree_t k v) (rct:tree_t k v).
      pure (ct == Some p) **
      (p |-> { key = nd_key ; value = nd_val ; left = lct ; right = rct}) **
      is_tree lct left' **
      is_tree rct right'


ghost
fn elim_is_tree_leaf (#k:Type0) (#v:Type0) (x:tree_t k v)
  requires is_tree x T.Leaf
  ensures pure (x == None)
{
   unfold (is_tree x T.Leaf)
}



ghost
fn intro_is_tree_leaf (#k:Type0) (#v:Type0) (x:tree_t k v)
  requires pure (x == None)
  ensures is_tree x T.Leaf
{
  fold (is_tree x T.Leaf);
}



ghost
fn elim_is_tree_node (#k:Type0) (#v:Type0) (ct:tree_t k v) (nd_key:k) (nd_val:v) (ltree:T.tree k v) (rtree:T.tree k v)
  requires is_tree ct (T.Node nd_key nd_val ltree rtree)
  ensures (
  exists* (p:node_ptr k v) (lct:tree_t k v) (rct:tree_t k v).
    pure (ct == Some p) **
    (p |-> { key = nd_key; value = nd_val; left = lct; right = rct }) **
    is_tree lct ltree **
    is_tree rct rtree
)
{
  unfold is_tree
}


module G = FStar.Ghost


ghost
fn intro_is_tree_node (#k:Type0) (#v:Type0) (ct:tree_t k v) (p:node_ptr k v) (#nd:node k v) (#ltree:T.tree k v) (#rtree:T.tree k v)
requires
  (p |-> nd) **
  is_tree nd.left ltree **
  is_tree nd.right rtree **
  pure (ct == Some p)
ensures
  is_tree ct (T.Node nd.key nd.value ltree rtree)
{
  fold (is_tree ct (T.Node nd.key nd.value ltree rtree))
}


[@@no_mkeys] // internal only
let is_tree_cases #k #v (x : option (box (node k v))) (ft : T.tree k v)
= match x with
  | None -> pure (ft == T.Leaf)
  | Some p ->
    exists* (n:node k v) (ltree:T.tree k v) (rtree:T.tree k v).
      (p |-> n) **
      pure (ft == T.Node n.key n.value ltree rtree) **
      is_tree n.left ltree **
      is_tree n.right rtree

ghost
fn cases_of_is_tree #k #v (x:tree_t k v) (ft:T.tree k v)
  requires is_tree x ft
  ensures  is_tree_cases x ft
{
  match ft {
    T.Leaf -> {
      unfold (is_tree x T.Leaf);
      fold (is_tree_cases None ft);
      rewrite is_tree_cases None ft as is_tree_cases x ft;
    }
    T.Node nd_key nd_val ltree rtree -> {
      unfold (is_tree x (T.Node nd_key nd_val ltree rtree));
      with p lct rct. _;
      with n. assert p |-> n;
      with l'. rewrite is_tree lct l' as is_tree n.left l';
      with r'. rewrite is_tree rct r' as is_tree n.right r';
      fold (is_tree_cases (Some p) ft);
      rewrite (is_tree_cases (Some p) ft) as is_tree_cases x ft;
    }
  }
}




ghost
fn is_tree_case_none (#k:Type) (#v:Type) (x:tree_t k v) (#l:T.tree k v)
  preserves is_tree x l
  requires pure (x == None)
  ensures pure (l == T.Leaf)
{
  rewrite each x as None;
  cases_of_is_tree None l;
  unfold is_tree_cases;
  intro_is_tree_leaf x;
  ()
}




ghost
fn is_tree_case_some (#k:Type) (#v:Type) (x:tree_t k v) (p:node_ptr k v) (#ft:T.tree k v)
  requires is_tree x ft
  requires pure (x == Some p)
ensures
   exists* (nd:node k v) (ltree:T.tree k v) (rtree:T.tree k v).
    (p |-> nd) **
    is_tree nd.left ltree **
    is_tree nd.right rtree **
    pure (ft == T.Node nd.key nd.value ltree rtree)

{
  rewrite each x as Some p;
  cases_of_is_tree (Some p) ft;
  unfold is_tree_cases;
}


///////////////////////////////////////////////////////////////////////////////


fn rec height (#k:Type0) (#v:Type0) (x:tree_t k v)
  preserves is_tree x 'l
  returns n:nat
  ensures pure (n == T.height 'l)
{
   match x {
    None -> {
       is_tree_case_none None;
       rewrite is_tree None 'l as is_tree x 'l;
       0
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      let node = !vl;
      let l_height = height node.left;
      let r_height = height node.right;
      intro_is_tree_node x vl;
      if (l_height > r_height) {
        (l_height + 1)
      } else {
        (r_height + 1)
      }
    }
  }
}



fn is_empty (#k:Type) (#v:Type) (x:tree_t k v) (#ft:G.erased(T.tree k v))
  preserves is_tree x ft
  returns b:bool
  ensures pure (b <==> (T.is_empty ft))
{
  match x {
    None -> {
      is_tree_case_none None;
      rewrite is_tree None ft as is_tree x ft;
      true
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      intro_is_tree_node x vl;
      false
    }
  }
}


let null_tree_t (k:Type0) (v:Type0) : tree_t k v = None



fn create (k:Type0) (v:Type0)
  returns x:tree_t k v
  ensures is_tree x T.Leaf
{
  let tree = null_tree_t k v;
  intro_is_tree_leaf tree;
  tree
}


fn node_cons (#k:Type0) (#v:Type0) (nd_key:k) (nd_val:v) (ltree:tree_t k v) (rtree:tree_t k v) (#l:(T.tree k v)) (#r:(T.tree k v))
  requires is_tree ltree l  **
           is_tree rtree r
  returns y:tree_t k v
  ensures is_tree y (T.Node nd_key nd_val l r)
  ensures (pure (Some? y))
{
  let y = Box.alloc { key=nd_key; value=nd_val; left=ltree; right=rtree };
  intro_is_tree_node (Some y) y;
  Some y
}



fn rec append_left (#k:Type0) (#v:Type0) (x:tree_t k v) (ak:k) (av:v) (#ft:G.erased (T.tree k v))
  requires is_tree x ft
  returns y:tree_t k v
  ensures is_tree y  (T.append_left ft ak av)
{
   match x {
    None -> {

      is_tree_case_none None;

      elim_is_tree_leaf None;


      let left = create k v;
      let right = create k v;


      let y = node_cons ak av left right;

      let np = Some?.v y;

      is_tree_case_some y np;

      intro_is_tree_node y np;
      y
    }
    Some vl -> {

      is_tree_case_some (Some vl) vl;

      let node = !vl;

      let left_new = append_left node.left ak av;

      vl := {node with left = left_new};

      intro_is_tree_node x vl;

      x
    }
  }
}




fn rec append_right (#k:Type0) (#v:Type0) (x:tree_t k v) (ak:k) (av:v) (#ft:G.erased (T.tree k v))
  requires is_tree x ft
  returns y:tree_t k v
  ensures is_tree y  (T.append_right ft ak av)
{
   match x {
    None -> {

      is_tree_case_none None;

      elim_is_tree_leaf None;

      let left = create k v;
      let right = create k v;


      let y = node_cons ak av left right;

      let np = Some?.v y;

      is_tree_case_some y np;

      intro_is_tree_node y np;

      y
    }
    Some np -> {
      is_tree_case_some (Some np) np;

      let node = !np;

      let right_new = append_right node.right ak av;

      np := {node with right = right_new};

      intro_is_tree_node x np;

      x
    }
  }
}




fn rec mem (#k:eqtype) (#v:Type0) (x:tree_t k v) (search_key: k) (#ft:G.erased (T.tree k v))
    preserves is_tree x ft
    returns b:bool
    ensures pure (b <==> (T.mem ft search_key))
{
  match x {
       None -> {
           is_tree_case_none None;
           rewrite is_tree None ft as is_tree x ft;
           false
       }
       Some vl -> {
           is_tree_case_some (Some vl) vl;
           let n = !vl;

           let dat = n.key;

           if (dat = search_key)
           {
             intro_is_tree_node x vl;
             true
           }
           else{
             let b1 = mem n.left search_key;
             let b2 = mem n.right search_key;

             let b3 = b1 || b2;
             intro_is_tree_node x vl;
             b3;

           }
       }
  }
}




fn get_some_ref (#k:Type) (#v:Type) (x:tree_t k v)
  requires is_tree x 'l
  requires pure (T.Node? 'l)
  returns p:node_ptr k v
ensures
  exists* (nd:node k v) (ltree:T.tree k v) (rtree:T.tree k v).
    pure (x == Some p) **
    pure ('l == T.Node nd.key nd.value ltree rtree) **
    (p |-> nd) **
    is_tree nd.left ltree **
    is_tree nd.right rtree
{
  match x {
    None -> {
      is_tree_case_none None;
      unreachable ()
    }
    Some p -> {
      is_tree_case_some (Some p) p;
      p
    }
  }
}

[@@pulse_unfold] let _left  (#k:Type) (#v:Type) (t:T.tree k v{T.Node? t}) = T.Node?.left  t
[@@pulse_unfold] let _right (#k:Type) (#v:Type) (t:T.tree k v{T.Node? t}) = T.Node?.right t
[@@pulse_unfold] let _key   (#k:Type) (#v:Type) (t:T.tree k v{T.Node? t}) = T.Node?.key   t
[@@pulse_unfold] let _val   (#k:Type) (#v:Type) (t:T.tree k v{T.Node? t}) = T.Node?.value t

fn read_node
  (#k:Type0) (#v:Type0)
  (tree : tree_t k v)
  (#t : erased (T.tree k v){T.Node? t})
  requires is_tree tree t
  returns  res : tree_t k v & k & v & tree_t k v & squash (Some? tree)
  ensures (
    let (l, xk, xv, r, _) = res in
    (Some?.v tree |-> {left = l; key = xk; value = xv; right = r})
    ** is_tree l (_left t)
    ** is_tree r (_right t)
    ** pure (xk == _key t)
    ** pure (xv == _val t)
  )
{
  let p = get_some_ref tree;
  with nd. assert p |-> nd;
  let n = !p;
  rewrite p |-> n as Some?.v tree |-> n;
  (n.left, n.key, n.value, n.right, ())
}

fn write_node
  (#k:Type0) (#v:Type0)
  (tree : tree_t k v{Some? tree})
  (lp : tree_t k v)
  (nd_key : k)
  (nd_val : v)
  (rp : tree_t k v)
  (#lt #rt : erased (T.tree k v))
  requires
    (Some?.v tree |-> 'n0) **
    is_tree lp lt **
    is_tree rp rt
  ensures
    is_tree tree (T.Node nd_key nd_val lt rt)
{
  let n = { key = nd_key; value = nd_val; left = lp; right = rp };
  let Some p = tree;
  p := n;
  fold (is_tree tree (T.Node nd_key nd_val lt rt))
}

fn rotate_left (#k:Type0) (#v:Type0) (tree:tree_t k v) (#l: G.erased (T.tree k v){ Some? (T.rotate_left l) })
  requires is_tree tree l
  returns  y : tree_t k v
  ensures  is_tree y (Some?.v (T.rotate_left l))
{
  let a, bk, bv, p', _  = read_node tree;
  let c, dk, dv, e,  _  = read_node p';
  write_node p' a bk bv c;
  write_node tree p' dk dv e;
  tree
}

fn rotate_right (#k:Type0) (#v:Type0) (tree:tree_t k v) (#l:G.erased (T.tree k v){ Some? (T.rotate_right l) })
  requires is_tree tree l
  returns y:tree_t k v
  ensures (is_tree y (Some?.v (T.rotate_right l)))
{
  let p', dk, dv, e, _  = read_node tree;
  let a, bk, bv, c, _  = read_node p';
  write_node p' c dk dv e;
  write_node tree a bk bv p';
  tree
}

fn rotate_right_left (#k:Type0) (#v:Type0) (tree:tree_t k v) (#l:G.erased (T.tree k v){ Some? (T.rotate_right_left l) })
  requires is_tree tree l
  returns  y : tree_t k v
  ensures  is_tree y (Some?.v (T.rotate_right_left l))
{
  let a, xk, xv, zp, _ = read_node tree;
  let yp, zk, zv, d,  _ = read_node zp;
  let b, yk, yv, c,  _ = read_node yp;
  write_node zp c zk zv d;
  write_node yp a xk xv b;
  write_node tree yp yk yv zp;
  tree
}

fn rotate_left_right (#k:Type0) (#v:Type0) (tree:tree_t k v) (#l:G.erased (T.tree k v){ Some? (T.rotate_left_right l) })
  requires is_tree tree l
  returns  y  :tree_t k v
  ensures  is_tree y (Some?.v (T.rotate_left_right l))
{
  let zp, xk, xv, d,  _ = read_node tree;
  let a, zk, zv, yp, _ = read_node zp;
  let b, yk, yv, c,  _ = read_node yp;
  write_node zp a zk zv b;
  write_node yp c xk xv d;
  write_node tree zp yk yv yp;
  tree
}


module M = FStar.Math.Lib


fn rec is_balanced (#k:Type0) (#v:Type0) (tree:tree_t k v)
  preserves is_tree tree 'l
  returns b:bool
  ensures pure (b <==> (T.is_balanced 'l))
{
  match tree {
    None -> {
      is_tree_case_none None;
      rewrite is_tree None 'l as is_tree tree 'l;
      true
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      let n = !vl;

      let height_l = height n.left;
      let height_r = height n.right;

      let b1 =  (M.abs(height_r - height_l) <= 1);

      let b2 = is_balanced n.right;

      let b3 = is_balanced n.left;

      let b4 = b1 && b2 && b3;

      intro_is_tree_node tree vl;

      b4
    }
  }
}




fn rec  rebalance_avl (#k:Type0) (#v:Type0) (tree:tree_t k v) (#l:G.erased(T.tree k v))
  requires is_tree tree l
  returns y:tree_t k v
  ensures (is_tree y (T.rebalance_avl l))
{
  let b = is_balanced tree;
  match tree {
    None -> {
      is_tree_case_none None;
      rewrite is_tree None l as is_tree tree l;
      tree
    }
    Some vl -> {
      rewrite each (Some vl) as tree;
      is_tree_case_some tree vl;

      if (b)
      {
        intro_is_tree_node tree vl;
        tree
      }
      else
      {
        let n = !vl;
        let height_l = height n.left;
        let height_r = height n.right;

        let diff_height = height_l - height_r ;

        if (diff_height > 1)
        {
          let vll = get_some_ref n.left;
          intro_is_tree_node n.left vll;
          is_tree_case_some n.left vll;

          let nl = !vll;

          let height_ll = height nl.left;
          let height_lr = height nl.right;

          if (height_lr > height_ll)
          {
             (*Only in this branch, this situation happens, Node x (Node z t1 (Node y t2 t3)) t4*)
             let vllr = get_some_ref nl.right;

             (*pack tree back in the order it is unpacked*)
             intro_is_tree_node nl.right vllr;

             intro_is_tree_node n.left vll;


             intro_is_tree_node tree vl;

             let y = rotate_left_right tree;
             y
          }
          else
          {
            (*Node x (Node z t1 t2) t3*)
            intro_is_tree_node n.left vll;
            intro_is_tree_node tree vl;
            let y = rotate_right tree;
            y
          }
        }
        else if (diff_height < -1)
        {
          let vlr = get_some_ref n.right;
          intro_is_tree_node n.right vlr;
          is_tree_case_some n.right vlr;

          let nr = !vlr;

          let height_rl = height nr.left;
          let height_rr = height nr.right;
          if (height_rl > height_rr)
          {
             (*Node x t1 (Node z (Node y t2 t3) t4)*)
             let vlrl = get_some_ref nr.left;

             (*pack tree back in the order it is unpacked*)
             intro_is_tree_node nr.left vlrl;
             intro_is_tree_node n.right vlr;
             intro_is_tree_node tree vl;
             let y = rotate_right_left tree;
             y
          }
          else
          {
            (*Node x t1 (Node z t2 t3)*)
            intro_is_tree_node n.right vlr;
            intro_is_tree_node tree vl;
            let y = rotate_left tree;
            y
          }

        }
        else
        {
          intro_is_tree_node tree vl;
          tree
        }

      }
    }
  }
}



fn rec insert_avl (#k:Type0) (#v:Type0) (cmp: T.cmp k) (tree:tree_t k v) (nd_key: k) (nd_val: v)
  requires is_tree tree 'l
  returns y:tree_t k v
  ensures (is_tree y (T.insert_avl cmp 'l nd_key nd_val))
{
  match tree {
    None -> {
       is_tree_case_none None;

       elim_is_tree_leaf None;

       let left = create k v;
       let right = create k v;


       let y = node_cons nd_key nd_val left right;

       let np = Some?.v y;

       is_tree_case_some y np;

       intro_is_tree_node y np;

       y
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      with nd. assert vl |-> nd;
      let n = !vl;
      let delta = cmp n.key nd_key;
      if (delta >= 0)
      {
        let new_left = insert_avl cmp n.left nd_key nd_val;
        let vl' = {key = n.key; value = n.value; left = new_left; right = n.right};
        vl := vl';
        rewrite each new_left as vl'.left;
        rewrite each nd.right as vl'.right;
        intro_is_tree_node (Some vl) vl #vl';
        let new_tree = rebalance_avl (Some vl);
        new_tree
      }
      else
      {
        let new_right = insert_avl cmp n.right nd_key nd_val;
        let vl' = {key = n.key; value = n.value; left = n.left; right = new_right };
        vl := vl';
        rewrite each new_right as vl'.right;
        rewrite each nd.left as vl'.left;
        intro_is_tree_node (Some vl) vl #vl';
        let new_tree = rebalance_avl (Some vl);
        new_tree
      }
    }
  }
}


ghost
fn is_tree_case_some1 (#k:Type) (#v:Type) (x:tree_t k v) (p:node_ptr k v) (#ft:T.tree k v)
  preserves is_tree x ft
  requires pure (x == Some p)
  ensures pure (T.Node? ft)
{
  rewrite each x as Some p;
  cases_of_is_tree (Some p) ft;
  unfold is_tree_cases;
  intro_is_tree_node (Some p) p;
  with 'ft. rewrite is_tree (Some p) 'ft as is_tree x 'ft;
}

fn rec tree_max_c (#k:Type0) (#v:Type0) (tree:tree_t k v) (#l:G.erased(T.tree k v){T.Node? l})
  preserves is_tree tree l
  returns y:(k & v)
  ensures pure (y == T.tree_max l)
{
  match tree {
    None -> {
      is_tree_case_none None;
      unreachable ()
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      let n = !vl;
      match n.right {
        None -> {
          let dk = n.key;
          let dv = n.value;
          is_tree_case_none n.right;
          intro_is_tree_node tree vl;
          (dk, dv)
        }
        Some vlr -> {
          is_tree_case_some1 n.right vlr;
          let max = tree_max_c n.right;
          intro_is_tree_node tree vl;
          max
        }
      }

    }
  }
}

fn rec delete_avl (#k:Type0) (#v:Type0) (cmp: T.cmp k) (tree:tree_t k v) (del_key: k)
  requires is_tree tree 'l
  returns  y : tree_t k v
  ensures  is_tree y (T.delete_avl cmp 'l del_key)
{
  match tree {
    None -> {
      is_tree_case_none None;
      rewrite is_tree None 'l as is_tree tree 'l;
      tree
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      with nd. assert vl |-> nd;
      let n = !vl;
      let delta = cmp n.key del_key;
      if (delta = 0) {
        let left = n.left;
        let right = n.right;
        rewrite each nd.left as left;
        rewrite each nd.right as right;
        //explicit ltree and rtree is needed, to find a proof for the existence of func ltree and rtree
        with ltree. assert is_tree left ltree;
        with rtree. assert is_tree right rtree;
        match left {
          None -> {(*Leaf, _*)
            is_tree_case_none None;
            match right {
              None -> { (*Leaf,Leaf*)
                 is_tree_case_none None #rtree;
                 let tr = create k v;
                 Box.free vl;
                 rewrite each rtree as T.Leaf #k #v;
                 rewrite each ltree as T.Leaf #k #v;
                 unfold is_tree #k #v None T.Leaf;
                 unfold is_tree #k #v None T.Leaf;
                 tr
              }
              Some vlr -> {(*Leaf,Node_*)
                is_tree_case_some (Some vlr) vlr;
                let rnode = !vlr;
                let vl' = {key = rnode.key; value = rnode.value; left = rnode.left; right = rnode.right};
                vl := vl';
                with ltree.
                  rewrite is_tree rnode.left ltree as is_tree vl'.left ltree;
                with rtree.
                  rewrite is_tree rnode.right rtree as is_tree vl'.right rtree;
                intro_is_tree_node (Some vl) vl #vl';
                with ltree.
                  assert (is_tree #k #v None ltree);
                Box.free vlr;
                elim_is_tree_leaf #k #v None;
                (Some vl)
              }
            }
          }
          Some vll -> {(*Node_,_*)
            is_tree_case_some1 (Some vll) vll;
            match right {
              None -> {(*Node_,Leaf*)
                is_tree_case_some (Some vll) vll;
                is_tree_case_none None;
                let lnode = !vll;
                let vl' = {key = lnode.key; value = lnode.value; left = lnode.left; right = lnode.right};
                vl := vl';
                with ltree.
                  rewrite is_tree lnode.left ltree as is_tree vl'.left ltree;
                with rtree.
                  rewrite is_tree lnode.right rtree as is_tree vl'.right rtree;
                intro_is_tree_node (Some vl) vl #vl';
                Box.free vll;
               //  rewrite (is_tree right rtree) as (is_tree right T.Leaf);
                elim_is_tree_leaf None;
                (Some vl)
              }
              Some vlr -> {(*Node_,Node_*)
                is_tree_case_some1 (Some vlr) vlr;
                let m = tree_max_c (Some vll);
                let new_left = delete_avl cmp (Some vll) (fst m);
                let vl' = {key = fst m; value = snd m; left = new_left; right = right};
                vl := vl';
                with ltree.
                  rewrite is_tree new_left ltree as is_tree vl'.left ltree;
                with rtree.
                  rewrite is_tree (Some vlr) rtree as is_tree vl'.right rtree;
                intro_is_tree_node (Some vl) vl #vl';
                let new_tree = rebalance_avl (Some vl);
                assert (is_tree new_tree (T.delete_avl cmp 'l del_key));
                new_tree
              }
            }
          }
        }
      } else {
        if (delta < 0) {
          assert (pure (delta < 0));
          let new_right = delete_avl cmp n.right del_key;
          let vl' = {key = n.key; value = n.value; left = n.left; right = new_right};
          vl := vl';
          with ltree.
            rewrite is_tree n.left ltree as is_tree vl'.left ltree;
          with rtree.
            rewrite is_tree new_right rtree as is_tree vl'.right rtree;
          intro_is_tree_node (Some vl) vl #vl';
          let new_tree = rebalance_avl (Some vl);
          new_tree
        } else {
          let new_left = delete_avl cmp n.left del_key;
          let vl' = {key = n.key; value = n.value; left = new_left; right = n.right};
          vl := vl';
          with ltree.
            rewrite is_tree new_left ltree as is_tree vl'.left ltree;
          with rtree.
            rewrite is_tree n.right rtree as is_tree vl'.right rtree;
          intro_is_tree_node (Some vl) vl #vl';

          let new_tree = rebalance_avl (Some vl);
          assert (is_tree new_tree (T.delete_avl cmp 'l del_key));

          new_tree
        }
      }
    }
  }
}

fn rec find_min (#k:Type0) (#v:Type0) (cmp: T.cmp k) (tree:tree_t k v) (#l:G.erased(T.tree k v){T.Node? l})
  preserves is_tree tree l
  returns y:(k & v)
  ensures pure (y == T.tree_min l)
{
  match tree {
    None -> {
      is_tree_case_none None;
      unreachable ()
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      let n = !vl;
      match n.left {
        None -> {
          let dk = n.key;
          let dv = n.value;
          is_tree_case_none n.left;
          intro_is_tree_node tree vl;
          (dk, dv)
        }
        Some vll -> {
          is_tree_case_some1 n.left vll;
          let min = find_min cmp n.left;
          intro_is_tree_node tree vl;
          min
        }
      }
    }
  }
}

fn rec find_max (#k:Type0) (#v:Type0) (cmp: T.cmp k) (tree:tree_t k v) (#l:G.erased(T.tree k v){T.Node? l})
  preserves is_tree tree l
  returns y:(k & v)
  ensures pure (y == T.tree_max l)
{
  match tree {
    None -> {
      is_tree_case_none None;
      unreachable ()
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      let n = !vl;
      match n.right {
        None -> {
          let dk = n.key;
          let dv = n.value;
          is_tree_case_none n.right;
          intro_is_tree_node tree vl;
          (dk, dv)
        }
        Some vr -> {
          is_tree_case_some1 n.right vr;
          let max = find_max cmp n.right;
          intro_is_tree_node tree vl;
          max
        }
      }
    }
  }
}

fn rec find_le (#k:Type0) (#v:Type0) (cmp: T.cmp k) (tree:tree_t k v) (search_key:k) (#ft:G.erased (T.tree k v))
  preserves is_tree tree ft
  returns y:option (k & v)
  ensures pure (y == T.find_le cmp ft search_key)
{
  match tree {
    None -> {
      is_tree_case_none None;
      rewrite is_tree None ft as is_tree tree ft;
      let r : option (k & v) = None;
      r
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      let n = !vl;
      let delta = cmp n.key search_key;
      if (delta > 0) {
        let r = find_le cmp n.left search_key;
        intro_is_tree_node tree vl;
        r
      } else if (delta = 0) {
        intro_is_tree_node tree vl;
        let r : option (k & v) = Some (n.key, n.value);
        r
      } else {
        let r = find_le cmp n.right search_key;
        intro_is_tree_node tree vl;
        match r {
          Some _ -> { r }
          None -> { let r2 : option (k & v) = Some (n.key, n.value); r2 }
        }
      }
    }
  }
}

fn rec find_ge (#k:Type0) (#v:Type0) (cmp: T.cmp k) (tree:tree_t k v) (search_key:k) (#ft:G.erased (T.tree k v))
  preserves is_tree tree ft
  returns y:option (k & v)
  ensures pure (y == T.find_ge cmp ft search_key)
{
  match tree {
    None -> {
      is_tree_case_none None;
      rewrite is_tree None ft as is_tree tree ft;
      let r : option (k & v) = None;
      r
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      let n = !vl;
      let delta = cmp n.key search_key;
      if (delta < 0) {
        let r = find_ge cmp n.right search_key;
        intro_is_tree_node tree vl;
        r
      } else if (delta = 0) {
        intro_is_tree_node tree vl;
        let r : option (k & v) = Some (n.key, n.value);
        r
      } else {
        let r = find_ge cmp n.left search_key;
        intro_is_tree_node tree vl;
        match r {
          Some _ -> { r }
          None -> { let r2 : option (k & v) = Some (n.key, n.value); r2 }
        }
      }
    }
  }
}

fn rec free (#k:Type0) (#v:Type0) (x:tree_t k v) (#ft:G.erased (T.tree k v))
  requires is_tree x ft
  ensures emp
{
  match x {
    None -> {
      is_tree_case_none None;
      rewrite is_tree None ft as is_tree None (T.Leaf #k #v);
      elim_is_tree_leaf (None #(node_ptr k v));
      ()
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      let n = !vl;
      free n.left;
      free n.right;
      Box.free vl
    }
  }
}
