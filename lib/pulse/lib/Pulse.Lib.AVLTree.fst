//Pulse AVL tree implementation. Inspired from Steel. The FStar spec file is adopted from Steel
//----------------------------------------------------------------------------------------------------------
module Pulse.Lib.AVLTree
open Pulse.Lib.Pervasives
module S = Pulse.Lib.Stick.Util
module FA = Pulse.Lib.Forall.Util
open FStar.List.Tot

module T = Spec.AVLTree

//type vprop = slprop

noeq
type node (t:Type0) = {
    data : t;
    left : tree_t t;
    right : tree_t t;
}

and node_ptr (t:Type0) = ref (node t)

and tree_t (t:Type0) = option (node_ptr t)

val is_tree #t (ct:tree_t t) (ft:T.tree t)
: Tot slprop (decreases ft)
let rec is_tree #t ct ft = match ft with
  | T.Leaf -> pure (ct == None)
  | T.Node data left' right' ->
    exists* (p:node_ptr t) (lct:tree_t t) (rct:tree_t t).
      pure (ct == Some p) **
      pts_to p { data = data ; left = lct ; right = rct} **
      is_tree lct left' **
      is_tree rct right'

//boilerplate$

```pulse
ghost
fn elim_is_tree_leaf (#t:Type0) (x:tree_t t)
requires is_tree x T.Leaf 
ensures pure (x == None)                 
{   
   admit () 
}
```

module G = FStar.Ghost

```pulse //is_list_case_none$
ghost
fn is_tree_case_none (#t:Type) (x:tree_t t) (#l:T.tree t)
requires is_tree x l ** pure (x == None)
ensures  is_tree x l ** pure (l == T.Leaf)
{
  admit ()
}

```

```pulse //is_list_case_some$
ghost
fn is_tree_case_some (#t:Type) (x:tree_t t) (v:node_ptr t) (#ft:T.tree t) 
requires is_tree x ft ** pure (x == Some v)
ensures  
   exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
    pts_to v node **
    is_tree node.left ltree **
    is_tree node.right rtree **
    pure (ft == T.Node node.data ltree rtree)
  
{
  admit ()
}
```

module G = FStar.Ghost

```pulse
fn delete_avl (#t:Type0) (cmp: T.cmp t) (tree:tree_t t) (key: t)
requires is_tree tree 'l
returns y:tree_t t 
ensures emp
{
  match tree{
   None -> {
    admit ()
   }
   Some vl -> {
    is_tree_case_some tree vl;
      let n = !vl;
      let delta = cmp n.data key;
      if (delta = 0){
       let left = n.left;
       let right = n.right;
       with ltree. assert (is_tree left ltree);
       with rtree. assert (is_tree right rtree);
       match left {
        None -> {(*Leaf, _*)
          is_tree_case_none left;
          match right {
            None -> { (*Leaf,Leaf*)
               is_tree_case_none right #rtree;
               assert (is_tree left ltree);
               assert (is_tree right rtree);
               assert (pure (ltree == T.Leaf /\ rtree == T.Leaf));
               //
               // AR: Without this rewrite, elim_is_tree_leaf fails
               //
               // rewrite (is_tree left ltree) as (is_tree left T.Leaf);
               elim_is_tree_leaf left;
               admit ()
            }
            Some vlr -> {(*Leaf,Node_*)
              admit ()
            }
          }
        }
        _ -> {(*Node_,_*)
        admit ()
        }
       }
      }
      else{
        admit ()
      }
   }
  }
}
```

