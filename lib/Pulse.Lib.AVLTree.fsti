//Pulse AVL tree interface. Inspired from Steel. The FStar spec file is adopted from Steel
//----------------------------------------------------------------------------------------------------------
module Pulse.Lib.AVLTree
open Pulse.Lib.Pervasives
module S = Pulse.Lib.Stick.Util
module FA = Pulse.Lib.Forall.Util
open FStar.List.Tot

module T = Spec.AVLTree
module G = FStar.Ghost

noeq
type node (t:Type0) = {
    data : t;
    left : tree_t t;
    right : tree_t t;
}

and node_ptr (t:Type0) = ref (node t)

//A nullable pointer to a node
and tree_t (t:Type0) = option (node_ptr t)

let vprop = slprop

val is_tree #t (ct:tree_t t) (ft:T.tree t)
: Tot vprop (decreases ft)

val height (#t:Type0) (x:tree_t t) (#ft:G.erased (T.tree t))
  : stt nat
(requires is_tree x ft)
(ensures fun n -> is_tree x ft ** pure (n == T.height ft))

val is_empty (#t:Type) (x:tree_t t) (#ft:(T.tree t))
   : stt bool
  (requires is_tree x ft)
  (ensures fun b -> is_tree x ft ** pure (b <==> (ft == T.Leaf)))

val null_tree_t (t:Type0) : tree_t t

val create (t:Type0)
   : stt (tree_t t)
  (requires emp)
  (ensures fun x -> is_tree x T.Leaf)

val append_left_none (#t:Type0) (x:tree_t t) (v:t) (#ft:G.erased (T.tree t))
   : stt (tree_t t)
(requires is_tree x ft ** pure (None? x))
(ensures fun y -> is_tree x ft  ** is_tree y (T.Node v T.Leaf T.Leaf))

val append_left (#t:Type0) (x:tree_t t) (v:t) (#ft:G.erased (T.tree t))
   : stt (tree_t t)
(requires is_tree x ft)
(ensures fun y -> is_tree y  (T.append_left ft v))

val append_right (#t:Type0) (x:tree_t t) (v:t) (#ft:G.erased (T.tree t))
   : stt (tree_t t)
(requires is_tree x ft)
(ensures fun y -> is_tree y  (T.append_right ft v))

val node_data (#t:Type) (x:tree_t t) (#ft:G.erased (T.tree t))
     : stt t
(requires is_tree x ft  ** (pure (Some? x)))
(ensures fun _ -> is_tree x ft)

val is_mem (#t:eqtype) (x:tree_t t) (v: t) (#ft:G.erased (T.tree t))
     : stt bool
(requires is_tree x ft)
(ensures fun b -> is_tree x ft ** pure (b <==> (T.mem ft v)))

val rotate_left (#t:Type0) (tree:tree_t t) (#l:G.erased(T.tree t){ Some? (T.rotate_left l) })
     : stt (tree_t t )
(requires is_tree tree l)
(ensures (fun y -> is_tree y (Some?.v (T.rotate_left l))))


val rotate_right (#t:Type0) (tree:tree_t t) (#l:G.erased (T.tree t){ Some? (T.rotate_right l) })
    : stt (tree_t t )
(requires is_tree tree l)
(ensures (fun y -> is_tree y (Some?.v (T.rotate_right l))))

val rotate_right_left (#t:Type0) (tree:tree_t t) (#l:G.erased (T.tree t){ Some? (T.rotate_right_left l) })
     : stt (tree_t t )
(requires is_tree tree l)
(ensures (fun y -> is_tree y (Some?.v (T.rotate_right_left l))))

val rotate_left_right (#t:Type0) (tree:tree_t t) (#l:G.erased (T.tree t){ Some? (T.rotate_left_right l) })
     : stt (tree_t t )
(requires is_tree tree l)
(ensures (fun y -> is_tree y (Some?.v (T.rotate_left_right l))))

val  is_balanced (#t:Type0) (tree:tree_t t) (#l:G.erased (T.tree t))
     : stt bool
(requires is_tree tree l)
(ensures fun b -> is_tree tree l ** pure (b <==> (T.is_balanced l)))

val  rebalance_avl (#t:Type0) (tree:tree_t t) (#l: G.erased(T.tree t))
     : stt (tree_t t )
(requires is_tree tree l)
(ensures fun y -> (is_tree y (T.rebalance_avl l)))

val  insert_avl (#t:Type0) (cmp: T.cmp t) (tree:tree_t t) (key: t) (#l: G.erased(T.tree t))
    : stt (tree_t t )
(requires is_tree tree l) 
(ensures fun y -> (is_tree y (T.insert_avl cmp l key)))

val  delete_avl (#t:Type0) (cmp: T.cmp t) (tree:tree_t t) (key: t) (#l: G.erased(T.tree t))
    : stt (tree_t t )
(requires is_tree tree l) 
(ensures fun y -> (is_tree y (T.delete_avl cmp l key)))
