//This file is copied verbatim from the steel repository except delete_avl.
module Pulse.Lib.Spec.AVLTree
#lang-pulse

module M = FStar.Math.Lib

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(*** Type definitions *)

(**** The tree structure *)

type tree (k: Type) (v: Type) =
  | Leaf : tree k v
  | Node: key: k -> value: v -> left: tree k v -> right: tree k v -> tree k v

(**** Binary search trees *)


type cmp (k: Type) = compare: (k -> k -> int){
  squash (forall x. compare x x == 0) /\
  squash (forall x y. compare x y > 0 <==> compare y x < 0) /\
  squash (forall x y z. compare x y >= 0 /\ compare y z >= 0 ==> compare x z >= 0)
}

let rec forall_keys (#k: Type) (#v: Type) (t: tree k v) (cond: k -> bool) : bool =
  match t with
  | Leaf -> true
  | Node nd_key nd_val left right ->
    cond nd_key && forall_keys left cond && forall_keys right cond

let key_left (#k: Type) (compare:cmp k) (root key: k) =
  compare root key >= 0

let key_right (#k: Type) (compare : cmp k) (root key: k) =
  compare root key <= 0

let rec is_bst (#k: Type) (#v: Type) (compare : cmp k) (x: tree k v) : bool =
  match x with
  | Leaf -> true
  | Node nd_key nd_val left right ->
    is_bst compare left && is_bst compare right &&
    forall_keys left (key_left compare nd_key) &&
    forall_keys right (key_right compare nd_key)

let bst (k: Type) (v: Type) (cmp:cmp k) = x:tree k v {is_bst cmp x}

(*** Operations *)

(**** empty *)
let is_empty (#k: Type) (#v: Type) (r: tree k v) : b:bool{b == true <==> r == Leaf} =
 match r with
 | Leaf -> true
 | _ -> false

(**** Lookup *)

let rec mem (#k: Type) (#v: Type) (r: tree k v) (x: k) : prop =
  match r with
  | Leaf -> False
  | Node nd_key nd_val left right ->
    (nd_key == x) \/ (mem right x) \/ mem left x

let rec bst_search (#k: Type) (#v: Type) (cmp:cmp k) (x: bst k v cmp) (key: k) : option (k & v) =
  match x with
  | Leaf -> None
  | Node nd_key nd_val left right ->
    let delta = cmp nd_key key in
    if delta < 0 then bst_search cmp right key else
    if delta > 0 then bst_search cmp left key else
    Some (nd_key, nd_val)

(**** Height *)

let rec height (#k: Type) (#v: Type) (x: tree k v) : nat =
  match x with
  | Leaf -> 0
  | Node nd_key nd_val left right ->
    if height left > height right then (height left) + 1
    else (height right) + 1

(**** Append *)

let rec append_left (#k: Type) (#v: Type) (x: tree k v) (ak: k) (av: v) : tree k v =
  match x with
  | Leaf -> Node ak av Leaf Leaf
  | Node xk xv left right -> Node xk xv (append_left left ak av) right

let rec append_right (#k: Type) (#v: Type) (x: tree k v) (ak: k) (av: v) : tree k v =
  match x with
  | Leaf -> Node ak av Leaf Leaf
  | Node xk xv left right -> Node xk xv left (append_right right ak av)


(**** Insertion *)

(**** BST insertion *)

let rec insert_bst (#k: Type) (#v: Type) (cmp:cmp k) (x: bst k v cmp) (key: k) (val_: v) : tree k v =
  match x with
  | Leaf -> Node key val_ Leaf Leaf
  | Node nd_key nd_val left right ->
    let delta = cmp nd_key key in
    if delta >= 0 then begin
      let new_left = insert_bst cmp left key val_ in
      Node nd_key nd_val new_left right
    end else begin
      let new_right = insert_bst cmp right key val_ in
      Node nd_key nd_val left new_right
    end

let rec insert_bst_preserves_forall_keys
  (#k: Type) (#v: Type)
  (cmp:cmp k)
  (x: bst k v cmp)
  (key: k)
  (val_: v)
  (cond: k -> bool)
    : Lemma
      (requires (forall_keys x cond /\ cond key))
      (ensures (forall_keys (insert_bst cmp x key val_) cond))
  =
  match x with
  | Leaf -> ()
  | Node nd_key nd_val left right ->
    let delta = cmp nd_key key in
    if delta >= 0 then
      insert_bst_preserves_forall_keys cmp left key val_ cond
    else
      insert_bst_preserves_forall_keys cmp right key val_ cond

let rec insert_bst_preserves_bst
  (#k: Type) (#v: Type)
  (cmp:cmp k)
  (x: bst k v cmp)
  (key: k)
  (val_: v)
    : Lemma(is_bst cmp (insert_bst cmp x key val_))
  =
  match x with
  | Leaf -> ()
  | Node nd_key nd_val left right ->
    let delta = cmp nd_key key in
    if delta >= 0 then begin
      insert_bst_preserves_forall_keys cmp left key val_ (key_left cmp nd_key);
      insert_bst_preserves_bst cmp left key val_
    end else begin
      insert_bst_preserves_forall_keys cmp right key val_ (key_right cmp nd_key);
      insert_bst_preserves_bst cmp right key val_
    end

(**** AVL insertion *)

let rec is_balanced (#k: Type) (#v: Type) (x: tree k v) : bool =
  match x with
  | Leaf -> true
  | Node nd_key nd_val left right ->
    M.abs(height right - height left) <= 1 &&
    is_balanced(right) &&
    is_balanced(left)

let is_avl (#k: Type) (#v: Type) (cmp:cmp k) (x: tree k v) : prop =
  is_bst cmp x /\ is_balanced x

let avl (k: Type) (v: Type) (cmp:cmp k) = x: tree k v {is_avl cmp x}

let rotate_left (#k: Type) (#v: Type) (r: tree k v) : option (tree k v) =
  match r with
  | Node xk xv t1 (Node zk zv t2 t3) -> Some (Node zk zv (Node xk xv t1 t2) t3)
  | _ -> None

let rotate_right (#k: Type) (#v: Type) (r: tree k v) : option (tree k v) =
  match r with
  | Node xk xv (Node zk zv t1 t2) t3 -> Some (Node zk zv t1 (Node xk xv t2 t3))
  | _ -> None

let rotate_right_left (#k: Type) (#v: Type) (r: tree k v) : option (tree k v) =
  match r with
  | Node xk xv t1 (Node zk zv (Node yk yv t2 t3) t4) -> Some (Node yk yv (Node xk xv t1 t2) (Node zk zv t3 t4))
  | _ -> None

let rotate_left_right (#k: Type) (#v: Type) (r: tree k v) : option (tree k v) =
  match r with
  | Node xk xv (Node zk zv t1 (Node yk yv t2 t3)) t4 -> Some (Node yk yv (Node zk zv t1 t2) (Node xk xv t3 t4))
  | _ -> None

(** rotate preserves bst *)
let rec forall_keys_trans (#k: Type) (#v: Type) (t: tree k v) (cond1 cond2: k -> bool)
  : Lemma (requires (forall x. cond1 x ==> cond2 x) /\ forall_keys t cond1)
          (ensures forall_keys t cond2)
  = match t with
  | Leaf -> ()
  | Node nd_key nd_val left right ->
    forall_keys_trans left cond1 cond2; forall_keys_trans right cond1 cond2

let rotate_left_bst (#k: Type) (#v: Type) (cmp:cmp k) (r:tree k v)
  : Lemma (requires is_bst cmp r /\ Some? (rotate_left r)) (ensures is_bst cmp (Some?.v (rotate_left r)))
  = match r with
  | Node xk xv t1 (Node zk zv t2 t3) ->
      assert (is_bst cmp (Node zk zv t2 t3));
      assert (is_bst cmp (Node xk xv t1 t2));
      forall_keys_trans t1 (key_left cmp xk) (key_left cmp zk)

let rotate_right_bst (#k: Type) (#v: Type) (cmp:cmp k) (r:tree k v)
  : Lemma (requires is_bst cmp r /\ Some? (rotate_right r)) (ensures is_bst cmp (Some?.v (rotate_right r)))
  = match r with
  | Node xk xv (Node zk zv t1 t2) t3 ->
      assert (is_bst cmp (Node zk zv t1 t2));
      assert (is_bst cmp (Node xk xv t2 t3));
      forall_keys_trans t3 (key_right cmp xk) (key_right cmp zk)

let rotate_right_left_bst (#k: Type) (#v: Type) (cmp:cmp k) (r:tree k v)
  : Lemma (requires is_bst cmp r /\ Some? (rotate_right_left r)) (ensures is_bst cmp (Some?.v (rotate_right_left r)))
  = match r with
  | Node xk xv t1 (Node zk zv (Node yk yv t2 t3) t4) ->
    assert (is_bst cmp (Node zk zv (Node yk yv t2 t3) t4));
    assert (is_bst cmp (Node yk yv t2 t3));
    let left = Node xk xv t1 t2 in
    let right = Node zk zv t3 t4 in

    assert (forall_keys (Node yk yv t2 t3) (key_right cmp xk));
    assert (forall_keys t2 (key_right cmp xk));
    assert (is_bst cmp left);

    assert (is_bst cmp right);

    forall_keys_trans t1 (key_left cmp xk) (key_left cmp yk);
    assert (forall_keys left (key_left cmp yk));

    forall_keys_trans t4 (key_right cmp zk) (key_right cmp yk);
    assert (forall_keys right (key_right cmp yk))


let rotate_left_right_bst (#k: Type) (#v: Type) (cmp:cmp k) (r:tree k v)
  : Lemma (requires is_bst cmp r /\ Some? (rotate_left_right r)) (ensures is_bst cmp (Some?.v (rotate_left_right r)))
  = match r with
  | Node xk xv (Node zk zv t1 (Node yk yv t2 t3)) t4 ->
    // Node yk yv (Node zk zv t1 t2) (Node xk xv t3 t4)
    assert (is_bst cmp (Node zk zv t1 (Node yk yv t2 t3)));
    assert (is_bst cmp (Node yk yv t2 t3));
    let left = Node zk zv t1 t2 in
    let right = Node xk xv t3 t4 in

    assert (is_bst cmp left);

    assert (forall_keys (Node yk yv t2 t3) (key_left cmp xk));
    assert (forall_keys t2 (key_left cmp xk));
    assert (is_bst cmp right);

    forall_keys_trans t1 (key_left cmp zk) (key_left cmp yk);
    assert (forall_keys left (key_left cmp yk));

    forall_keys_trans t4 (key_right cmp xk) (key_right cmp yk);
    assert (forall_keys right (key_right cmp yk))

(** Same elements before and after rotate **)

let rotate_left_key_left (#k: Type) (#v: Type) (cmp:cmp k) (r:tree k v) (root:k)
  : Lemma (requires forall_keys r (key_left cmp root) /\ Some? (rotate_left r))
          (ensures  forall_keys (Some?.v (rotate_left r)) (key_left cmp root))
  = match r with
  | Node xk xv t1 (Node zk zv t2 t3) ->
      assert (forall_keys (Node zk zv t2 t3) (key_left cmp root));
      assert (forall_keys (Node xk xv t1 t2) (key_left cmp root))

let rotate_left_key_right (#k: Type) (#v: Type) (cmp:cmp k) (r:tree k v) (root:k)
  : Lemma (requires forall_keys r (key_right cmp root) /\ Some? (rotate_left r))
          (ensures  forall_keys (Some?.v (rotate_left r)) (key_right cmp root))
  = match r with
  | Node xk xv t1 (Node zk zv t2 t3) ->
      assert (forall_keys (Node zk zv t2 t3) (key_right cmp root));
      assert (forall_keys (Node xk xv t1 t2) (key_right cmp root))

let rotate_right_key_left (#k: Type) (#v: Type) (cmp:cmp k) (r:tree k v) (root:k)
  : Lemma (requires forall_keys r (key_left cmp root) /\ Some? (rotate_right r))
          (ensures  forall_keys (Some?.v (rotate_right r)) (key_left cmp root))
  = match r with
  | Node xk xv (Node zk zv t1 t2) t3 ->
      assert (forall_keys (Node zk zv t1 t2) (key_left cmp root));
      assert (forall_keys (Node xk xv t2 t3) (key_left cmp root))

let rotate_right_key_right (#k: Type) (#v: Type) (cmp:cmp k) (r:tree k v) (root:k)
  : Lemma (requires forall_keys r (key_right cmp root) /\ Some? (rotate_right r))
          (ensures  forall_keys (Some?.v (rotate_right r)) (key_right cmp root))
  = match r with
  | Node xk xv (Node zk zv t1 t2) t3 ->
      assert (forall_keys (Node zk zv t1 t2) (key_right cmp root));
      assert (forall_keys (Node xk xv t2 t3) (key_right cmp root))

let rotate_right_left_key_left (#k: Type) (#v: Type) (cmp:cmp k) (r:tree k v) (root:k)
  : Lemma (requires forall_keys r (key_left cmp root) /\ Some? (rotate_right_left r))
          (ensures  forall_keys (Some?.v (rotate_right_left r)) (key_left cmp root))
  = match r with
  | Node xk xv t1 (Node zk zv (Node yk yv t2 t3) t4) ->
    assert (forall_keys (Node zk zv (Node yk yv t2 t3) t4) (key_left cmp root));
    assert (forall_keys (Node yk yv t2 t3) (key_left cmp root));
    let left = Node xk xv t1 t2 in
    let right = Node zk zv t3 t4 in
    assert (forall_keys left (key_left cmp root));
    assert (forall_keys right (key_left cmp root))


let rotate_right_left_key_right (#k: Type) (#v: Type) (cmp:cmp k) (r:tree k v) (root:k)
  : Lemma (requires forall_keys r (key_right cmp root) /\ Some? (rotate_right_left r))
          (ensures  forall_keys (Some?.v (rotate_right_left r)) (key_right cmp root))
  = match r with
  | Node xk xv t1 (Node zk zv (Node yk yv t2 t3) t4) ->
    assert (forall_keys (Node zk zv (Node yk yv t2 t3) t4) (key_right cmp root));
    assert (forall_keys (Node yk yv t2 t3) (key_right cmp root));
    let left = Node xk xv t1 t2 in
    let right = Node zk zv t3 t4 in
    assert (forall_keys left (key_right cmp root));
    assert (forall_keys right (key_right cmp root))

let rotate_left_right_key_left (#k: Type) (#v: Type) (cmp:cmp k) (r:tree k v) (root:k)
  : Lemma (requires forall_keys r (key_left cmp root) /\ Some? (rotate_left_right r))
          (ensures  forall_keys (Some?.v (rotate_left_right r)) (key_left cmp root))
  = match r with
  | Node xk xv (Node zk zv t1 (Node yk yv t2 t3)) t4 ->
    // Node yk yv (Node zk zv t1 t2) (Node xk xv t3 t4)
    assert (forall_keys (Node zk zv t1 (Node yk yv t2 t3)) (key_left cmp root));
    assert (forall_keys (Node yk yv t2 t3) (key_left cmp root));
    let left = Node zk zv t1 t2 in
    let right = Node xk xv t3 t4 in

    assert (forall_keys left (key_left cmp root));
    assert (forall_keys right (key_left cmp root))

let rotate_left_right_key_right (#k: Type) (#v: Type) (cmp:cmp k) (r:tree k v) (root:k)
  : Lemma (requires forall_keys r (key_right cmp root) /\ Some? (rotate_left_right r))
          (ensures  forall_keys (Some?.v (rotate_left_right r)) (key_right cmp root))
  = match r with
  | Node xk xv (Node zk zv t1 (Node yk yv t2 t3)) t4 ->
    // Node yk yv (Node zk zv t1 t2) (Node xk xv t3 t4)
    assert (forall_keys (Node zk zv t1 (Node yk yv t2 t3)) (key_right cmp root));
    assert (forall_keys (Node yk yv t2 t3) (key_right cmp root));
    let left = Node zk zv t1 t2 in
    let right = Node xk xv t3 t4 in

    assert (forall_keys left (key_right cmp root));
    assert (forall_keys right (key_right cmp root))


(** Balancing operation for AVLs *)

let rebalance_avl (#k: Type) (#v: Type) (x: tree k v) : tree k v =
    match x with
    | Leaf -> x
    | Node nd_key nd_val left right ->

      if is_balanced x then x
      else (

        if height left - height right > 1 then (
          let Node lk lv lleft lright = left in
          if height lright > height lleft then (
            match rotate_left_right x with
            | Some y -> y
            | _ -> x
          ) else (
            match rotate_right x with
            | Some y -> y
            | _ -> x
          )

        ) else if height left - height right < -1 then (
          let Node rk rv rleft rright = right in
            if height rleft > height rright then (
              match rotate_right_left x with
              | Some y -> y
              | _ -> x
            ) else (
              match rotate_left x with
              | Some y -> y
              | _ -> x
            )
        ) else (
          x
        )
      )


let rebalance_avl_proof (#k: Type) (#v: Type) (cmp:cmp k) (x: tree k v)
  (root:k)
  : Lemma
  (requires is_bst cmp x /\ (
    match x with
    | Leaf -> True
    | Node nd_key nd_val left right ->
      is_balanced left /\ is_balanced right /\
      height left - height right <= 2 /\
      height right - height left <= 2
    )
  )
  (ensures is_avl cmp (rebalance_avl x) /\
     (forall_keys x (key_left cmp root) ==> forall_keys (rebalance_avl x) (key_left cmp root)) /\
     (forall_keys x (key_right cmp root) ==> forall_keys (rebalance_avl x) (key_right cmp root))
  )
  =
    match x with
    | Leaf -> ()
    | Node nd_key nd_val left right ->
      let x_f = rebalance_avl x in
      let Node f_key f_val f_left f_right = x_f in
      if is_balanced x then ()
      else (
        if height left - height right > 1 then (
          assert (height left = height right + 2);
          let Node lk lv lleft lright = left in
          if height lright > height lleft then (
            assert (height left = height lright + 1);
            rotate_left_right_bst cmp x;
            Classical.move_requires (rotate_left_right_key_left cmp x) root;
            Classical.move_requires (rotate_left_right_key_right cmp x) root;

            let Node yk yv t2 t3 = lright in
            let Node xk xv (Node zk zv t1 (Node yk yv t2 t3)) t4 = x in
            assert (f_key == yk);
            assert (f_left == Node zk zv t1 t2);
            assert (f_right == Node xk xv t3 t4);
            assert (lright == Node yk yv t2 t3);

            // Left part

            assert (is_balanced lright);
            assert (height t1 - height t2 <= 1);

            assert (height t2 - height t1 <= 1);

            assert (is_balanced t1);

            assert (is_balanced (Node yk yv t2 t3));
            assert (is_balanced t2);

            assert (is_balanced f_left);


            // Right part
            assert (height t3 - height t4 <= 1);
            assert (height t4 - height t3 <= 1);

            assert (is_balanced t3);
            assert (is_balanced t4);
            assert (is_balanced f_right)

          ) else (
            rotate_right_bst cmp x;
            Classical.move_requires (rotate_right_key_left cmp x) root;
            Classical.move_requires (rotate_right_key_right cmp x) root;

            assert (is_balanced f_left);
            assert (is_balanced f_right);
            assert (is_balanced x_f)
          )

        ) else if height left - height right < -1 then (
          let Node rk rv rleft rright = right in
          if height rleft > height rright then (
            rotate_right_left_bst cmp x;
            Classical.move_requires (rotate_right_left_key_left cmp x) root;
            Classical.move_requires (rotate_right_left_key_right cmp x) root;

            let Node xk xv t1 (Node zk zv (Node yk yv t2 t3) t4) = x in
            assert (f_key == yk);
            assert (f_left == Node xk xv t1 t2);
            assert (f_right == Node zk zv t3 t4);

            // Right part
            assert (is_balanced rleft);
            assert (height t3 - height t4 <= 1);
            assert (height t4 - height t4 <= 1);

            assert (is_balanced (Node yk yv t2 t3));
            assert (is_balanced f_right);

            // Left part
            assert (is_balanced t1);
            assert (is_balanced t2);
            assert (is_balanced f_left)

          ) else (
            rotate_left_bst cmp x;
            Classical.move_requires (rotate_left_key_left cmp x) root;
            Classical.move_requires (rotate_left_key_right cmp x) root;

            assert (is_balanced f_left);
            assert (is_balanced f_right);
            assert (is_balanced x_f)
          )
        )
      )

(** Insertion **)

let rec insert_avl (#k: Type) (#v: Type) (cmp:cmp k) (x: tree k v) (key: k) (val_: v) : tree k v =
  match x with
  | Leaf -> Node key val_ Leaf Leaf
  | Node nd_key nd_val left right ->
    let delta = cmp nd_key key in
    if delta >= 0 then (
      let new_left = insert_avl cmp left key val_ in
      let tmp = Node nd_key nd_val new_left right in
      rebalance_avl tmp
    ) else (
      let new_right = insert_avl cmp right key val_ in
      let tmp = Node nd_key nd_val left new_right in
      rebalance_avl tmp
    )

let rec tree_max (#k: Type) (#v: Type)  (x: tree k v {Node? x}) : (k & v) =
  match x with
  | Node dk dv _ Leaf -> (dk, dv)
  | Node _ _ _ r -> tree_max r


(** Deletion *)
let rec delete_avl (#k: Type) (#v: Type) (cmp:cmp k) (x: tree k v) (key: k) : tree k v =
  match x with
  | Leaf -> Leaf
  | Node nd_key nd_val left right ->
    let delta = cmp nd_key key in
    if delta = 0 then (
      match left, right with
      | Leaf , Leaf -> Leaf
      | Node _ _ _ _ , Leaf -> left
      | Leaf , Node _ _ _ _ -> right
      | _ -> let m = tree_max left in
             let new_left = delete_avl cmp left (fst m) in
             let tmp = Node (fst m) (snd m) new_left right in
             rebalance_avl tmp
    )
    else
    (
      if delta < 0 then (
        assert (delta < 0);
        let new_right = delete_avl cmp right key in
        let tmp = Node nd_key nd_val left new_right in
        rebalance_avl tmp
      )
      else (
        assert (delta > 0);
        let new_left = delete_avl cmp left key in
        let tmp = Node nd_key nd_val new_left right in
        rebalance_avl tmp
      )
    )



#push-options "--z3rlimit 50"

let rec insert_avl_proof_aux (#k: Type) (#v: Type) (cmp:cmp k) (x: avl k v cmp) (key: k) (val_: v)
  (root:k)

  : Lemma (requires is_avl cmp x)
    (ensures (
      let res = insert_avl cmp x key val_ in
      is_avl cmp res /\
      height x <= height res /\
      height res <= height x + 1 /\
      (forall_keys x (key_left cmp root) /\ key_left cmp root key ==> forall_keys res (key_left cmp root)) /\
      (forall_keys x (key_right cmp root) /\ key_right cmp root key ==> forall_keys res (key_right cmp root)))

    )
  = match x with
  | Leaf -> ()
  | Node nd_key nd_val left right ->
    let delta = cmp nd_key key in
    if delta >= 0 then (
      let new_left = insert_avl cmp left key val_ in
      let tmp = Node nd_key nd_val new_left right in

      insert_avl_proof_aux cmp left key val_ nd_key;
      // Need this one for propagating that all elements are smaller than root
      insert_avl_proof_aux cmp left key val_ root;

      rebalance_avl_proof cmp tmp root

    ) else (
      let new_right = insert_avl cmp right key val_ in
      let tmp = Node nd_key nd_val left new_right in

      insert_avl_proof_aux cmp right key val_ nd_key;
      insert_avl_proof_aux cmp right key val_ root;

      rebalance_avl_proof cmp tmp root
    )

  

#pop-options

let insert_avl_proof (#k: Type) (#v: Type) (cmp:cmp k) (x: avl k v cmp) (key: k) (val_: v)
  : Lemma (requires is_avl cmp x) (ensures is_avl cmp (insert_avl cmp x key val_))
  = Classical.forall_intro (Classical.move_requires (insert_avl_proof_aux cmp x key val_))

/// Minimum element of a non-empty tree (leftmost)
let rec tree_min (#k: Type) (#v: Type) (x: tree k v{Node? x}) : (k & v) =
  match x with
  | Node dk dv Leaf _ -> (dk, dv)
  | Node _ _ l _ -> tree_min l

/// Find largest element <= key (predecessor query). Returns None if no such element.
let rec find_le (#k: Type) (#v: Type) (cmp: cmp k) (x: tree k v) (key: k) : option (k & v) =
  match x with
  | Leaf -> None
  | Node nd_key nd_val left right ->
    let delta = cmp nd_key key in
    if delta > 0 then
      // nd_key > key, go left
      find_le cmp left key
    else if delta = 0 then
      // nd_key = key, exact match
      Some (nd_key, nd_val)
    else
      // nd_key < key, nd_key is a candidate; check if right subtree has a better one
      match find_le cmp right key with
      | Some r -> Some r
      | None -> Some (nd_key, nd_val)

/// Find smallest element >= key (successor query). Returns None if no such element.
let rec find_ge (#k: Type) (#v: Type) (cmp: cmp k) (x: tree k v) (key: k) : option (k & v) =
  match x with
  | Leaf -> None
  | Node nd_key nd_val left right ->
    let delta = cmp nd_key key in
    if delta < 0 then
      // nd_key < key, go right
      find_ge cmp right key
    else if delta = 0 then
      // nd_key = key, exact match
      Some (nd_key, nd_val)
    else
      // nd_key > key, nd_key is a candidate; check if left subtree has a better one
      match find_ge cmp left key with
      | Some r -> Some r
      | None -> Some (nd_key, nd_val)


(*** Inorder traversal and sorted sequence correspondence *)

/// In-order traversal of a tree, producing a sequence
let rec inorder (#k: Type) (#v: Type) (t: tree k v) : Tot (Seq.seq (k & v)) (decreases t) =
  match t with
  | Leaf -> Seq.empty
  | Node dk dv l r -> Seq.append (inorder l) (Seq.cons (dk, dv) (inorder r))

/// All elements of a sequence satisfy a boolean predicate on keys
let rec seq_forall (#k: Type) (#v: Type) (f: k -> bool) (s: Seq.seq (k & v))
  : Tot bool (decreases Seq.length s) =
  if Seq.length s = 0 then true
  else f (fst (Seq.head s)) && seq_forall f (Seq.tail s)

/// A sequence is sorted w.r.t. a comparison function
let rec sorted (#k: Type) (#v: Type) (compare: cmp k) (s: Seq.seq (k & v))
  : Tot bool (decreases Seq.length s) =
  if Seq.length s <= 1 then true
  else compare (fst (Seq.head s)) (fst (Seq.index s 1)) <= 0 && sorted compare (Seq.tail s)

/// Insert an element at the correct position in a sorted sequence
let rec sorted_insert (#k: Type) (#v: Type) (compare: cmp k) (kv: (k & v)) (s: Seq.seq (k & v))
  : Tot (Seq.seq (k & v)) (decreases Seq.length s) =
  if Seq.length s = 0 then Seq.create 1 kv
  else
    let hd = Seq.head s in
    if compare (fst hd) (fst kv) >= 0 then
      Seq.cons kv s
    else
      Seq.cons hd (sorted_insert compare kv (Seq.tail s))

/// Remove the first occurrence of an element equal to key from a sorted sequence
let rec sorted_remove (#k: Type) (#v: Type) (compare: cmp k) (key: k) (s: Seq.seq (k & v))
  : Tot (Seq.seq (k & v)) (decreases Seq.length s) =
  if Seq.length s = 0 then Seq.empty
  else
    let hd = Seq.head s in
    if compare (fst hd) key = 0 then Seq.tail s
    else Seq.cons hd (sorted_remove compare key (Seq.tail s))

(** A2: Rotation lemmas — rotations preserve inorder traversal *)

#push-options "--fuel 3 --z3rlimit 40"

let rotate_left_inorder (#k: Type) (#v: Type) (r: tree k v)
  : Lemma (requires Some? (rotate_left r))
          (ensures Seq.equal (inorder (Some?.v (rotate_left r))) (inorder r))
  = match r with
  | Node xk xv t1 (Node zk zv t2 t3) ->
    Seq.append_assoc (inorder t1) (Seq.cons (xk, xv) (inorder t2)) (Seq.cons (zk, zv) (inorder t3))

let rotate_right_inorder (#k: Type) (#v: Type) (r: tree k v)
  : Lemma (requires Some? (rotate_right r))
          (ensures Seq.equal (inorder (Some?.v (rotate_right r))) (inorder r))
  = match r with
  | Node xk xv (Node zk zv t1 t2) t3 ->
    Seq.append_assoc (inorder t1) (Seq.cons (zk, zv) (inorder t2)) (Seq.cons (xk, xv) (inorder t3))

let rotate_right_left_inorder (#k: Type) (#v: Type) (r: tree k v)
  : Lemma (requires Some? (rotate_right_left r))
          (ensures Seq.equal (inorder (Some?.v (rotate_right_left r))) (inorder r))
  = match r with
  | Node xk xv t1 (Node zk zv (Node yk yv t2 t3) t4) ->
    let l1 = inorder t1 in let l2 = inorder t2 in
    let l3 = inorder t3 in let l4 = inorder t4 in
    // Original: l1 ++ cons x ((l2 ++ cons y l3) ++ cons z l4)
    // Target:   (l1 ++ cons x l2) ++ cons y (l3 ++ cons z l4)
    Seq.append_assoc l2 (Seq.cons (yk, yv) l3) (Seq.cons (zk, zv) l4);
    Seq.append_assoc (Seq.create 1 (yk, yv)) l3 (Seq.cons (zk, zv) l4);
    Seq.append_assoc (Seq.create 1 (xk, xv)) l2 (Seq.cons (yk, yv) (Seq.append l3 (Seq.cons (zk, zv) l4)));
    Seq.append_assoc l1 (Seq.cons (xk, xv) l2) (Seq.cons (yk, yv) (Seq.append l3 (Seq.cons (zk, zv) l4)))

let rotate_left_right_inorder (#k: Type) (#v: Type) (r: tree k v)
  : Lemma (requires Some? (rotate_left_right r))
          (ensures Seq.equal (inorder (Some?.v (rotate_left_right r))) (inorder r))
  = match r with
  | Node xk xv (Node zk zv t1 (Node yk yv t2 t3)) t4 ->
    let l1 = inorder t1 in let l2 = inorder t2 in
    let l3 = inorder t3 in let l4 = inorder t4 in
    // Original: (l1 ++ cons z (l2 ++ cons y l3)) ++ cons x l4
    // Target:   (l1 ++ cons z l2) ++ cons y (l3 ++ cons x l4)
    Seq.append_assoc (Seq.create 1 (zk, zv)) l2 (Seq.cons (yk, yv) l3);
    Seq.append_assoc l1 (Seq.cons (zk, zv) l2) (Seq.cons (yk, yv) l3);
    Seq.append_assoc (Seq.append l1 (Seq.cons (zk, zv) l2)) (Seq.cons (yk, yv) l3) (Seq.cons (xk, xv) l4);
    Seq.append_assoc (Seq.create 1 (yk, yv)) l3 (Seq.cons (xk, xv) l4)

let rebalance_inorder (#k: Type) (#v: Type) (t: tree k v)
  : Lemma (ensures Seq.equal (inorder (rebalance_avl t)) (inorder t))
  = match t with
  | Leaf -> ()
  | Node nd_key nd_val left right ->
    if is_balanced t then ()
    else if height left - height right > 1 then (
      let Node lk lv lleft lright = left in
      if height lright > height lleft then
        rotate_left_right_inorder t
      else
        rotate_right_inorder t
    ) else if height left - height right < -1 then (
      let Node rk rv rleft rright = right in
      if height rleft > height rright then
        rotate_right_left_inorder t
      else
        rotate_left_inorder t
    ) else ()

#pop-options

(** A3: BST implies sorted inorder *)

#push-options "--fuel 2 --z3rlimit 40"

/// Helper: seq_forall distributes over cons
let seq_forall_cons (#k: Type) (#v: Type) (f: k -> bool) (kv: (k & v)) (s: Seq.seq (k & v))
  : Lemma (requires f (fst kv) /\ seq_forall f s)
          (ensures seq_forall f (Seq.cons kv s))
  = let s' = Seq.cons kv s in
    Seq.lemma_head_append (Seq.create 1 kv) s;
    Seq.lemma_tail_append (Seq.create 1 kv) s;
    assert (Seq.head s' == kv);
    assert (Seq.equal (Seq.tail s') s)

/// Helper: seq_forall distributes over append
let rec seq_forall_append (#k: Type) (#v: Type) (f: k -> bool) (s1 s2: Seq.seq (k & v))
  : Lemma (requires seq_forall f s1 /\ seq_forall f s2)
          (ensures seq_forall f (Seq.append s1 s2))
          (decreases Seq.length s1)
  = if Seq.length s1 = 0 then (
      assert (Seq.equal s1 (Seq.empty #(k & v)));
      assert (Seq.equal (Seq.append s1 s2) s2)
    ) else (
      seq_forall_append f (Seq.tail s1) s2;
      Seq.lemma_head_append s1 s2;
      Seq.lemma_tail_append s1 s2
    )

/// Bridge: forall_keys on tree implies seq_forall on inorder
let rec forall_keys_inorder (#k: Type) (#v: Type) (t: tree k v) (cond: k -> bool)
  : Lemma (requires forall_keys t cond)
          (ensures seq_forall cond (inorder t))
          (decreases t)
  = match t with
  | Leaf -> ()
  | Node dk dv l r ->
    forall_keys_inorder l cond;
    forall_keys_inorder r cond;
    seq_forall_cons cond (dk, dv) (inorder r);
    seq_forall_append cond (inorder l) (Seq.cons (dk, dv) (inorder r))

/// Helper: sorted left + all left ≤ d + d ≤ all right + sorted right → sorted (left ++ [d] ++ right)

let sorted_cons_right (#k: Type) (#v: Type) (compare: cmp k) (d: (k & v)) (s: Seq.seq (k & v))
  : Lemma (requires sorted compare s /\ (Seq.length s > 0 ==> compare (fst d) (fst (Seq.head s)) <= 0))
          (ensures sorted compare (Seq.cons d s))
  = let cs = Seq.cons d s in
    Seq.lemma_head_append (Seq.create 1 d) s;
    Seq.lemma_tail_append (Seq.create 1 d) s;
    assert (Seq.head cs == d);
    assert (Seq.equal (Seq.tail cs) s);
    if Seq.length s = 0 then ()
    else (
      assert (Seq.index cs 1 == Seq.head s)
    )

let rec sorted_append (#k: Type) (#v: Type) (compare: cmp k) (s1: Seq.seq (k & v)) (d: (k & v)) (s2: Seq.seq (k & v))
  : Lemma (requires
      sorted compare s1 /\
      sorted compare s2 /\
      seq_forall (key_left compare (fst d)) s1 /\
      seq_forall (key_right compare (fst d)) s2)
    (ensures sorted compare (Seq.append s1 (Seq.cons d s2)))
    (decreases Seq.length s1)
  = let ds2 = Seq.cons d s2 in
    if Seq.length s1 = 0 then (
      assert (Seq.equal s1 (Seq.empty #(k & v)));
      assert (Seq.equal (Seq.append s1 ds2) ds2);
      sorted_cons_right compare d s2
    ) else (
      let hd = Seq.head s1 in
      let tl = Seq.tail s1 in
      sorted_append compare tl d s2;
      Seq.lemma_head_append s1 ds2;
      Seq.lemma_tail_append s1 ds2;
      if Seq.length tl = 0 then (
        assert (Seq.equal tl (Seq.empty #(k & v)));
        assert (Seq.equal (Seq.append tl ds2) ds2);
        Seq.lemma_head_append (Seq.create 1 d) s2;
        assert (key_left compare (fst d) (fst hd))
      ) else (
        Seq.lemma_head_append tl ds2
      )
    )

/// The main theorem: BST inorder is sorted
let rec is_bst_sorted_inorder (#k: Type) (#v: Type) (compare: cmp k) (t: tree k v)
  : Lemma (requires is_bst compare t)
          (ensures sorted compare (inorder t))
          (decreases t)
  = match t with
  | Leaf -> ()
  | Node dk dv l r ->
    is_bst_sorted_inorder compare l;
    is_bst_sorted_inorder compare r;
    forall_keys_inorder l (key_left compare dk);
    forall_keys_inorder r (key_right compare dk);
    sorted_append compare (inorder l) (dk, dv) (inorder r)

#pop-options

(** A4: Insert correspondence — inorder(insert_bst t k) == sorted_insert k (inorder t) *)

#push-options "--fuel 3 --z3rlimit 60"

/// Helper: sorted_insert into append — kv goes left when d >= kv
let rec sorted_insert_append_left (#k: Type) (#v: Type) (compare: cmp k) (s1: Seq.seq (k & v)) (d: (k & v)) (s2: Seq.seq (k & v)) (kv: (k & v))
  : Lemma
    (requires sorted compare (Seq.append s1 (Seq.cons d s2)) /\
             seq_forall (key_left compare (fst d)) s1 /\
             seq_forall (key_right compare (fst d)) s2 /\
             compare (fst d) (fst kv) >= 0)
    (ensures Seq.equal
      (sorted_insert compare kv (Seq.append s1 (Seq.cons d s2)))
      (Seq.append (sorted_insert compare kv s1) (Seq.cons d s2)))
    (decreases Seq.length s1)
  = if Seq.length s1 = 0 then (
      assert (Seq.equal s1 (Seq.empty #(k & v)));
      assert (Seq.equal (Seq.append s1 (Seq.cons d s2)) (Seq.cons d s2));
      Seq.lemma_head_append (Seq.create 1 d) s2;
      assert (Seq.head (Seq.cons d s2) == d)
    ) else (
      let hd = Seq.head s1 in
      let tl = Seq.tail s1 in
      Seq.lemma_head_append s1 (Seq.cons d s2);
      Seq.lemma_tail_append s1 (Seq.cons d s2);
      if compare (fst hd) (fst kv) >= 0 then ()
      else
        sorted_insert_append_left compare tl d s2 kv
    )

/// Helper: sorted_insert into append — kv goes right when d < kv
let rec sorted_insert_append_right (#k: Type) (#v: Type) (compare: cmp k) (s1: Seq.seq (k & v)) (d: (k & v)) (s2: Seq.seq (k & v)) (kv: (k & v))
  : Lemma
    (requires sorted compare (Seq.append s1 (Seq.cons d s2)) /\
             seq_forall (key_left compare (fst d)) s1 /\
             seq_forall (key_right compare (fst d)) s2 /\
             compare (fst d) (fst kv) < 0)
    (ensures Seq.equal
      (sorted_insert compare kv (Seq.append s1 (Seq.cons d s2)))
      (Seq.append s1 (Seq.cons d (sorted_insert compare kv s2))))
    (decreases Seq.length s1)
  = if Seq.length s1 = 0 then (
      assert (Seq.equal s1 (Seq.empty #(k & v)));
      assert (Seq.equal (Seq.append s1 (Seq.cons d s2)) (Seq.cons d s2));
      Seq.lemma_head_append (Seq.create 1 d) s2;
      Seq.lemma_tail_append (Seq.create 1 d) s2;
      assert (Seq.equal (Seq.tail (Seq.cons d s2)) s2)
    ) else (
      let hd = Seq.head s1 in
      let tl = Seq.tail s1 in
      Seq.lemma_head_append s1 (Seq.cons d s2);
      Seq.lemma_tail_append s1 (Seq.cons d s2);
      assert (key_left compare (fst d) (fst hd));
      sorted_insert_append_right compare tl d s2 kv
    )

/// inorder(insert_bst t k) == sorted_insert k (inorder t)
let rec insert_bst_inorder (#k: Type) (#v: Type) (compare: cmp k) (t: bst k v compare) (key: k) (val_: v)
  : Lemma (ensures Seq.equal (inorder (insert_bst compare t key val_)) (sorted_insert compare (key, val_) (inorder t)))
          (decreases t)
  = match t with
  | Leaf -> ()
  | Node dk dv l r ->
    let delta = compare dk key in
    is_bst_sorted_inorder compare t;
    forall_keys_inorder l (key_left compare dk);
    forall_keys_inorder r (key_right compare dk);
    if delta >= 0 then (
      insert_bst_inorder compare l key val_;
      sorted_insert_append_left compare (inorder l) (dk, dv) (inorder r) (key, val_)
    ) else (
      insert_bst_inorder compare r key val_;
      sorted_insert_append_right compare (inorder l) (dk, dv) (inorder r) (key, val_)
    )

/// inorder(insert_avl t k) == sorted_insert k (inorder t)
let rec insert_avl_inorder (#k: Type) (#v: Type) (compare: cmp k) (t: avl k v compare) (key: k) (val_: v)
  : Lemma (ensures Seq.equal (inorder (insert_avl compare t key val_)) (sorted_insert compare (key, val_) (inorder t)))
          (decreases t)
  = match t with
  | Leaf -> ()
  | Node dk dv l r ->
    let delta = compare dk key in
    is_bst_sorted_inorder compare t;
    forall_keys_inorder l (key_left compare dk);
    forall_keys_inorder r (key_right compare dk);
    if delta >= 0 then (
      insert_avl_inorder compare l key val_;
      let new_left = insert_avl compare l key val_ in
      let tmp = Node dk dv new_left r in
      rebalance_inorder tmp;
      sorted_insert_append_left compare (inorder l) (dk, dv) (inorder r) (key, val_)
    ) else (
      insert_avl_inorder compare r key val_;
      let new_right = insert_avl compare r key val_ in
      let tmp = Node dk dv l new_right in
      rebalance_inorder tmp;
      sorted_insert_append_right compare (inorder l) (dk, dv) (inorder r) (key, val_)
    )

#pop-options

(** A5: Delete correspondence — inorder(delete_avl t k) == sorted_remove k (inorder t) *)

#push-options "--fuel 3 --z3rlimit 60"

/// tree_max is the last element of inorder
let rec tree_max_last_inorder (#k: Type) (#v: Type) (t: tree k v{Node? t})
  : Lemma (ensures Seq.length (inorder t) > 0 /\
                   tree_max t == Seq.index (inorder t) (Seq.length (inorder t) - 1))
          (decreases t)
  = match t with
  | Node dk dv l Leaf ->
    Seq.lemma_len_append (inorder l) (Seq.cons (dk, dv) Seq.empty);
    Seq.lemma_index_app2 (inorder l) (Seq.cons (dk, dv) Seq.empty) (Seq.length (inorder l) + 1 - 1)
  | Node dk dv l r ->
    tree_max_last_inorder r;
    let ir = inorder r in
    Seq.lemma_len_append (inorder l) (Seq.cons (dk, dv) ir);
    let full = Seq.append (inorder l) (Seq.cons (dk, dv) ir) in
    let full_len = Seq.length full in
    Seq.lemma_index_app2 (inorder l) (Seq.cons (dk, dv) ir) (full_len - 1);
    let idx_in_cons = full_len - 1 - Seq.length (inorder l) in
    Seq.lemma_index_app2 (Seq.create 1 (dk, dv)) ir idx_in_cons

/// Helper: sorted_remove on a sequence that doesn't contain key is identity
let rec sorted_remove_absent (#k: Type) (#v: Type) (compare: cmp k) (key: k) (s: Seq.seq (k & v))
  : Lemma (requires (forall (i:nat). i < Seq.length s ==> compare (fst (Seq.index s i)) key <> 0))
          (ensures Seq.equal (sorted_remove compare key s) s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (
      assert (compare (fst (Seq.index s 0)) key <> 0);
      assert (compare (fst (Seq.head s)) key <> 0);
      sorted_remove_absent compare key (Seq.tail s)
    )

/// seq_forall implies pointwise condition
let rec seq_forall_index (#k: Type) (#v: Type) (f: k -> bool) (s: Seq.seq (k & v))
  : Lemma (requires seq_forall f s)
          (ensures forall (i:nat). i < Seq.length s ==> f (fst (Seq.index s i)))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (
      seq_forall_index f (Seq.tail s);
      let aux (i:nat{i < Seq.length s}) : Lemma (f (fst (Seq.index s i))) =
        if i = 0 then ()
        else (
          assert (i - 1 < Seq.length (Seq.tail s));
          assert (Seq.index s i == Seq.index (Seq.tail s) (i - 1))
        )
      in
      Classical.forall_intro (fun (i:nat{i < Seq.length s}) -> aux i)
    )

/// Helper: sorted_remove on append when key < all of s1 — passes through s1 to find d
let rec sorted_remove_append_left (#k: Type) (#v: Type) (compare: cmp k) (s1: Seq.seq (k & v)) (d: (k & v)) (s2: Seq.seq (k & v)) (key: k)
  : Lemma
    (requires sorted compare (Seq.append s1 (Seq.cons d s2)) /\
             seq_forall (key_left compare (fst d)) s1 /\
             seq_forall (key_right compare (fst d)) s2 /\
             compare (fst d) key > 0)
    (ensures Seq.equal
      (sorted_remove compare key (Seq.append s1 (Seq.cons d s2)))
      (Seq.append (sorted_remove compare key s1) (Seq.cons d s2)))
    (decreases Seq.length s1)
  = if Seq.length s1 = 0 then (
      assert (Seq.equal s1 (Seq.empty #(k & v)));
      assert (Seq.equal (Seq.append s1 (Seq.cons d s2)) (Seq.cons d s2));
      Seq.lemma_head_append (Seq.create 1 d) s2;
      Seq.lemma_tail_append (Seq.create 1 d) s2;
      assert (Seq.head (Seq.cons d s2) == d);
      assert (compare (fst d) key <> 0);
      // key < d <= all of s2, so key not in s2
      seq_forall_index (key_right compare (fst d)) s2;
      sorted_remove_absent compare key s2;
      assert (Seq.equal (sorted_remove compare key s2) s2);
      assert (Seq.equal (Seq.tail (Seq.cons d s2)) s2);
      assert (Seq.equal (Seq.append (Seq.empty #(k & v)) (Seq.cons d s2)) (Seq.cons d s2))
    ) else (
      let hd = Seq.head s1 in
      let tl = Seq.tail s1 in
      Seq.lemma_head_append s1 (Seq.cons d s2);
      Seq.lemma_tail_append s1 (Seq.cons d s2);
      if compare (fst hd) key = 0 then ()
      else
        sorted_remove_append_left compare tl d s2 key
    )

/// Helper: sorted_remove on append when key goes right past d
let rec sorted_remove_append_right (#k: Type) (#v: Type) (compare: cmp k) (s1: Seq.seq (k & v)) (d: (k & v)) (s2: Seq.seq (k & v)) (key: k)
  : Lemma
    (requires sorted compare (Seq.append s1 (Seq.cons d s2)) /\
             seq_forall (key_left compare (fst d)) s1 /\
             seq_forall (key_right compare (fst d)) s2 /\
             compare (fst d) key < 0)
    (ensures Seq.equal
      (sorted_remove compare key (Seq.append s1 (Seq.cons d s2)))
      (Seq.append s1 (Seq.cons d (sorted_remove compare key s2))))
    (decreases Seq.length s1)
  = if Seq.length s1 = 0 then (
      assert (Seq.equal s1 (Seq.empty #(k & v)));
      assert (Seq.equal (Seq.append s1 (Seq.cons d s2)) (Seq.cons d s2));
      Seq.lemma_head_append (Seq.create 1 d) s2;
      Seq.lemma_tail_append (Seq.create 1 d) s2;
      assert (Seq.equal (Seq.tail (Seq.cons d s2)) s2);
      assert (compare (fst d) key <> 0)
    ) else (
      let hd = Seq.head s1 in
      let tl = Seq.tail s1 in
      Seq.lemma_head_append s1 (Seq.cons d s2);
      Seq.lemma_tail_append s1 (Seq.cons d s2);
      assert (key_left compare (fst d) (fst hd));
      // compare (fst d) (fst hd) >= 0, compare (fst d) key < 0, so compare hd key <= compare hd d <= 0 < compare key (fst d)
      // Actually we need compare hd key != 0. Since d >= hd and d < key, we have hd <= d < key, so hd < key
      // meaning compare hd key < 0 != 0.
      assert (compare (fst d) (fst hd) >= 0);
      // By transitivity: hd <= d and d < key means hd < key means compare hd key < 0
      sorted_remove_append_right compare tl d s2 key
    )

/// Helper: sorted_remove on append when key = d — removes d from middle
/// Requires: no element in s1 compares equal to d (strict BST left property)
let rec sorted_remove_append_mid (#k: Type) (#v: Type) (compare: cmp k) (s1: Seq.seq (k & v)) (d: (k & v)) (s2: Seq.seq (k & v))
  : Lemma
    (requires sorted compare (Seq.append s1 (Seq.cons d s2)) /\
             seq_forall (key_left compare (fst d)) s1 /\
             (forall (i:nat). i < Seq.length s1 ==> compare (fst (Seq.index s1 i)) (fst d) <> 0))
    (ensures Seq.equal
      (sorted_remove compare (fst d) (Seq.append s1 (Seq.cons d s2)))
      (Seq.append s1 s2))
    (decreases Seq.length s1)
  = if Seq.length s1 = 0 then (
      assert (Seq.equal s1 (Seq.empty #(k & v)));
      assert (Seq.equal (Seq.append s1 (Seq.cons d s2)) (Seq.cons d s2));
      Seq.lemma_head_append (Seq.create 1 d) s2;
      Seq.lemma_tail_append (Seq.create 1 d) s2;
      assert (Seq.equal (Seq.tail (Seq.cons d s2)) s2);
      assert (compare (fst d) (fst d) = 0);
      assert (Seq.equal (Seq.append s1 s2) s2)
    ) else (
      let hd = Seq.head s1 in
      let tl = Seq.tail s1 in
      Seq.lemma_head_append s1 (Seq.cons d s2);
      Seq.lemma_tail_append s1 (Seq.cons d s2);
      assert (compare (fst (Seq.index s1 0)) (fst d) <> 0);
      assert (compare (fst hd) (fst d) <> 0);
      sorted_remove_append_mid compare tl d s2
    )

/// No-duplicate tree: each node's data is compare-distinct from all subtree elements
let rec no_dup_tree (#k: Type) (#v: Type) (compare: cmp k) (t: tree k v) : Tot bool (decreases t) =
  match t with
  | Leaf -> true
  | Node dk dv l r ->
    forall_keys l (fun x -> compare dk x <> 0) &&
    forall_keys r (fun x -> compare dk x <> 0) &&
    no_dup_tree compare l &&
    no_dup_tree compare r

/// forall_keys on tree implies condition on tree_max
let rec forall_keys_tree_max (#k: Type) (#v: Type) (t: tree k v) (f: k -> bool)
  : Lemma (requires forall_keys t f /\ Node? t)
          (ensures f (fst (tree_max t)))
          (decreases t)
  = match t with
  | Node _ _ _ Leaf -> ()
  | Node _ _ _ r -> forall_keys_tree_max r f

/// sorted_remove is invariant under compare-equal key substitution
let rec sorted_remove_cmp_eq (#k: Type) (#v: Type) (compare: cmp k) (k1 k2: k) (s: Seq.seq (k & v))
  : Lemma (requires compare k1 k2 = 0)
          (ensures Seq.equal (sorted_remove compare k1 s) (sorted_remove compare k2 s))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else if compare (fst (Seq.head s)) k1 = 0 then ()
    else sorted_remove_cmp_eq compare k1 k2 (Seq.tail s)

/// Helper to decompose no_dup_tree at a Node
let no_dup_tree_node (#k: Type) (#v: Type) (compare: cmp k) (dk: k) (dv: v) (l r: tree k v)
  : Lemma (requires no_dup_tree compare (Node dk dv l r))
          (ensures forall_keys l (fun x -> compare dk x <> 0) /\
                   forall_keys r (fun x -> compare dk x <> 0) /\
                   no_dup_tree compare l /\
                   no_dup_tree compare r)
  = normalize_term_spec (no_dup_tree compare (Node dk dv l r))

/// Removing tree_max from inorder and re-appending gives back inorder
let rec remove_max_reappend (#k: Type) (#v: Type) (compare: cmp k) (t: tree k v)
  : Lemma (requires is_bst compare t /\ no_dup_tree compare t /\ Node? t)
          (ensures (let m = tree_max t in
                    Seq.equal (Seq.append (sorted_remove compare (fst m) (inorder t)) (Seq.create 1 m)) (inorder t)))
          (decreases t)
  = match t with
  | Node dk dv l Leaf ->
    no_dup_tree_node compare dk dv l Leaf;
    is_bst_sorted_inorder compare t;
    forall_keys_inorder l (key_left compare dk);
    forall_keys_inorder l (fun x -> compare dk x <> 0);
    seq_forall_index (fun x -> compare dk x <> 0) (inorder l);
    sorted_remove_append_mid compare (inorder l) (dk, dv) (Seq.empty #(k & v));
    Seq.append_assoc (inorder l) (Seq.empty #(k & v)) (Seq.create 1 (dk, dv))
  | Node dk dv l r ->
    no_dup_tree_node compare dk dv l r;
    let m = tree_max r in
    remove_max_reappend compare r;
    is_bst_sorted_inorder compare t;
    forall_keys_inorder l (key_left compare dk);
    forall_keys_inorder r (key_right compare dk);
    forall_keys_tree_max r (fun x -> compare dk x <> 0);
    forall_keys_tree_max r (key_right compare dk);
    assert (compare dk (fst m) <> 0 /\ compare dk (fst m) <= 0);
    sorted_remove_append_right compare (inorder l) (dk, dv) (inorder r) (fst m);
    Seq.append_assoc (inorder l) (Seq.cons (dk, dv) (sorted_remove compare (fst m) (inorder r))) (Seq.create 1 m);
    Seq.append_assoc (Seq.create 1 (dk, dv)) (sorted_remove compare (fst m) (inorder r)) (Seq.create 1 m)

/// inorder(delete_avl t k) == sorted_remove k (inorder t) (requires no-dup BST)
let rec delete_avl_inorder (#k: Type) (#v: Type) (compare: cmp k) (t: tree k v) (key: k)
  : Lemma (requires is_bst compare t /\ no_dup_tree compare t)
          (ensures Seq.equal (inorder (delete_avl compare t key)) (sorted_remove compare key (inorder t)))
          (decreases t)
  = match t with
  | Leaf -> ()
  | Node dk dv l r ->
    no_dup_tree_node compare dk dv l r;
    let delta = compare dk key in
    is_bst_sorted_inorder compare t;
    forall_keys_inorder l (key_left compare dk);
    forall_keys_inorder r (key_right compare dk);
    if delta = 0 then (
      match l, r with
      | Leaf, Leaf ->
        Seq.lemma_head_append (Seq.create 1 (dk, dv)) (Seq.empty #(k & v));
        Seq.lemma_tail_append (Seq.create 1 (dk, dv)) (Seq.empty #(k & v))
      | Node _ _ _ _, Leaf ->
        forall_keys_inorder l (fun x -> compare dk x <> 0);
        seq_forall_index (fun x -> compare dk x <> 0) (inorder l);
        sorted_remove_append_mid compare (inorder l) (dk, dv) (Seq.empty #(k & v));
        sorted_remove_cmp_eq compare dk key (Seq.append (inorder l) (Seq.cons (dk, dv) (Seq.empty #(k & v))))
      | Leaf, Node _ _ _ _ ->
        Seq.lemma_head_append (Seq.create 1 (dk, dv)) (inorder r);
        Seq.lemma_tail_append (Seq.create 1 (dk, dv)) (inorder r)
      | _ ->
        let m = tree_max l in
        // IH: inorder(delete l m) = sorted_remove m (inorder l)
        delete_avl_inorder compare l (fst m);
        // rebalance preserves inorder
        rebalance_inorder (Node (fst m) (snd m) (delete_avl compare l (fst m)) r);
        // remove_max_reappend: sorted_remove m (inorder l) ++ [m] = inorder l
        remove_max_reappend compare l;
        // Use assoc to show: sr_m_l ++ [m] ++ inorder r = inorder l ++ inorder r
        Seq.append_assoc (sorted_remove compare (fst m) (inorder l)) (Seq.create 1 m) (inorder r);
        // RHS: sorted_remove key (inorder t) = inorder l ++ inorder r
        forall_keys_inorder l (fun x -> compare dk x <> 0);
        seq_forall_index (fun x -> compare dk x <> 0) (inorder l);
        sorted_remove_append_mid compare (inorder l) (dk, dv) (inorder r);
        sorted_remove_cmp_eq compare dk key (Seq.append (inorder l) (Seq.cons (dk, dv) (inorder r)))
    ) else if delta < 0 then (
      // data < key, recurse on right (fixed)
      delete_avl_inorder compare r key;
      rebalance_inorder (Node dk dv l (delete_avl compare r key));
      sorted_remove_append_right compare (inorder l) (dk, dv) (inorder r) key
    ) else (
      // data > key, recurse on left (fixed)
      delete_avl_inorder compare l key;
      rebalance_inorder (Node dk dv (delete_avl compare l key) r);
      sorted_remove_append_left compare (inorder l) (dk, dv) (inorder r) key
    )

(** A6: Membership correspondence *)

// TODO: mem_inorder needs rework for (k & v) pairs
// mem t x checks key membership, but Seq.mem operates on (k & v) pairs

#pop-options

(** A7: delete_avl preserves BST *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

/// tree_max is maximal — all keys in tree satisfy key_left cmp (fst (tree_max t)
let rec tree_max_is_maximal (#k: Type) (#v: Type) (cmp: cmp k) (t: tree k v)
  : Lemma (requires Node? t /\ is_bst cmp t)
          (ensures forall_keys t (key_left cmp (fst (tree_max t))))
          (decreases t)
  = match t with
    | Node dk dv l Leaf -> ()
    | Node dk dv l r ->
      tree_max_is_maximal cmp r;
      forall_keys_tree_max r (key_right cmp dk);
      forall_keys_trans l (key_left cmp dk) (key_left cmp (fst (tree_max r)))

/// rebalance_avl preserves is_bst
let rebalance_bst (#k: Type) (#v: Type) (cmp: cmp k) (t: tree k v)
  : Lemma (requires is_bst cmp t)
          (ensures is_bst cmp (rebalance_avl t))
  = match t with
    | Leaf -> ()
    | Node nd_key nd_val left right ->
      if is_balanced t then ()
      else if height left - height right > 1 then (
        let Node lk lv lleft lright = left in
        if height lright > height lleft then
          rotate_left_right_bst cmp t
        else
          rotate_right_bst cmp t
      ) else if height left - height right < -1 then (
        let Node rk rv rleft rright = right in
        if height rleft > height rright then
          rotate_right_left_bst cmp t
        else
          rotate_left_bst cmp t
      ) else ()

/// rebalance_avl preserves forall_keys for key_left
let rebalance_forall_left (#k: Type) (#v: Type) (cmp: cmp k) (t: tree k v) (root: k)
  : Lemma (requires is_bst cmp t /\ forall_keys t (key_left cmp root))
          (ensures forall_keys (rebalance_avl t) (key_left cmp root))
  = match t with
    | Leaf -> ()
    | Node nd_key nd_val left right ->
      if is_balanced t then ()
      else if height left - height right > 1 then (
        let Node lk lv lleft lright = left in
        if height lright > height lleft then
          rotate_left_right_key_left cmp t root
        else
          rotate_right_key_left cmp t root
      ) else if height left - height right < -1 then (
        let Node rk rv rleft rright = right in
        if height rleft > height rright then
          rotate_right_left_key_left cmp t root
        else
          rotate_left_key_left cmp t root
      ) else ()

/// rebalance_avl preserves forall_keys for key_right
let rebalance_forall_right (#k: Type) (#v: Type) (cmp: cmp k) (t: tree k v) (root: k)
  : Lemma (requires is_bst cmp t /\ forall_keys t (key_right cmp root))
          (ensures forall_keys (rebalance_avl t) (key_right cmp root))
  = match t with
    | Leaf -> ()
    | Node nd_key nd_val left right ->
      if is_balanced t then ()
      else if height left - height right > 1 then (
        let Node lk lv lleft lright = left in
        if height lright > height lleft then
          rotate_left_right_key_right cmp t root
        else
          rotate_right_key_right cmp t root
      ) else if height left - height right < -1 then (
        let Node rk rv rleft rright = right in
        if height rleft > height rright then
          rotate_right_left_key_right cmp t root
        else
          rotate_left_key_right cmp t root
      ) else ()

#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"

let rec delete_avl_proof_aux (#k: Type) (#v: Type) (cmp: cmp k) (t: tree k v) (key: k) (root: k)
  : Lemma (requires is_bst cmp t)
          (ensures (
            let res = delete_avl cmp t key in
            is_bst cmp res /\
            (forall_keys t (key_left cmp root) ==> forall_keys res (key_left cmp root)) /\
            (forall_keys t (key_right cmp root) ==> forall_keys res (key_right cmp root))
          ))
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node nd_key nd_val left right ->
      let delta = cmp nd_key key in
      if delta = 0 then (
        match left, right with
        | Leaf, Leaf -> ()
        | Node _ _ _ _, Leaf -> ()
        | Leaf, Node _ _ _ _ -> ()
        | _, _ ->
          let m = tree_max left in
          delete_avl_proof_aux cmp left (fst m) nd_key;
          delete_avl_proof_aux cmp left (fst m) (fst m);
          delete_avl_proof_aux cmp left (fst m) root;
          let new_left = delete_avl cmp left (fst m) in
          let tmp = Node (fst m) (snd m) new_left right in
          tree_max_is_maximal cmp left;
          forall_keys_tree_max left (key_left cmp nd_key);
          forall_keys_trans right (key_right cmp nd_key) (key_right cmp (fst m));
          rebalance_bst cmp tmp;
          let aux_left () : Lemma (forall_keys t (key_left cmp root) ==> forall_keys (rebalance_avl tmp) (key_left cmp root)) =
            if forall_keys t (key_left cmp root) then (
              forall_keys_tree_max left (key_left cmp root);
              assert (forall_keys tmp (key_left cmp root));
              rebalance_forall_left cmp tmp root
            )
          in
          aux_left ();
          let aux_right () : Lemma (forall_keys t (key_right cmp root) ==> forall_keys (rebalance_avl tmp) (key_right cmp root)) =
            if forall_keys t (key_right cmp root) then (
              forall_keys_tree_max left (key_right cmp root);
              assert (forall_keys tmp (key_right cmp root));
              rebalance_forall_right cmp tmp root
            )
          in
          aux_right ()
      ) else if delta < 0 then (
        delete_avl_proof_aux cmp right key nd_key;
        delete_avl_proof_aux cmp right key root;
        let new_right = delete_avl cmp right key in
        let tmp = Node nd_key nd_val left new_right in
        rebalance_bst cmp tmp;
        let aux_left () : Lemma (forall_keys t (key_left cmp root) ==> forall_keys (rebalance_avl tmp) (key_left cmp root)) =
          if forall_keys t (key_left cmp root) then (
            assert (forall_keys tmp (key_left cmp root));
            rebalance_forall_left cmp tmp root
          )
        in
        aux_left ();
        let aux_right () : Lemma (forall_keys t (key_right cmp root) ==> forall_keys (rebalance_avl tmp) (key_right cmp root)) =
          if forall_keys t (key_right cmp root) then (
            assert (forall_keys tmp (key_right cmp root));
            rebalance_forall_right cmp tmp root
          )
        in
        aux_right ()
      ) else (
        delete_avl_proof_aux cmp left key nd_key;
        delete_avl_proof_aux cmp left key root;
        let new_left = delete_avl cmp left key in
        let tmp = Node nd_key nd_val new_left right in
        rebalance_bst cmp tmp;
        let aux_left () : Lemma (forall_keys t (key_left cmp root) ==> forall_keys (rebalance_avl tmp) (key_left cmp root)) =
          if forall_keys t (key_left cmp root) then (
            assert (forall_keys tmp (key_left cmp root));
            rebalance_forall_left cmp tmp root
          )
        in
        aux_left ();
        let aux_right () : Lemma (forall_keys t (key_right cmp root) ==> forall_keys (rebalance_avl tmp) (key_right cmp root)) =
          if forall_keys t (key_right cmp root) then (
            assert (forall_keys tmp (key_right cmp root));
            rebalance_forall_right cmp tmp root
          )
        in
        aux_right ()
      )

/// delete_avl preserves is_bst
let delete_avl_preserves_bst (#k: Type) (#v: Type) (cmp: cmp k) (t: tree k v) (key: k)
  : Lemma (requires is_bst cmp t)
          (ensures is_bst cmp (delete_avl cmp t key))
  = match t with
    | Leaf -> ()
    | Node nd_key _ _ _ -> delete_avl_proof_aux cmp t key nd_key
#pop-options

/// rotate_left preserves forall_keys for any predicate
#push-options "--fuel 2 --ifuel 2"
let rotate_left_forall_keys (#k: Type) (#v: Type) (r: tree k v) (f: k -> bool)
  : Lemma (requires forall_keys r f /\ Some? (rotate_left r))
          (ensures forall_keys (Some?.v (rotate_left r)) f)
  = ()
#pop-options

/// rotate_right preserves forall_keys for any predicate
#push-options "--fuel 2 --ifuel 2"
let rotate_right_forall_keys (#k: Type) (#v: Type) (r: tree k v) (f: k -> bool)
  : Lemma (requires forall_keys r f /\ Some? (rotate_right r))
          (ensures forall_keys (Some?.v (rotate_right r)) f)
  = ()
#pop-options

/// rotate_left_right preserves forall_keys for any predicate
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let rotate_left_right_forall_keys (#k: Type) (#v: Type) (r: tree k v) (f: k -> bool)
  : Lemma (requires forall_keys r f /\ Some? (rotate_left_right r))
          (ensures forall_keys (Some?.v (rotate_left_right r)) f)
  = match r with
    | Node xk xv (Node zk zv t1 (Node yk yv t2 t3)) t4 ->
      // rotate_left_right: Node xk xv (Node zk zv t1 (Node yk yv t2 t3)) t4 -> Node yk yv (Node zk zv t1 t2) (Node xk xv t3 t4)
      normalize_term_spec (forall_keys r f);
      normalize_term_spec (forall_keys (Some?.v (rotate_left_right r)) f)
    | _ -> ()
#pop-options

/// rotate_right_left preserves forall_keys for any predicate
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let rotate_right_left_forall_keys (#k: Type) (#v: Type) (r: tree k v) (f: k -> bool)
  : Lemma (requires forall_keys r f /\ Some? (rotate_right_left r))
          (ensures forall_keys (Some?.v (rotate_right_left r)) f)
  = match r with
    | Node xk xv t1 (Node zk zv (Node yk yv t2 t3) t4) ->
      normalize_term_spec (forall_keys r f);
      normalize_term_spec (forall_keys (Some?.v (rotate_right_left r)) f)
    | _ -> ()
#pop-options

/// rebalance_avl preserves forall_keys
#push-options "--z3rlimit 50"
let rebalance_preserves_forall_keys (#k: Type) (#v: Type) (cmp: cmp k) (t: tree k v) (f: k -> bool)
  : Lemma (requires forall_keys t f)
          (ensures forall_keys (rebalance_avl t) f)
  = match t with
    | Leaf -> ()
    | Node nd_key nd_val left right ->
      if is_balanced t then ()
      else if height left - height right > 1 then (
        let Node lk lv lleft lright = left in
        if height lright > height lleft then
          rotate_left_right_forall_keys t f
        else
          rotate_right_forall_keys t f
      ) else if height right - height left > 1 then (
        let Node rk rv rleft rright = right in
        if height rleft > height rright then
          rotate_right_left_forall_keys t f
        else
          rotate_left_forall_keys t f
      ) else ()
#pop-options

/// rotate_left preserves no_dup_tree (requires is_bst)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let rotate_left_no_dup (#k: Type) (#v: Type) (cmp: cmp k) (r: tree k v)
  : Lemma (requires is_bst cmp r /\ no_dup_tree cmp r /\ Some? (rotate_left r))
          (ensures no_dup_tree cmp (Some?.v (rotate_left r)))
  = match r with
  | Node xk xv t1 (Node zk zv t2 t3) ->
      // Result: Node zk zv (Node xk xv t1 t2) t3
      // Unpack original no_dup_tree
      no_dup_tree_node cmp xk xv t1 (Node zk zv t2 t3);
      no_dup_tree_node cmp zk zv t2 t3;
      
      // From BST: t1 < x < z (transitivity)
      // All keys in t1 satisfy (k <= x) and (k >= x), but x < z, so k < z
      forall_keys_trans t1 (key_left cmp xk) (fun kk -> cmp zk kk <> 0);
      
      // Explicitly normalize both subtrees and result
      normalize_term_spec (no_dup_tree cmp (Node xk xv t1 t2));
      normalize_term_spec (no_dup_tree cmp (Node zk zv (Node xk xv t1 t2) t3))
#pop-options

/// rotate_right preserves no_dup_tree (requires is_bst)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let rotate_right_no_dup (#k: Type) (#v: Type) (cmp: cmp k) (r: tree k v)
  : Lemma (requires is_bst cmp r /\ no_dup_tree cmp r /\ Some? (rotate_right r))
          (ensures no_dup_tree cmp (Some?.v (rotate_right r)))
  = match r with
  | Node xk xv (Node zk zv t1 t2) t3 ->
      // Result: Node zk zv t1 (Node xk xv t2 t3)
      // Unpack original no_dup_tree
      no_dup_tree_node cmp xk xv (Node zk zv t1 t2) t3;
      no_dup_tree_node cmp zk zv t1 t2;
      
      // From BST: z < x < t3 (transitivity)
      // All keys in t3 satisfy (k >= x) and z < x, so z < k
      forall_keys_trans t3 (key_right cmp xk) (fun kk -> cmp zk kk <> 0);
      
      // Explicitly normalize both subtrees and result
      normalize_term_spec (no_dup_tree cmp (Node xk xv t2 t3));
      normalize_term_spec (no_dup_tree cmp (Node zk zv t1 (Node xk xv t2 t3)))
#pop-options

/// rotate_left_right preserves no_dup_tree (requires is_bst)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let rotate_left_right_no_dup (#k: Type) (#v: Type) (cmp: cmp k) (r: tree k v)
  : Lemma (requires is_bst cmp r /\ no_dup_tree cmp r /\ Some? (rotate_left_right r))
          (ensures no_dup_tree cmp (Some?.v (rotate_left_right r)))
  = match r with
  | Node xk xv (Node zk zv t1 (Node yk yv t2 t3)) t4 ->
      // Result: Node yk yv (Node zk zv t1 t2) (Node xk xv t3 t4)
      // Unpack original no_dup_tree
      no_dup_tree_node cmp xk xv (Node zk zv t1 (Node yk yv t2 t3)) t4;
      no_dup_tree_node cmp zk zv t1 (Node yk yv t2 t3);
      no_dup_tree_node cmp yk yv t2 t3;
      
      // From BST: t1 < z < y < x < t4 (chain of transitivity)
      forall_keys_trans t1 (key_left cmp zk) (fun kk -> cmp yk kk <> 0);
      forall_keys_trans t4 (key_right cmp xk) (fun kk -> cmp yk kk <> 0);
      
      // Show that y is distinct from z
      // forall_keys (Node yk yv t2 t3) (fun kk -> cmp zk kk <> 0) from original
      // This includes y itself, so cmp zk yk <> 0, hence cmp yk zk <> 0
      
      // Explicitly normalize and assert needed facts
      assert (forall_keys t1 (fun kk -> cmp yk kk <> 0));
      assert (forall_keys t2 (fun kk -> cmp yk kk <> 0));
      assert (forall_keys t3 (fun kk -> cmp yk kk <> 0));
      assert (forall_keys t4 (fun kk -> cmp yk kk <> 0));
      assert (forall_keys t1 (fun kk -> cmp zk kk <> 0));
      assert (forall_keys t2 (fun kk -> cmp zk kk <> 0));
      assert (forall_keys t3 (fun kk -> cmp xk kk <> 0));
      assert (forall_keys t4 (fun kk -> cmp xk kk <> 0));
      normalize_term_spec (no_dup_tree cmp (Node zk zv t1 t2));
      normalize_term_spec (no_dup_tree cmp (Node xk xv t3 t4));
      normalize_term_spec (no_dup_tree cmp (Node yk yv (Node zk zv t1 t2) (Node xk xv t3 t4)))
#pop-options

/// rotate_right_left preserves no_dup_tree (requires is_bst)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let rotate_right_left_no_dup (#k: Type) (#v: Type) (cmp: cmp k) (r: tree k v)
  : Lemma (requires is_bst cmp r /\ no_dup_tree cmp r /\ Some? (rotate_right_left r))
          (ensures no_dup_tree cmp (Some?.v (rotate_right_left r)))
  = match r with
  | Node xk xv t1 (Node zk zv (Node yk yv t2 t3) t4) ->
      // Result: Node yk yv (Node xk xv t1 t2) (Node zk zv t3 t4)
      // Unpack original no_dup_tree
      no_dup_tree_node cmp xk xv t1 (Node zk zv (Node yk yv t2 t3) t4);
      no_dup_tree_node cmp zk zv (Node yk yv t2 t3) t4;
      no_dup_tree_node cmp yk yv t2 t3;
      
      // From BST: t1 < x < y < z < t4 (chain of transitivity)
      forall_keys_trans t1 (key_left cmp xk) (fun kk -> cmp yk kk <> 0);
      forall_keys_trans t4 (key_right cmp zk) (fun kk -> cmp yk kk <> 0);
      
      // Explicitly assert needed facts
      assert (forall_keys t1 (fun kk -> cmp yk kk <> 0));
      assert (forall_keys t2 (fun kk -> cmp yk kk <> 0));
      assert (forall_keys t3 (fun kk -> cmp yk kk <> 0));
      assert (forall_keys t4 (fun kk -> cmp yk kk <> 0));
      assert (forall_keys t1 (fun kk -> cmp xk kk <> 0));
      assert (forall_keys t2 (fun kk -> cmp xk kk <> 0));
      assert (forall_keys t3 (fun kk -> cmp zk kk <> 0));
      assert (forall_keys t4 (fun kk -> cmp zk kk <> 0));
      normalize_term_spec (no_dup_tree cmp (Node xk xv t1 t2));
      normalize_term_spec (no_dup_tree cmp (Node zk zv t3 t4));
      normalize_term_spec (no_dup_tree cmp (Node yk yv (Node xk xv t1 t2) (Node zk zv t3 t4)))
#pop-options

/// rebalance_avl preserves no_dup_tree (requires is_bst)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let rebalance_preserves_no_dup (#k: Type) (#v: Type) (cmp: cmp k) (t: tree k v)
  : Lemma (requires is_bst cmp t /\ no_dup_tree cmp t)
          (ensures no_dup_tree cmp (rebalance_avl t))
  = match t with
    | Leaf -> ()
    | Node nd_key nd_val left right ->
      if is_balanced t then ()
      else if height left - height right > 1 then (
        let Node lk lv lleft lright = left in
        if height lright > height lleft then
          rotate_left_right_no_dup cmp t
        else
          rotate_right_no_dup cmp t
      ) else if height right - height left > 1 then (
        let Node rk rv rleft rright = right in
        if height rleft > height rright then
          rotate_right_left_no_dup cmp t
        else
          rotate_left_no_dup cmp t
      ) else ()
#pop-options

/// BST ordering implies distinctness: if m_key < data_key < all keys in r, then all keys in r are != m_key
#push-options "--fuel 2 --ifuel 2 --z3rlimit 250"
let rec bst_left_right_distinct (#k: Type) (#v: Type) (cmp: cmp k) (m_key data_key: k) (r: tree k v)
  : Lemma (requires is_bst cmp r /\ 
                    forall_keys r (key_right cmp data_key) /\
                    key_left cmp data_key m_key /\
                    cmp data_key m_key <> 0 /\
                    forall_keys r (fun kk -> cmp data_key kk <> 0))
          (ensures forall_keys r (fun kk -> cmp m_key kk <> 0))
          (decreases r)
  = match r with
    | Leaf -> ()
    | Node nd_key nd_val l r_right ->
      bst_left_right_distinct cmp m_key data_key l;
      bst_left_right_distinct cmp m_key data_key r_right
#pop-options

/// Extensionality for forall_keys: two functions that agree pointwise give the same result
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec forall_keys_ext (#k: Type) (#v: Type) (t: tree k v) (f g: k -> bool)
  : Lemma (requires forall_keys t f /\ (forall (x:k). f x == g x))
          (ensures forall_keys t g)
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node dk dv l r -> forall_keys_ext l f g; forall_keys_ext r f g

/// Assemble no_dup_tree from components, bridging lambda representations via forall_keys_ext
let no_dup_tree_assemble (#k: Type) (#v: Type) (cmp: cmp k) (dk: k) (dv: v) (l r: tree k v) (f: k -> bool)
  : Lemma (requires forall_keys l f /\ forall_keys r f /\
                    no_dup_tree cmp l /\ no_dup_tree cmp r /\
                    (forall (x: k). f x == (cmp dk x <> 0)))
          (ensures no_dup_tree cmp (Node dk dv l r))
  = let nd_f : (k -> bool) = fun kk -> cmp dk kk <> 0 in
    forall_keys_ext l f nd_f;
    forall_keys_ext r f nd_f;
    normalize_term_spec (no_dup_tree cmp (Node dk dv l r))
#pop-options

/// Helper: forall_keys is preserved through delete_avl
#push-options "--fuel 3 --ifuel 2 --z3rlimit 100"
let rebalance_forall_keys_f (#k: Type) (#v: Type) (t: tree k v) (f: k -> bool)
  : Lemma (requires forall_keys t f)
          (ensures forall_keys (rebalance_avl t) f) = ()

let rec forall_keys_delete_avl (#k: Type) (#v: Type) (cmp: cmp k) (t: tree k v) (key: k) (f: k -> bool)
  : Lemma (requires forall_keys t f)
          (ensures forall_keys (delete_avl cmp t key) f)
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node dk dv l r ->
      if cmp dk key = 0 then (
        match l with
        | Leaf -> ()
        | _ -> forall_keys_tree_max l f;
               forall_keys_delete_avl cmp l (fst (tree_max l)) f;
               rebalance_forall_keys_f (Node (fst (tree_max l)) (snd (tree_max l)) (delete_avl cmp l (fst (tree_max l))) r) f
      ) else if cmp dk key < 0 then (
        forall_keys_delete_avl cmp r key f;
        rebalance_forall_keys_f (Node dk dv l (delete_avl cmp r key)) f
      ) else (
        forall_keys_delete_avl cmp l key f;
        rebalance_forall_keys_f (Node dk dv (delete_avl cmp l key) r) f
      )
#pop-options

/// Transitivity helper for cmp neq
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let neq_transitive (#k: Type) (cmp: cmp k) (m_key d_key k_key: k)
  : Lemma (requires cmp d_key k_key >= 0 /\ cmp d_key k_key <> 0 /\ cmp m_key d_key > 0)
          (ensures cmp m_key k_key <> 0) = ()
#pop-options

/// forall_keys neq via transitivity through BST ordering
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let rec forall_keys_neq_via_trans (#k: Type) (#v: Type) (cmp: cmp k) (t: tree k v) (d_key m_key: k)
  : Lemma (requires forall_keys t (key_left cmp d_key) /\
                    forall_keys t (fun kk -> cmp d_key kk <> 0) /\
                    cmp m_key d_key > 0)
          (ensures forall_keys t (fun kk -> cmp m_key kk <> 0))
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node xk xv l r ->
      neq_transitive cmp m_key d_key xk;
      forall_keys_neq_via_trans cmp l d_key m_key;
      forall_keys_neq_via_trans cmp r d_key m_key
#pop-options

/// BST+no_dup (Node dk dv l r) with Node? r => forall_keys l (fun k -> cmp (tree_max r) k <> 0)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let left_max_right_distinct (#k: Type) (#v: Type) (cmp: cmp k) (dk: k) (dv: v) (l r: tree k v)
  : Lemma (requires is_bst cmp (Node dk dv l r) /\ no_dup_tree cmp (Node dk dv l r) /\ Node? r)
          (ensures (let m = tree_max r in
                    forall_keys l (fun kk -> cmp (fst m) kk <> 0)))
  = let m = tree_max r in
    no_dup_tree_node cmp dk dv l r;
    forall_keys_tree_max r (key_right cmp dk);
    forall_keys_tree_max r (fun kk -> cmp dk kk <> 0);
    forall_keys_neq_via_trans cmp l dk (fst m);
    let f_local : (k -> bool) = fun kk -> cmp (fst m) kk <> 0 in
    let f_ensures : (k -> bool) = fun kk -> cmp (fst (tree_max r)) kk <> 0 in
    forall_keys_ext l f_local f_ensures
#pop-options

/// After deleting tree_max, all remaining keys are distinct from it
/// Uses forall_keys_ext to bridge lambda representations across recursive calls
#push-options "--fuel 3 --ifuel 2 --z3rlimit 250"
let rec delete_max_neq (#k: Type) (#v: Type) (cmp: cmp k) (t: tree k v) (m_key: k)
  : Lemma (requires Node? t /\ is_bst cmp t /\ no_dup_tree cmp t /\ m_key == fst (tree_max t))
          (ensures forall_keys (delete_avl cmp t m_key) (fun kk -> cmp m_key kk <> 0))
          (decreases t)
  = let Node dk dv l r = t in
    let f : (k -> bool) = fun kk -> cmp m_key kk <> 0 in
    no_dup_tree_node cmp dk dv l r;
    if Leaf? r then (
      let f_d : (k -> bool) = fun kk -> cmp dk kk <> 0 in
      match l with
      | Leaf -> ()
      | _ ->
        forall_keys_ext l f_d f;
        forall_keys_delete_avl cmp l (fst (tree_max l)) f;
        forall_keys_tree_max l f;
        rebalance_forall_keys_f (Node (fst (tree_max l)) (snd (tree_max l)) (delete_avl cmp l (fst (tree_max l))) Leaf) f
    ) else (
      forall_keys_tree_max r (fun kk -> cmp dk kk <> 0);
      forall_keys_tree_max r (key_right cmp dk);
      delete_max_neq cmp r m_key;
      forall_keys_neq_via_trans cmp l dk m_key;
      let g : (k -> bool) = fun kk -> cmp m_key kk <> 0 in
      forall_keys_ext l g f;
      normalize_term_spec (forall_keys (Node dk dv l (delete_avl cmp r m_key)) f);
      rebalance_forall_keys_f (Node dk dv l (delete_avl cmp r m_key)) f
    )

let delete_max_keys_distinct (#k: Type) (#v: Type) (cmp: cmp k) (t: tree k v)
  : Lemma (requires is_bst cmp t /\ no_dup_tree cmp t /\ Node? t)
          (ensures (let m = tree_max t in
                    forall_keys (delete_avl cmp t (fst m)) (fun kk -> cmp (fst m) kk <> 0)))
  = delete_max_neq cmp t (fst (tree_max t))
#pop-options

/// delete_avl preserves no_dup_tree (with forall_keys tracking for the induction)
#push-options "--z3rlimit 1000 --fuel 2 --ifuel 2"
let rec delete_avl_no_dup_aux (#k: Type) (#v: Type) (cmp: cmp k) (t: tree k v) (key: k) (root: k)
  : Lemma (requires is_bst cmp t /\ no_dup_tree cmp t)
          (ensures (
            let res = delete_avl cmp t key in
            no_dup_tree cmp res /\
            (forall_keys t (fun kk -> cmp root kk <> 0) ==> forall_keys res (fun kk -> cmp root kk <> 0))
          ))
          (decreases t)
  = match t with
    | Leaf -> ()
    | Node nd_key nd_val left right ->
      let delta = cmp nd_key key in
      no_dup_tree_node cmp nd_key nd_val left right;
      if delta = 0 then (
        match left, right with
        | Leaf, Leaf -> ()
        | Node _ _ _ _, Leaf -> ()
        | Leaf, Node _ _ _ _ -> ()
        | _, _ ->
          let m = tree_max left in
          delete_avl_no_dup_aux cmp left (fst m) nd_key;
          delete_avl_no_dup_aux cmp left (fst m) (fst m);
          delete_avl_no_dup_aux cmp left (fst m) root;
          let new_left = delete_avl cmp left (fst m) in
          let tmp = Node (fst m) (snd m) new_left right in
          
          delete_avl_proof_aux cmp left (fst m) nd_key;
          delete_avl_proof_aux cmp left (fst m) (fst m);
          tree_max_is_maximal cmp left;
          forall_keys_tree_max left (key_left cmp nd_key);
          forall_keys_trans right (key_right cmp nd_key) (key_right cmp (fst m));
          forall_keys_tree_max left (fun kk -> cmp nd_key kk <> 0);
          
          // no_dup for tmp: use forall_keys_ext to bridge lambda representations
          delete_max_keys_distinct cmp left;
          let f_neq : (k -> bool) = fun kk -> cmp (fst m) kk <> 0 in
          let f_src : (k -> bool) = fun kk -> cmp (fst (tree_max left)) kk <> 0 in
          forall_keys_ext new_left f_src f_neq;
          bst_left_right_distinct cmp (fst m) nd_key right;
          let f_bst : (k -> bool) = fun kk -> cmp (fst m) kk <> 0 in
          forall_keys_ext right f_bst f_neq;
          no_dup_tree_assemble cmp (fst m) (snd m) new_left right f_neq;
          
          normalize_term_spec (is_bst cmp tmp);
          rebalance_bst cmp tmp;
          rebalance_preserves_no_dup cmp tmp;
          if forall_keys (Node nd_key nd_val left right) (fun kk -> cmp root kk <> 0) then (
            forall_keys_tree_max left (fun kk -> cmp root kk <> 0);
            rebalance_preserves_forall_keys cmp tmp (fun kk -> cmp root kk <> 0)
          )
      ) else if delta < 0 then (
        delete_avl_no_dup_aux cmp right key nd_key;
        delete_avl_no_dup_aux cmp right key root;
        let new_right = delete_avl cmp right key in
        let tmp = Node nd_key nd_val left new_right in
        delete_avl_proof_aux cmp right key nd_key;
        let f_neq2 : (k -> bool) = fun kk -> cmp nd_key kk <> 0 in
        forall_keys_delete_avl cmp right key f_neq2;
        no_dup_tree_assemble cmp nd_key nd_val left new_right f_neq2;
        normalize_term_spec (is_bst cmp tmp);
        rebalance_bst cmp tmp;
        rebalance_preserves_no_dup cmp tmp;
        if forall_keys (Node nd_key nd_val left right) (fun kk -> cmp root kk <> 0) then
          rebalance_preserves_forall_keys cmp tmp (fun kk -> cmp root kk <> 0)
      ) else (
        delete_avl_no_dup_aux cmp left key nd_key;
        delete_avl_no_dup_aux cmp left key root;
        let new_left = delete_avl cmp left key in
        let tmp = Node nd_key nd_val new_left right in
        delete_avl_proof_aux cmp left key nd_key;
        let f_neq3 : (k -> bool) = fun kk -> cmp nd_key kk <> 0 in
        forall_keys_delete_avl cmp left key f_neq3;
        no_dup_tree_assemble cmp nd_key nd_val new_left right f_neq3;
        normalize_term_spec (is_bst cmp tmp);
        rebalance_bst cmp tmp;
        rebalance_preserves_no_dup cmp tmp;
        if forall_keys (Node nd_key nd_val left right) (fun kk -> cmp root kk <> 0) then
          rebalance_preserves_forall_keys cmp tmp (fun kk -> cmp root kk <> 0)
      )

/// delete_avl preserves no_dup_tree
let delete_avl_preserves_no_dup_tree (#k: Type) (#v: Type) (cmp: cmp k) (t: tree k v) (key: k)
  : Lemma (requires is_bst cmp t /\ no_dup_tree cmp t)
          (ensures no_dup_tree cmp (delete_avl cmp t key))
  = match t with
    | Leaf -> ()
    | Node nd_key _ _ _ -> delete_avl_no_dup_aux cmp t key nd_key

/// Helper: insert_avl preserves forall_keys
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let rec insert_avl_preserves_forall_keys
  (#k: Type) (#v: Type)
  (cmp: cmp k)
  (t: tree k v)
  (key: k)
  (val_: v)
  (cond: k -> bool)
    : Lemma
      (requires forall_keys t cond /\ cond key)
      (ensures forall_keys (insert_avl cmp t key val_) cond)
      (decreases t)
  = match t with
    | Leaf -> ()
    | Node nd_key nd_val left right ->
      let delta = cmp nd_key key in
      if delta >= 0 then (
        insert_avl_preserves_forall_keys cmp left key val_ cond;
        rebalance_preserves_forall_keys cmp (Node nd_key nd_val (insert_avl cmp left key val_) right) cond
      ) else (
        insert_avl_preserves_forall_keys cmp right key val_ cond;
        rebalance_preserves_forall_keys cmp (Node nd_key nd_val left (insert_avl cmp right key val_)) cond
      )
#pop-options

/// Helper: insert_avl preserves is_bst
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let rec insert_avl_preserves_bst
  (#k: Type) (#v: Type)
  (cmp: cmp k)
  (t: tree k v)
  (key: k)
  (val_: v)
    : Lemma
      (requires is_bst cmp t)
      (ensures is_bst cmp (insert_avl cmp t key val_))
      (decreases t)
  = match t with
    | Leaf -> ()
    | Node nd_key nd_val left right ->
      let delta = cmp nd_key key in
      if delta >= 0 then (
        insert_avl_preserves_forall_keys cmp left key val_ (key_left cmp nd_key);
        insert_avl_preserves_bst cmp left key val_;
        normalize_term_spec (is_bst cmp (Node nd_key nd_val (insert_avl cmp left key val_) right));
        rebalance_bst cmp (Node nd_key nd_val (insert_avl cmp left key val_) right)
      ) else (
        insert_avl_preserves_forall_keys cmp right key val_ (key_right cmp nd_key);
        insert_avl_preserves_bst cmp right key val_;
        normalize_term_spec (is_bst cmp (Node nd_key nd_val left (insert_avl cmp right key val_)));
        rebalance_bst cmp (Node nd_key nd_val left (insert_avl cmp right key val_))
      )
#pop-options

/// insert_avl preserves no_dup_tree
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let rec insert_avl_preserves_no_dup_tree
  (#k: Type) (#v: Type)
  (cmp: cmp k)
  (t: tree k v)
  (key: k)
  (val_: v)
    : Lemma
      (requires is_bst cmp t /\ no_dup_tree cmp t /\
                forall_keys t (fun kk -> cmp key kk <> 0))
      (ensures no_dup_tree cmp (insert_avl cmp t key val_))
      (decreases t)
  = match t with
    | Leaf -> ()
    | Node nd_key nd_val left right ->
      let delta = cmp nd_key key in
      let f : (k -> bool) = fun kk -> cmp nd_key kk <> 0 in
      no_dup_tree_node cmp nd_key nd_val left right;
      forall_keys_ext left (fun kk -> cmp nd_key kk <> 0) f;
      forall_keys_ext right (fun kk -> cmp nd_key kk <> 0) f;
      
      if delta >= 0 then (
        insert_avl_preserves_no_dup_tree cmp left key val_;
        insert_avl_preserves_bst cmp left key val_;
        insert_avl_preserves_forall_keys cmp left key val_ f;
        insert_avl_preserves_forall_keys cmp left key val_ (key_left cmp nd_key);
        let tmp = Node nd_key nd_val (insert_avl cmp left key val_) right in
        normalize_term_spec (is_bst cmp tmp);
        no_dup_tree_assemble cmp nd_key nd_val (insert_avl cmp left key val_) right f;
        rebalance_bst cmp tmp;
        rebalance_preserves_no_dup cmp tmp
      ) else (
        insert_avl_preserves_no_dup_tree cmp right key val_;
        insert_avl_preserves_bst cmp right key val_;
        insert_avl_preserves_forall_keys cmp right key val_ f;
        insert_avl_preserves_forall_keys cmp right key val_ (key_right cmp nd_key);
        let tmp = Node nd_key nd_val left (insert_avl cmp right key val_) in
        normalize_term_spec (is_bst cmp tmp);
        no_dup_tree_assemble cmp nd_key nd_val left (insert_avl cmp right key val_) f;
        rebalance_bst cmp tmp;
        rebalance_preserves_no_dup cmp tmp
      )
#pop-options
#pop-options

(** Strictly sorted sequences and BST no_dup_tree bridge *)

/// Strictly sorted: each consecutive pair has compare < 0 (not <=)
let rec sorted_strict (#k: Type) (#v: Type) (compare: cmp k) (s: Seq.seq (k & v))
  : Tot bool (decreases Seq.length s) =
  if Seq.length s <= 1 then true
  else compare (fst (Seq.head s)) (fst (Seq.index s 1)) < 0 && sorted_strict compare (Seq.tail s)

/// sorted_strict implies sorted
let rec sorted_strict_implies_sorted (#k: Type) (#v: Type) (compare: cmp k) (s: Seq.seq (k & v))
  : Lemma (requires sorted_strict compare s)
          (ensures sorted compare s)
          (decreases Seq.length s) =
  if Seq.length s <= 1 then ()
  else sorted_strict_implies_sorted compare (Seq.tail s)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

/// In a strictly sorted sequence, all pairs are distinct under cmp
let rec sorted_strict_forall_neq (#k: Type) (#v: Type) (compare: cmp k) (s: Seq.seq (k & v)) (i j: nat)
  : Lemma (requires sorted_strict compare s /\ i < j /\ j < Seq.length s)
          (ensures compare (fst (Seq.index s i)) (fst (Seq.index s j)) < 0)
          (decreases Seq.length s) =
  if i = 0 then (
    if j = 1 then ()
    else sorted_strict_forall_neq compare (Seq.tail s) 0 (j - 1)
  ) else
    sorted_strict_forall_neq compare (Seq.tail s) (i - 1) (j - 1)

#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"

/// Helper: In a strictly sorted sequence, no element equals a given element at a different position
let rec sorted_strict_neq_all (#k: Type) (#v: Type) (compare: cmp k) (s: Seq.seq (k & v)) (d: (k & v)) (d_pos: nat)
  : Lemma
    (requires sorted_strict compare s /\ d_pos < Seq.length s /\ Seq.index s d_pos == d)
    (ensures (forall (i:nat{i < Seq.length s /\ i <> d_pos}). compare (fst d) (fst (Seq.index s i)) <> 0))
    (decreases Seq.length s) =
  let aux (i:nat{i < Seq.length s /\ i <> d_pos})
    : Lemma (compare (fst d) (fst (Seq.index s i)) <> 0) =
    if i < d_pos then sorted_strict_forall_neq compare s i d_pos
    else sorted_strict_forall_neq compare s d_pos i
  in
  Classical.forall_intro aux

/// sorted_strict on tail
let sorted_strict_tail (#k: Type) (#v: Type) (compare: cmp k) (s: Seq.seq (k & v))
  : Lemma (requires sorted_strict compare s /\ Seq.length s > 0)
          (ensures sorted_strict compare (Seq.tail s)) = ()

/// sorted_strict on the append components
let rec sorted_strict_append_left (#k: Type) (#v: Type) (compare: cmp k) (s1 s2: Seq.seq (k & v))
  : Lemma (requires sorted_strict compare (Seq.append s1 s2))
          (ensures sorted_strict compare s1)
          (decreases Seq.length s1) =
  if Seq.length s1 <= 1 then ()
  else (
    Seq.lemma_head_append s1 s2;
    Seq.lemma_tail_append s1 s2;
    assert (Seq.index (Seq.append s1 s2) 0 == Seq.index s1 0);
    assert (Seq.index (Seq.append s1 s2) 1 == Seq.index s1 1);
    sorted_strict_append_left compare (Seq.tail s1) s2
  )

let rec sorted_strict_append_right (#k: Type) (#v: Type) (compare: cmp k) (s1 s2: Seq.seq (k & v))
  : Lemma (requires sorted_strict compare (Seq.append s1 s2))
          (ensures sorted_strict compare s2)
          (decreases Seq.length s1) =
  if Seq.length s1 = 0 then
    assert (Seq.equal (Seq.append s1 s2) s2)
  else (
    Seq.lemma_tail_append s1 s2;
    sorted_strict_append_right compare (Seq.tail s1) s2
  )

/// seq_forall on append components (reverse of seq_forall_append)
let rec seq_forall_append_inv (#k: Type) (#v: Type) (f: k -> bool) (s1 s2: Seq.seq (k & v))
  : Lemma (requires seq_forall f (Seq.append s1 s2))
          (ensures seq_forall f s1 /\ seq_forall f s2)
          (decreases Seq.length s1) =
  if Seq.length s1 = 0 then
    assert (Seq.equal (Seq.append s1 s2) s2)
  else (
    Seq.lemma_head_append s1 s2;
    Seq.lemma_tail_append s1 s2;
    seq_forall_append_inv f (Seq.tail s1) s2
  )

/// Reverse bridge: seq_forall on inorder implies forall_keys on tree
let rec inorder_forall_keys (#k: Type) (#v: Type) (t: tree k v) (cond: k -> bool)
  : Lemma (requires seq_forall cond (inorder t))
          (ensures forall_keys t cond)
          (decreases t) =
  match t with
  | Leaf -> ()
  | Node dk dv l r ->
    // inorder t == append (inorder l) (cons d (inorder r))
    seq_forall_append_inv cond (inorder l) (Seq.cons (dk, dv) (inorder r));
    // Now: seq_forall cond (inorder l) /\ seq_forall cond (cons d (inorder r))
    // From cons: head is d so cond d, tail is inorder r
    let dr = Seq.cons (dk, dv) (inorder r) in
    assert (Seq.head dr == (dk, dv));
    assert (Seq.equal (Seq.tail dr) (inorder r));
    inorder_forall_keys l cond;
    inorder_forall_keys r cond

#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"

/// All elements left of d in a sorted_strict sequence have compare d k <> 0.
/// Since sorted_strict_forall_neq gives compare k d < 0 for k before d,
/// the cmp axiom gives compare d k > 0, hence <> 0.
let rec sorted_strict_left_neq (#k: Type) (#v: Type) (compare: cmp k) (s1: Seq.seq (k & v)) (d: (k & v)) (s2: Seq.seq (k & v))
  : Lemma
    (requires sorted_strict compare (Seq.append s1 (Seq.cons d s2)))
    (ensures seq_forall (fun x -> compare (fst d) x <> 0) s1)
    (decreases Seq.length s1)
  = if Seq.length s1 = 0 then ()
    else begin
      let h = Seq.head s1 in
      let t = Seq.tail s1 in
      let ds = Seq.cons d s2 in
      let full = Seq.append s1 ds in
      sorted_strict_forall_neq compare full 0 (Seq.length s1);
      Seq.lemma_tail_append s1 ds;
      sorted_strict_left_neq compare t d s2;
      seq_forall_cons (fun x -> compare (fst d) x <> 0) (fst h, snd h) t
    end

/// All elements after d in a sorted_strict (d :: s) have compare d k <> 0.
/// Key: from sorted_strict (d :: h :: t), derive sorted_strict (d :: t) via
/// sorted_strict_forall_neq to get compare d (head t) < 0.
let rec sorted_strict_right_neq (#k: Type) (#v: Type) (compare: cmp k) (d: (k & v)) (s: Seq.seq (k & v))
  : Lemma
    (requires sorted_strict compare (Seq.cons d s))
    (ensures seq_forall (fun x -> compare (fst d) x <> 0) s)
    (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      let h = Seq.head s in
      let t = Seq.tail s in
      let ds = Seq.cons d s in
      // Establish tail(cons d s) == s
      Seq.lemma_tail_append (Seq.create 1 d) s;
      assert (Seq.equal (Seq.tail ds) s);
      if Seq.length t = 0 then ()
      else begin
        sorted_strict_tail compare ds;
        sorted_strict_tail compare s;
        sorted_strict_forall_neq compare ds 0 2;
        let dt = Seq.cons d t in
        Seq.lemma_head_append (Seq.create 1 d) t;
        Seq.lemma_tail_append (Seq.create 1 d) t;
        assert (Seq.head dt == d);
        assert (Seq.equal (Seq.tail dt) t);
        assert (Seq.index dt 1 == Seq.head t);
        sorted_strict_right_neq compare d t
      end;
      seq_forall_cons (fun x -> compare (fst d) x <> 0) (fst h, snd h) t
    end

/// Extensionality for seq_forall: two predicates that agree on keys give the same result
let rec seq_forall_ext (#k: Type) (#v: Type) (f g: k -> bool) (s: Seq.seq (k & v))
  : Lemma (requires seq_forall f s /\ (forall (x:k). f x == g x))
          (ensures seq_forall g s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else seq_forall_ext f g (Seq.tail s)

/// BST with strictly sorted inorder implies no_dup_tree
let rec bst_strict_sorted_no_dup (#k: Type) (#v: Type) (compare: cmp k) (t: tree k v)
  : Lemma
    (requires is_bst compare t /\ sorted_strict compare (inorder t))
    (ensures no_dup_tree compare t)
    (decreases t) =
  match t with
  | Leaf -> ()
  | Node dk dv l r ->
    let io_l = inorder l in
    let io_r = inorder r in
    let ds = Seq.cons (dk, dv) io_r in
    // sorted_strict on sub-sequences
    sorted_strict_append_left compare io_l ds;
    sorted_strict_append_right compare io_l ds;
    sorted_strict_tail compare ds;
    assert (Seq.equal (Seq.tail ds) io_r);
    bst_strict_sorted_no_dup compare l;
    bst_strict_sorted_no_dup compare r;
    // Build forall_keys l/r (fun x -> compare dk x <> 0)
    let f : (k -> bool) = fun x -> compare dk x <> 0 in
    let g : (k -> bool) = fun x -> compare (fst (dk, dv)) x <> 0 in
    sorted_strict_left_neq compare io_l (dk, dv) io_r;
    // sorted_strict_left_neq gives seq_forall g io_l, but we need seq_forall f io_l
    // Since fst (dk, dv) = dk, g and f are extensionally equal
    assert (forall (x:k). g x == f x);
    seq_forall_ext g f io_l;
    inorder_forall_keys l f;
    sorted_strict_right_neq compare (dk, dv) io_r;
    seq_forall_ext g f io_r;
    inorder_forall_keys r f;
    no_dup_tree_assemble compare dk dv l r f

#pop-options
