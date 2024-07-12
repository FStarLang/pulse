module Pulse.Lib.Deque

open Pulse.Lib.Pervasives
open Pulse.Lib.Stick.Util
open FStar.List.Tot
open Pulse.Lib.Trade
module T = FStar.Tactics
module I = Pulse.Lib.Stick.Util
module FA = Pulse.Lib.Forall.Util


noeq
type node (t:Type0) = {
    value : t;
    dprev : option (node_ptr t);
    dnext : option (node_ptr t);
}

and node_ptr (t:Type0) = ref (node t)

noeq
type deque (t:Type0) = {
  head: option (node_ptr t);
  tail: option (node_ptr t);
}

let rec is_deque_suffix
  (#t:Type0)
  (p:node_ptr t)
  (l:list t {Cons? l})
  (prev:option (node_ptr t))
  (tail:node_ptr t)
  (last:option (node_ptr t))
  : Tot slprop (decreases l)
  = match l with
    | [n] ->
      exists* (v:node t).
        pts_to p v **
        pure (v.value == n /\
          v.dnext == last /\
          v.dprev == prev /\
          p == tail)
    | n::ns ->
      exists* (v:node t) (np:node_ptr t).
        pts_to p v **
        is_deque_suffix np ns (Some p) tail last **
        pure (v.value == n /\
          v.dprev == prev /\
          v.dnext == (Some np))
          
```pulse
ghost
fn fold_is_deque_suffix_cons
  (#t:Type0)
  (p:node_ptr t)
  (n:t)
  (ns:list t {Cons? ns})
  (prev:option (node_ptr t))
  (tail:node_ptr t)
  (last:option (node_ptr t))
  (v : node t) (np : node_ptr t)
  requires
    pts_to p v **
    is_deque_suffix np ns (Some p) tail last **
    pure (v.value == n /\
      v.dprev == prev /\
      v.dnext == (Some np))
  ensures
    is_deque_suffix p (n::ns) prev tail last
{
  let n' = Cons?.hd ns;
  let ns' = Cons?.tl ns;
  rewrite each ns as (n' :: ns');
  fold (is_deque_suffix p (n::n'::ns') prev tail last);
}
```


let is_deque #t (x:deque t) (l:list t)
  : Tot slprop (decreases l)
  = match l with
    | [] ->
        pure (x == { head = None; tail = None })
    | ns ->
        exists* (hp tp:node_ptr t).
          is_deque_suffix hp ns None tp None **
          pure (x.head == (Some hp) /\ x.tail == (Some tp))

```pulse
fn mk_empty (#t:Type) (_:unit)
  requires emp
  returns  p : deque t
  ensures  is_deque p []
{
  let p = { head = None; tail = None } <: deque t;
  fold (is_deque p []);
  p
}
```

```pulse
fn push_front_empty (#t:Type) (l : deque t) (x : t)
  requires is_deque l []
  returns  l' : deque t
  ensures  is_deque l' [x]
{
  unfold (is_deque l []);

  let vnode = {
    value = x;
    dprev = None;
    dnext = None;
  };
  let node = alloc vnode;

  fold (is_deque_suffix node [x] None node);

  let l' = {
    head = Some node;
    tail = Some node;
  };

  fold (is_deque l' [x]);
  l'
}
```

```pulse
ghost
fn is_deque_null_head_ptr
  (#t:Type)
  (l : deque t)
  (#xs : erased (list t))
  requires
    is_deque l xs **
    pure (l.head == None)
  ensures
    is_deque l xs **
    pure (l.tail == None /\ xs == [])
{
  let xss = reveal xs;
  match xss {
    Nil -> {
      (* Need to unfold + fold to bring pure into scope. *)
      unfold (is_deque l []);
      fold (is_deque l []);
      ()
    }
    Cons hd tl -> {
      unfold (is_deque l (hd :: tl));
      unreachable();
    }
  }
}
```

```pulse
ghost
fn is_deque_some_head_ptr
  (#t:Type)
  (l : deque t)
  (#xs : erased (list t))
  requires
    is_deque l xs **
    pure (Some? l.head)
  ensures
    is_deque l xs **
    pure (Some? l.tail /\ Cons? xs)
{
  let xss = reveal xs;
  match xss {
    Nil -> {
      (* Need to unfold + fold to bring pure into scope. *)
      unfold (is_deque l []);
      unreachable();
    }
    Cons hd tl -> {
      unfold (is_deque l (hd :: tl));
      fold (is_deque l (hd :: tl));
    }
  }
}
```

```pulse
ghost
fn some_head_then_some_tail
  (#t:Type)
  (l : deque t)
  (#xs : erased (list t))
  requires is_deque l xs ** pure (Some? l.head)
  ensures  is_deque l xs ** pure (Some? l.tail)
{
  let xss = reveal xs;
  match xss {
    Nil -> {
      unfold (is_deque l []);
      fold (is_deque l []);
      ();
    }
    Cons hd tl -> {
      unfold (is_deque l (hd :: tl));
      fold (is_deque l (hd :: tl));
      ();
    }
  }
}
```

(* This is really the contrarreciprocal of the `is_deque_null_head_ptr` lemma above. *)
```pulse
ghost
fn is_deque_cons_not_none
  (#t:Type)
  (l : deque t)
  (#xs : erased (list t))
  requires
    is_deque l xs **
    pure (Cons? xs)
  ensures
    is_deque l xs **
    pure (Some? l.head /\ Some? l.tail)
{
  if (Some? l.head) {
    some_head_then_some_tail l;
  } else {
    is_deque_null_head_ptr l;
  }
}
```

(* This function VERY brittle. See #112. *)
```pulse
ghost
fn unfold_is_deque_cons (#t:Type) (l : deque t) (#xs : (list t){Cons? xs})
  requires is_deque l xs ** pure (Cons? xs)
  returns  hptp : erased (node_ptr t & node_ptr t)
  ensures  is_deque_suffix (fst hptp) xs None (snd hptp) None **
           pure (l.head == Some (fst hptp) /\ l.tail == Some (snd hptp))
{
  match xs {
    Nil -> {
      unreachable();
    }
    Cons hd tl -> {
      rewrite each xs as Cons hd tl;
      unfold is_deque;
      with hp tp. assert (is_deque_suffix hp (hd::tl) None tp None);
      hide (hp, tp)
    }
  }
}
```

(* In support of the definition below. It is hard to work with
(triggers #112) without this. *)
let is_deque_suffix_factored_next
  (#t:Type0)
  (p:node_ptr t) (l:list t{Cons? l})
  (tail : node_ptr t)
  (last : option (node_ptr t))
  (v_dnext : option (node_ptr t))
  : Tot slprop
= match l with
  | [n] -> pure (v_dnext == last /\ p == tail)
  | n::ns ->
    exists* (np:node_ptr t).
      is_deque_suffix np ns (Some p) tail last **
      pure (v_dnext == Some np)

(* is_deque_suffix requires us to match on the (erased) list l to
even get permission to the pointer, which is not doable in normal code. But,
ghostly, we can turn it into this, which gives us unconditional permission
on the head. *)
let is_deque_suffix_factored
   (#t:Type0)
   (x:node_ptr t) (l:list t{Cons? l})
   (prev : option (node_ptr t))
   (tail : node_ptr t)
   (last : option (node_ptr t))
: Tot slprop
  = exists* (v:node t).
      pts_to x v **
      pure (
        v.value == List.Tot.hd l /\
        v.dprev == prev
      ) **
      is_deque_suffix_factored_next x l tail last v.dnext

```pulse
ghost
fn factor_is_deque_suffix
  (#t:Type0)
  (p:node_ptr t) (l:list t{Cons? l}) (prev:option (node_ptr t)) (tail:node_ptr t)
  (#last : option (node_ptr t))
  requires
    is_deque_suffix p l prev tail last
  ensures
    is_deque_suffix_factored p l prev tail last
{
  let hd : t = List.Tot.hd l;
  let tl : list t = List.Tot.tl l;
  match tl {
    Nil -> {
      assert (pure (l == [hd]));
      unfold (is_deque_suffix p [hd] prev tail);
      with v. assert (pts_to p v);
      fold (is_deque_suffix_factored_next p [hd] tail last v.dnext);
      fold (is_deque_suffix_factored p [hd] prev tail last);
    }
    Cons y ys -> {
      assert (pure (l == hd::y::ys));
      unfold (is_deque_suffix p (hd::y::ys) prev tail);
      with v. assert (pts_to p v);
      fold (is_deque_suffix_factored_next p (hd::y::ys) tail last v.dnext);
      fold (is_deque_suffix_factored p (hd::y::ys) prev tail last);
    }
  }
}
```

```pulse
ghost
fn unfactor_is_deque_suffix
  (#t:Type)
  (p:node_ptr t) (l:list t{Cons? l})
  (prev:option (node_ptr t)) (tail:node_ptr t)
  (#last : option (node_ptr t))
   requires
     is_deque_suffix_factored p l prev tail last
   ensures
     is_deque_suffix p l prev tail last
{
  unfold (is_deque_suffix_factored p l prev tail last);
  with v. assert (pts_to p v);
  unfold (is_deque_suffix_factored_next p l tail last v.dnext);
  let hd : t = List.Tot.hd l;
  let tl : list t = List.Tot.tl l;
  match tl {
    Nil -> {
      rewrite each l as [hd];
      rewrite each tl as [];
      fold (is_deque_suffix p [hd] prev tail last);
    }
    Cons y ys -> {
      rewrite each l as (hd::y::ys);
      rewrite each tl as (y::ys);
      fold (is_deque_suffix p (hd::y::ys) prev tail last);
    }
  }
}
```

```pulse
fn set_back_pointer
  (#t:Type) (x : node_ptr t)
  (prev' : option (node_ptr t))
  (#l : erased (list t){Cons? l})
  (#prev : erased (option (node_ptr t)))
  (#tail : erased (node_ptr t))
  (#last : erased (option (node_ptr t)))
  requires is_deque_suffix x l prev  tail last
  ensures  is_deque_suffix x l prev' tail last
{
  factor_is_deque_suffix x l prev tail;
  unfold (is_deque_suffix_factored x l prev tail);
  with v. assert (pts_to x v);
  let cv = !x;
  let cv' = { cv with dprev = prev' };
  x := cv';

  rewrite is_deque_suffix_factored_next x l tail last cv.dnext
       as is_deque_suffix_factored_next x l tail last cv'.dnext;

  fold (is_deque_suffix_factored x l prev' tail);
  unfactor_is_deque_suffix x l prev' tail;
}
```

```pulse
fn push_front_cons (#t:Type) (l : deque t) (x : t) (#xs : erased (list t))
  requires is_deque l xs ** pure (Cons? xs)
  returns  l' : deque t
  ensures  is_deque l' (x::xs)
{
  is_deque_cons_not_none l;
  assert (pure (Some? l.head));
  assert (pure (Some? l.tail));

  let h = hide (Cons?.hd xs);
  let t = hide (Cons?.tl xs);

  rewrite (is_deque l xs)
       as (is_deque l (reveal h :: reveal t));
  unfold is_deque;

  let vnode = {
    value = x;
    dprev = None;
    dnext = l.head;
  };
  let node = alloc vnode;

  let hh = Some?.v l.head;
  let tt = Some?.v l.tail;

  assert (is_deque_suffix hh (reveal h :: reveal t) None tt None);
  set_back_pointer hh (Some node);
  assert (is_deque_suffix hh (reveal h :: reveal t) (Some node) tt None);
  fold (is_deque_suffix node (x :: reveal h :: reveal t) None tt None);

  let l' = {
    head = Some node;
    tail = l.tail;
  };

  fold (is_deque l' (x::xs));
  l'
}
```

```pulse
fn push_front (#t:Type) (l : deque t) (x : t)
  (#xs:erased (list t))
  requires is_deque l xs
  returns  l' : deque t
  ensures  is_deque l' (x::xs)
{
  match l.head {
    None -> {
      is_deque_null_head_ptr l;
      push_front_empty l x;
    }
    Some hp -> {
      is_deque_some_head_ptr l;
      push_front_cons l x;
    }
  }
}
```

(* Popping the last element *)
```pulse
fn pop_front_nil (#t:Type) (l : deque t)
  (#x : erased t)
  requires is_deque l [reveal x]
  returns  l'x : (deque t & t)
  ensures  is_deque (fst l'x) [] ** pure (snd l'x == x)
{
  is_deque_cons_not_none l;
  assert (pure (Some? l.head));
  assert (pure (Some? l.tail));

  unfold is_deque;

  with hp tp.
    assert (is_deque_suffix hp [reveal x] None tp None);
  unfold is_deque_suffix;

  assert (pure (Some? l.head));
  assert (pure (Some? l.tail));
  assert (pure (l.head == l.tail));

  let headp = Some?.v l.head;
  rewrite each hp as headp;

  let v = !headp;

  let x = v.value;

  free headp;

  let l' : deque t = {
    head = None;
    tail = None;
  };
  fold (is_deque l' []);

  (l', x)
}
```

```pulse
fn pop_front_cons (#t:Type) (l : deque t)
  (#x : erased t)
  (#xs : erased (list t))
  requires is_deque l (reveal x :: xs) ** pure (Cons? xs)
  returns  l'x : (deque t & t)
  ensures  is_deque (fst l'x) xs ** pure (snd l'x == x)
{
  let y = hide (Cons?.hd xs);
  let ys = hide (Cons?.tl xs);
  rewrite each xs as (reveal y :: reveal ys);

  unfold is_deque;
  with hp tp.
    assert (is_deque_suffix hp (reveal x :: reveal y :: reveal ys) None tp None);

  assert (pure (l.head == Some hp));
  assert (pure (l.tail == Some tp));

  let headp = Some?.v l.head;
  rewrite each hp as headp;
  unfold is_deque_suffix;

  (* Get the value, free the cell *)
  let n1 = !headp;
  let retv = n1.value;
  free headp;

  assert (pure (Some? n1.dnext));

  let headp' = Some?.v n1.dnext;

  (* Unset the back pointer of the now-first cell. *)
  set_back_pointer headp' None;

  let l' = { head = Some headp'; tail = l.tail };
  fold (is_deque l' (reveal y :: reveal ys));

  (l', retv)
}
```

```pulse
ghost
fn suffix_factored_none_helper
  (#t:_)
  (p:node_ptr t)
  (x:t)
  (l:list t) (tail:node_ptr t) (last : option (node_ptr t))
  requires
    is_deque_suffix_factored_next p (x::l) tail last None
  ensures
    is_deque_suffix_factored_next p (x::l) tail last None ** pure (l == [])
{
  unfold (is_deque_suffix_factored_next p (x::l) tail last None);
  match l {
    Nil -> {
      fold (is_deque_suffix_factored_next p (x::l) tail last None);
    }
    Cons y ys -> {
      fold (is_deque_suffix_factored_next p (x::l) tail last None);
    }
  }
}
```

```pulse
ghost
fn suffix_factored_some_helper
  (#t:_)
  (p:node_ptr t)
  (x:t)
  (l:list t) (tail:node_ptr t)
  (np : node_ptr t)
  requires
    is_deque_suffix_factored_next p (x::l) tail None (Some np)
  ensures
    is_deque_suffix_factored_next p (x::l) tail None (Some np) ** pure (Cons? l)
{
  unfold (is_deque_suffix_factored_next p (x::l) tail None (Some np));
  match l {
    Nil -> {
      assert (pure False); // somehow I need this!!
      unreachable();
    }
    Cons y ys -> {
      assert (pure (Cons? l));
      fold (is_deque_suffix_factored_next p (x::y::ys) tail None (Some np));
    }
  }
}
```

```pulse
fn is_singleton
  (#t:Type) (p : deque t)
  (#x : erased t)
  (#xs : erased (list t))
  requires is_deque p (reveal x::xs)
  returns  b : bool
  ensures  is_deque p (reveal x::xs) ** pure (b <==> Nil? xs)
{
  is_deque_cons_not_none p;
  unfold is_deque;
  let headp = Some?.v p.head;
  factor_is_deque_suffix headp _ _ _;
  unfold is_deque_suffix_factored;

  with v. assert (pts_to headp v);
  let vv = !headp;
  rewrite each v as vv;

  let nextp = vv.dnext;
  rewrite each vv.dnext as nextp;

  if (None? nextp) {
    rewrite each nextp as None;
    suffix_factored_none_helper headp x xs _ _;
    assert (pure (Nil? xs));
    fold is_deque_suffix_factored_next;
    with tp.
      rewrite
        is_deque_suffix_factored_next headp (reveal x :: reveal xs) tp None None
      as
        is_deque_suffix_factored_next headp (reveal x :: reveal xs) tp None vv.dnext;

    fold is_deque_suffix_factored;
    unfactor_is_deque_suffix headp _ _ _;
    fold (is_deque p (reveal x::xs));
    true;
  } else {
    let np = Some?.v nextp;
    rewrite each nextp as (Some np);
    suffix_factored_some_helper headp x xs _ _;
    assert (pure (Cons? xs));

    fold is_deque_suffix_factored_next;
    with tp.
      rewrite
        is_deque_suffix_factored_next headp (reveal x :: reveal xs) tp None (Some np)
      as
        is_deque_suffix_factored_next headp (reveal x :: reveal xs) tp None vv.dnext;

    fold is_deque_suffix_factored;
    unfactor_is_deque_suffix headp _ _ _;
    fold (is_deque p (reveal x::xs));

    false;
  }
}
```

```pulse
fn pop_front (#t:Type) (l : deque t)
  (#x : erased t)
  (#xs : erased (list t))
  requires is_deque l (reveal x :: xs)
  returns  l'x : (deque t & t)
  ensures  is_deque (fst l'x) xs ** pure (snd l'x == x)
{
  let b = is_singleton l;
  if b {
    pop_front_nil l;
  } else {
    pop_front_cons l;
  }
}
```

val snoc : #t:_ -> list t -> t -> l':list t{Cons? l'}
let snoc xs x = xs @ [x]

```pulse
ghost
fn rec join_last 
  (#t:Type) (headp : node_ptr t) (tailp : node_ptr t) (tailp' : node_ptr t)
  (#y : erased t)
  (#ys : erased (list t){Cons? ys})
  (#prev : erased (option (node_ptr t)))
  (#last : erased (option (node_ptr t)))
  (#v : erased (node t))
  requires is_deque_suffix headp ys prev tailp (Some tailp') **
           pts_to tailp' v **
           pure (v.value == y /\ v.dprev == Some (reveal tailp) /\ v.dnext == last)
  ensures  is_deque_suffix headp (snoc ys y) prev tailp' last
  decreases length ys
{
  let y1 : t = Cons?.hd ys;
  let ys1 : list t = Cons?.tl ys;
  rewrite each ys as (y1 :: ys1);
  match ys1 {
    Nil -> {
      unfold is_deque_suffix headp [y1] prev         tailp (Some tailp');
      assert (pure (headp == tailp));
      fold   is_deque_suffix tailp' [reveal y]            (Some tailp) tailp' last;
      fold   is_deque_suffix headp  [reveal y1; reveal y] prev         tailp' last;
    }
    Cons y2 ys' -> {
      unfold (is_deque_suffix headp (y1 :: y2 :: ys') prev tailp (Some tailp'));
      with headp'.
        assert (is_deque_suffix headp' (y2 :: ys') (Some headp) tailp (Some tailp'));
      join_last headp' tailp tailp' #y #(y2 :: ys') #(Some headp) #last #v;
      
      rewrite 
        is_deque_suffix
          headp'
          (snoc (y2::ys') (reveal y))
          (Some headp)
          tailp'
          last
      as
        is_deque_suffix
          headp'
          (y2 :: snoc ys' (reveal y))
          (Some headp)
          tailp'
          last;
      
      fold_is_deque_suffix_cons headp y1 (y2 :: snoc ys' y) prev tailp' last _ headp';
    }
  }
}
```

let tag_pure p = pure p

(* This should really be just a consequence of proving a pure lemma. *)
```pulse
ghost
fn rec unsnoc_list (#t:Type0) (l : list t)
  requires pure (Cons? l)
  returns  ysy  :  erased (list t & t)
  ensures  tag_pure (eq2 #(list t) l (fst ysy @ [snd ysy]))
  decreases length l
{
  let hd = Cons?.hd l;
  let tl = Cons?.tl l;
  match tl {
    Nil -> {
      let ys = Nil #t;
      let y = hd;
      fold (tag_pure (l == ys @ [y]));
      (ys, y)
    }
    Cons _ _ -> {
      let ysy = unsnoc_list tl;
      let ys = fst ysy;
      let y = snd ysy;
      assert (tag_pure (eq2 #(list t) tl (ys @ [y])));
      unfold tag_pure;
      let ys' = hd :: ys;
      fold (tag_pure (l == ys' @ [y]));
      (ys', y)
    }
  }
}
```

```pulse
ghost
fn fold_is_deque_cons
  (#t:Type0)
  (l : deque t) (#xs : (list t){Cons? xs})
  (#hp:_) (#tp:_)
  requires is_deque_suffix hp xs None tp None
           ** pure (l.head == Some hp /\ l.tail == Some tp)
  ensures  is_deque l xs
{
  match xs {
    Nil -> {
      unreachable();
    }
    Cons hd tl -> {
      rewrite each xs as Cons hd tl;
      fold (is_deque l (hd :: tl));
    }
  }
}
```

```pulse
ghost
fn rec sep_last 
  (#t:Type) (headp : node_ptr t) (tailp : node_ptr t)
  (#y : erased t)
  (#ys : erased (list t){Cons? ys})
  (#prev : erased (option (node_ptr t)))
  (#last : erased (option (node_ptr t)))
  requires is_deque_suffix headp (snoc ys y) prev tailp last
  returns  tailp' : erased (node_ptr t)
  ensures  is_deque_suffix headp ys prev tailp' (Some tailp) **
           (exists* v. pts_to tailp v
                    ** pure (v.value == y /\ v.dprev == Some (reveal tailp') /\ v.dnext == last))
  decreases length ys
{
  let y1 = Cons?.hd ys;
  let ys1 = Cons?.tl ys;
  rewrite each ys as (y1 :: ys1);
  match ys1 {
    Nil -> {
      rewrite
        is_deque_suffix headp (snoc [y1] y) prev tailp last
      as
        is_deque_suffix headp [y1; reveal y] prev tailp last;

      unfold is_deque_suffix;
      with v_headp. assert (pts_to headp v_headp);
      with np. assert (is_deque_suffix np [reveal y] (Some headp) tailp last);
      unfold is_deque_suffix np [reveal y] (Some headp) tailp last;

      fold (is_deque_suffix headp [y1] prev headp (Some tailp));
      
      let tailp' = Some?.v v_headp.dnext;
      assert (pure (np == tailp));
      
      rewrite each np as tailp;

      headp
    }
    Cons y2 ys' -> {
      assert (is_deque_suffix headp (snoc (y1 :: y2 :: ys') y) prev tailp last);
      rewrite (is_deque_suffix headp (snoc (y1 :: y2 :: ys') y) prev tailp last)
           as (is_deque_suffix headp (y1 :: y2 :: snoc ys' y) prev tailp last);

      unfold (is_deque_suffix headp (y1 :: y2 :: snoc ys' y) prev tailp last);
      
      with v np. assert (pts_to headp v ** is_deque_suffix np (y2 :: snoc ys' y) (Some headp) tailp last);
      rewrite is_deque_suffix np (y2 :: snoc ys' y) (Some headp) tailp last
           as is_deque_suffix np (snoc (y2 :: ys') y) (Some headp) tailp last;
      let tailp' = sep_last np tailp;
      
      fold (is_deque_suffix headp (y1 :: y2 :: ys') prev tailp' (Some tailp));

      tailp';
    }
  };
}
```

let rec is_deque_suffix_nolast 
  (#t:Type0)
  (p:node_ptr t)
  (l:list t {Cons? l})
  (prev:option (node_ptr t))
  (tail:node_ptr t)
  : Tot slprop (decreases l)
  = match l with
    | [n] ->
      pure (p == tail)
    | n::ns ->
      exists* (v:node t) (np:node_ptr t).
        pts_to p v **
        is_deque_suffix_nolast np ns (Some p) tail **
        pure (v.value == n /\
          v.dprev == prev /\
          v.dnext == (Some np))

```pulse
ghost
fn rec is_deque_suffix_nolast_helper
  (#t:Type0)
  (p:node_ptr t)
  (l:list t {Cons? l})
  (prev:option (node_ptr t))
  (tail : node_ptr t)
  (last  : option (node_ptr t))
  (last' : option (node_ptr t))
  requires is_deque_suffix p l prev tail last
  returns  v : erased (node t)
  ensures  pts_to tail v **
           trade (pts_to tail { v with dnext = last' }) (is_deque_suffix p l prev tail last')
  decreases length l
{
  let hd = List.Tot.hd l;
  let tl = List.Tot.tl l;
  rewrite each l as (hd :: tl);
  
  match tl {
    Nil -> {
      unfold is_deque_suffix p [hd] prev tail last;
      rewrite each p as tail;
      with v. assert (pts_to tail v);
      ghost fn pf ()
        requires
          emp **
          pts_to tail ({ v with dnext = last' })
        ensures
          is_deque_suffix p [hd] prev tail last'
      {
        rewrite each tail as p;
        fold (is_deque_suffix p [hd] prev tail last');
      };
      intro_trade
        (pts_to tail { v with dnext = last' })
        (is_deque_suffix p [hd] prev tail last')
        emp
        pf;
      v;
    }
    Cons h2 tl2 -> {
      rewrite each l as (hd :: h2 :: tl2);
      unfold is_deque_suffix p (hd :: h2 :: tl2) prev tail last;
      
      with vp. assert (pts_to p vp);
      let p' = Some?.v vp.dnext;
      
      let v = is_deque_suffix_nolast_helper p' (h2 :: tl2) (Some p) tail last last';

      ghost fn pf ()
        requires
          (
            pts_to p vp **
            trade (pts_to tail { v with dnext = last' }) (is_deque_suffix p' (h2 :: tl2) (Some p) tail last')
          ) **
          pts_to tail ({ v with dnext = last' })
        ensures
          is_deque_suffix p (hd :: h2 :: tl2) prev tail last'
      {
        elim_trade _ _;
        fold (is_deque_suffix p (hd :: h2 :: tl2) prev tail last');
      };
      intro_trade
        (pts_to tail { v with dnext = last' })
        (is_deque_suffix p (hd :: h2 :: tl2) prev tail last')
        (
          pts_to p vp **
          trade (pts_to tail { v with dnext = last' }) (is_deque_suffix p' (h2 :: tl2) (Some p) tail last')
        )
        pf;

      v;
    }
  }
}
```

```pulse
fn set_forward_pointer
  (#t:Type) (headp : node_ptr t)
  (last' : option (node_ptr t))
  (#xs : erased (list t){length xs >= 1})
  (#prev : erased (option (node_ptr t)))
  (tail : (node_ptr t))
  (#last : erased (option (node_ptr t)))
  requires is_deque_suffix headp xs prev tail last
  ensures  is_deque_suffix headp xs prev tail last'
{
  is_deque_suffix_nolast_helper headp xs prev tail last last';

  let v = !tail;
  let v' = { v with dnext = last' };
  tail := v';
  
  elim_trade _ _;
}
```

```pulse
fn push_back_cons (#t:Type0) (l : deque t)
  (x : t)
  (#xs : erased (list t))
  requires is_deque l xs ** pure (Cons? xs)
  returns  l' : deque t
  ensures  is_deque l' (snoc xs x)
{
  unsnoc_list xs;
  with ys y. assert (tag_pure (reveal xs == ys @ [y]));
  unfold tag_pure;
  assert (pure (xs == ys @ [y]));
  
  rewrite each xs as (ys @ [y]);
  
  is_deque_cons_not_none l;
  unfold_is_deque_cons l;
  let headp = Some?.v l.head;    rewrite each l.head as (Some headp);
  let tailp = Some?.v l.tail;    rewrite each l.tail as (Some tailp);
  
  let newnodev = {
    value = x;
    dprev = l.tail;
    dnext = None;
  };
  let newnode = alloc newnodev;
  
  set_forward_pointer headp (Some newnode) tailp;
  
  join_last headp tailp newnode #x #(snoc ys y) #None #None;
  
  let l' = {
    head = l.head;
    tail = Some newnode;
  };
  
  fold_is_deque_cons l';
  l'
}
```

```pulse
fn push_back_nil (#t:Type0) (l : deque t)
  (x : t)
  (#xs : erased (list t))
  requires is_deque l xs ** pure (Nil? xs)
  returns  l' : deque t
  ensures  is_deque l' (snoc xs x)
{
  push_front_empty l x;
}
```

```pulse
fn push_back (#t:Type) (l : deque t) (x : t)
  (#xs : erased (list t))
  requires is_deque l xs
  returns  l'  :  deque t
  ensures  is_deque l' (snoc xs x)
{
  match l.head {
    None -> {
      is_deque_null_head_ptr l;
      push_back_nil l x;
    }
    Some hp -> {
      is_deque_some_head_ptr l;
      push_back_cons l x;
    }
  }
}
```

```pulse
fn pop_back_cons (#t:Type0) (l : deque t)
  (#x : erased t)
  (#xs : erased (list t))
  requires is_deque l (snoc xs x) ** pure (Cons? xs)
  returns  l'x  :  (deque t & t)
  ensures  is_deque (fst l'x) xs ** pure (snd l'x == x)
{
  is_deque_cons_not_none l;
  unfold_is_deque_cons l;
  let headp = Some?.v l.head;    rewrite each l.head as (Some headp);
  let tailp = Some?.v l.tail;    rewrite each l.tail as (Some tailp);

  let g_tailp' = sep_last headp tailp #x #xs #None #None;
  
  let v_last = !tailp;
  
  let tailp' = Some?.v v_last.dprev;
  let v = v_last.value;
  free tailp;
  
  set_forward_pointer headp None tailp';
  
  let l' = { head = l.head; tail = Some tailp' };

  fold_is_deque_cons l';
  (l', v)
}
```


```pulse
fn pop_back_nil (#t:Type0) (l : deque t)
  (#x : erased t)
  requires is_deque l [reveal x]
  returns  l'x  :  (deque t & t)
  ensures  is_deque (fst l'x) [] ** pure (snd l'x == x)
{
  pop_front_nil l;
}
```

```pulse
fn is_singleton_snoc
  (#t:Type) (p : deque t)
  (#x : erased t)
  (#xs : erased (list t))
  requires is_deque p (snoc xs (reveal x))
  returns  b : bool
  ensures  is_deque p (snoc xs (reveal x)) ** pure (b <==> Nil? xs)
{
  assert (pure (Cons? (snoc xs (reveal x))));
  let h = hide (Cons?.hd (snoc xs (reveal x)));
  let t = hide (Cons?.tl (snoc xs (reveal x)));
  rewrite (is_deque p (snoc xs (reveal x)))
       as (is_deque p (reveal h :: reveal t));
       
  (* This works quite nicely. The SMT is giving us that the LHS of the
  snoc is Nil iff `t` above is nil. *)
  is_singleton p;
}
```

```pulse
fn pop_back (#t:Type0) (l : deque t)
  (#x : erased t)
  (#xs : erased (list t))
  requires is_deque l (snoc xs x)
  returns  l'x  :  (deque t & t)
  ensures  is_deque (fst l'x) xs ** pure (snd l'x == x)
{
  let b = is_singleton_snoc l;
  if b {
    rewrite each (snoc (reveal xs) (reveal x)) as [reveal x];
    pop_back_nil l;
  } else {
    pop_back_cons l;
  }
}
```
