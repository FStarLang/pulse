module Demo.VSS2025_2
#lang-pulse
open FStar.Mul
open Pulse.Lib
open Pulse.Lib.Pervasives

////////////////////////////////////////////////////
// Some simple data structures
////////////////////////////////////////////////////
noeq
type point = {
    x:ref int;
    y:ref int;
}

let is_point (p:point) (x y:int) : slprop =
  pts_to p.x x **
  pts_to p.y y

fn move (p:point) (dx:int) (dy:int)
requires is_point p 'x 'y
ensures is_point p ('x + dx) ('y + dy)
{
  unfold is_point;
  let x = !p.x;
  let y = !p.y;
  p.x := x + dx;
  p.y := y + dy;
  fold is_point; 
}

fn test (x y:int)
requires emp
ensures emp
{
  let mut x = 0;
  let mut y = 0;
  let p = { x; y };
  rewrite each x as p.x, y as p.y;
  fold (is_point p 0 0);
  move p 5 10;
  move p 10 5;
  assert (is_point p 15 15);
  unfold is_point;
  rewrite each p.x as x, p.y as y;
}

////////////////////////////////////////////////////
// A linked list
////////////////////////////////////////////////////
noeq
type node (t:Type0) = {
    head : t;
    tail : llist t;
}

and node_ptr (t:Type0) = ref (node t)

//A nullable pointer to a node
and llist (t:Type0) = option (node_ptr t)

let rec is_list #t (x:llist t) (l:list t)
: Tot slprop (decreases l)
= match l with
  | [] -> pure (x == None)
  | head::tl -> 
    exists* (p:node_ptr t) (tail:llist t).
      pure (x == Some p) **
      pts_to p { head; tail } **
      is_list tail tl

ghost
fn intro_is_list_cons (#t:Type0) (x:llist t) (v:node_ptr t) (#node:node t) (#tl:list t)
requires
  pts_to v node **
  is_list node.tail tl **
  pure (x == Some v)
ensures
  is_list x (node.head::tl)
{
  rewrite (pts_to v node) as (pts_to v { head=node.head; tail=node.tail });
  fold (is_list x (node.head::tl));
}

let is_list_cases #t (x:llist t) (l:list t)
: slprop 
= match x with
  | None -> pure (l == [])
  | Some v -> 
    exists* (n:node t) (tl:list t).
      pts_to v n **
      pure (l == n.head::tl) **
      is_list n.tail tl

ghost
fn cases_of_is_list #t (x:llist t) (l:list t)
requires is_list x l
ensures is_list_cases x l
{
  match l {
    [] -> {
      unfold is_list;
      fold (is_list_cases None l);
    }
    head :: tl -> {
      unfold (is_list x (head :: tl));
      with w tail. _;
      let v = Some?.v x;
      rewrite each w as v;
      fold (is_list_cases (Some v) l);
    }
  }
}


fn rec length (#t:Type0) (x:llist t)
requires is_list x 'l
returns n:nat
ensures is_list x 'l ** pure (n == List.Tot.length 'l)
{
  cases_of_is_list _ _;
  match x {
    None -> {
      unfold (is_list_cases None 'l);
      fold (is_list #t None []);
      0
    }
    Some vl -> {
      unfold (is_list_cases (Some vl) 'l);  
      let node = !vl;
      let n = length node.tail;
      intro_is_list_cons x vl;
      (1 + n)
    }
  }
}

///////////////////////////////////////////////////////////
// A little glimpse into the checker: SMT only when needed
///////////////////////////////////////////////////////////
module DQ = Pulse.Lib.DequeRef

fn test_dq ()
requires emp
returns dq:DQ.dq int
ensures DQ.is_dq dq []
{
  let dq = DQ.mk_empty #int ();
  DQ.push_front dq 1;
  DQ.push_front dq 2;
  DQ.push_front dq 3;
  DQ.push_front dq 4;
  DQ.push_front dq 5;
  let _ = DQ.pop_front dq;
  let _ = DQ.pop_front dq;
  let _ = DQ.pop_front dq;
  let _ = DQ.pop_front dq;
  let _ = DQ.pop_front dq;
  dq
}