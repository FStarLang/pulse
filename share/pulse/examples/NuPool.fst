module NuPool

// TODO: I think this invariant trick to make the big_joinables
// small is a generic thing, and we could do it *outside* this module too.
// That is, define a wrapper where the pool'  type is pool+ghost handle list+invariant,
// and define the small operations over these big ones.

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open FStar.Tactics
open FStar.Preorder
open Pulse.Lib.Par.Pledge
open Pulse.Lib.Trade
open Pulse.Lib.InvList
open Pulse.Class.Duplicable

module FRAP  = Pulse.Lib.FractionalAnchoredPreorder
module BAR   = Pulse.Lib.BigAnchoredReference
module AR    = Pulse.Lib.AnchoredReference
module Big   = Pulse.Lib.BigReference
module Ghost = Pulse.Lib.GhostReference

unfold let p12 : perm = half_perm full_perm
unfold let p14 : perm = half_perm (half_perm full_perm)

let vprop_equiv_refl (v1 v2 : vprop) (_ : squash (v1 == v2))
  : vprop_equiv v1 v2 = vprop_equiv_refl _

let helper_tac () : Tac unit =
  apply (`vprop_equiv_refl);
  trefl()

(* This MUST be Type0 *)
noeq
type task_state : Type0 =
  | Ready    : task_state
  | Running  : task_state
  | Done     : task_state
  | Claimed  : task_state

let unclaimed (s : task_state) : task_state =
  match s with
  | Claimed -> Done
  | x -> x

let v (s : task_state) : int =
  match s with
  | Ready -> 0
  | Running -> 1
  | Done -> 2
  | Claimed -> 3
  
let p_st : preorder (task_state) = fun x y -> b2t (v x <= v y)

let anchor_rel : FRAP.anchor_rel p_st =
  fun (x y : task_state) ->
    match x, y with
    | Ready, Claimed -> False
    | x, y -> squash (p_st x y)

let anchor_rel_refl (x:task_state) :
  Lemma (anchor_rel x x) [SMTPat (anchor_rel x x)]
  =
  assert_norm (anchor_rel Ready Ready);
  assert_norm (anchor_rel Running Running);
  assert_norm (anchor_rel Done Done);
  assert_norm (anchor_rel Claimed Claimed)

let state_res #code
  ([@@@equate_by_smt]pre : erased code.t)
  ([@@@equate_by_smt]post : erased code.t)
  (g_state : AR.ref task_state p_st anchor_rel)
  ([@@@equate_by_smt] st : task_state)
=
  match st with
  | Ready -> code.up pre
  | Running -> emp
  | Done -> code.up post
  | Claimed -> AR.anchored g_state Claimed

noeq
type handle : Type u#0 = {
  state   : ref task_state;
  g_state : AR.ref task_state p_st anchor_rel; (* these two refs are kept in sync *)
}

noeq
type task_t (code : vcode) : Type u#2 = {
  pre :  erased code.t;
  post : erased code.t;

  h : handle;

  thunk : unit -> stt unit (code.up pre) (fun _ -> code.up post);
}

let state_pred
  (#code:vcode)
  ([@@@equate_by_smt] pre : erased code.t)
  ([@@@equate_by_smt] post : erased code.t)
  ([@@@equate_by_smt] h : handle)
: vprop =
  exists* (v_state : task_state).
    pts_to
      h.state
      #(if Running? v_state then half_perm full_perm else full_perm)
      (unclaimed v_state)
      **
    AR.pts_to h.g_state v_state **
    state_res pre post h.g_state v_state

// equate_by_smt due to #22
let rec all_state_pred
  (#code:vcode)
  ([@@@equate_by_smt] v_runnable : list (task_t code))
: vprop
= match v_runnable with
  | [] -> emp
  | t :: ts ->
    state_pred t.pre t.post t.h **
    all_state_pred ts

```pulse
ghost
fn add_one_state_pred (#code:vcode)
  (t : task_t code)
  (v_runnable : list (task_t code))
  requires state_pred t.pre t.post t.h
        ** all_state_pred v_runnable
  ensures  all_state_pred (t :: v_runnable)
{
  fold (all_state_pred (t :: v_runnable));
}
```

```pulse
ghost
fn take_one_h11 (#code:vcode)
  (t : task_t code)
  (v_runnable : list (task_t code))
  requires all_state_pred (t :: v_runnable)
  ensures  state_pred t.pre t.post t.h
        ** all_state_pred v_runnable
{
  unfold (all_state_pred (t :: v_runnable));
}
```
(** List preorder and anchor relation. Used for the runnable lists
which are monotonically increasing. **)
let list_extension #a (t0 t1 : list a)
  : prop
  = Cons? t1 /\ t0 == List.Tot.tail t1

let list_preorder #a
  : FStar.Preorder.preorder (list a)
  = FStar.ReflexiveTransitiveClosure.closure list_extension

let list_anchor : FRAP.anchor_rel list_preorder = fun x y -> list_preorder x y /\ True

let list_preorder_mono_memP (#a:Type) (x:a) (l1 l2:list a)
  : Lemma (requires List.memP x l1 /\ list_preorder l1 l2)
          (ensures List.memP x l2)
          [SMTPat (list_preorder l1 l2); SMTPat (List.memP x l1)]
      = admit()

let lock_inv (#code:vcode)
  (runnable   : Big.ref (list (task_t code)))
  (g_runnable : BAR.ref (list (task_t code)) list_preorder list_anchor)
: vprop
= 
  exists*
    (v_runnable : list (task_t code))
  .
    Big.pts_to      runnable        v_runnable **
    BAR.pts_to_full g_runnable #p12 v_runnable **
    all_state_pred v_runnable

let rec handles_one_to_one (#code:vcode)
  (v_runnable : list (task_t code))
  (handles : list handle)
  : vprop
= match v_runnable, handles with
  | [], [] -> emp
  | t::ts, h::hs ->
    pure (t.h == h) ** handles_one_to_one ts hs
  | _ -> pure False

let small_handle_list_inv (#code:vcode)
  (g_runnable : BAR.ref (list (task_t code)) list_preorder list_anchor)
  (small_handle_list : AR.ref (list handle) list_preorder list_anchor)
  =
  exists*
    (v_runnable : list (task_t code))
    (handles : list handle)
  .
    BAR.pts_to_full g_runnable #p12 v_runnable **
    AR.pts_to_full small_handle_list handles **
    handles_one_to_one v_runnable handles

noeq
type pool_st (code:vcode) : Type u#0 = {
  runnable   : Big.ref (list (task_t code));
  g_runnable : BAR.ref (list (task_t code)) list_preorder list_anchor;

  small_handle_list : AR.ref (list handle) list_preorder list_anchor;

  i : inv (small_handle_list_inv g_runnable small_handle_list);

  lk : lock (lock_inv runnable g_runnable);
}
type pool (code:vcode) = pool_st code

let pool_invlist (#code:vcode) (p:pool code)
  : invlist
  = add_one (| _, p.i |) invlist_empty

(* Assuming a vprop for lock ownership. *)
assume val lock_alive
  (#p:vprop)
  (#[exact (`full_perm)] f : perm)
  (l : lock p)
  : (v:vprop{is_small v})

let pool_alive (#[exact (`full_perm)] f : perm) (#code:vcode) (p:pool code) : vprop =
  lock_alive #_ #(half_perm f) p.lk

let state_res' #code (post : erased code.t) ([@@@equate_by_smt] st : task_state) =
  match st with
  | Done -> code.up post
  | Claimed -> emp
  | _ -> pure False

let big_task_spotted (#code:vcode)
  (p : pool code)
  (t : task_t code)
: vprop =
  exists* v_runnable.
    BAR.snapshot p.g_runnable v_runnable **
    pure (List.memP t v_runnable)

let big_handle_spotted (#code:vcode)
  (p : pool code)
  (post : erased code.t)
  (h : handle)
  : vprop =
    exists* (t : task_t code).
      big_task_spotted p t **
      pure (t.post == post /\ t.h == h)

let big_joinable
  (#code:vcode) (p : pool code)
  ([@@@equate_by_smt]post:erased code.t)
  ([@@@equate_by_smt]h : handle)
: vprop =
  AR.anchored h.g_state Ready **
  big_handle_spotted p post h

let handle_spotted (#code:vcode)
  (p : pool code)
  (post : erased code.t)
  (h : handle)
  : vprop =
    exists* v_small_handle_list.
      AR.snapshot p.small_handle_list v_small_handle_list **
      pure (List.memP h v_small_handle_list)

let joinable
  (#code:vcode) (p : pool code)
  ([@@@equate_by_smt]post:erased code.t)
  ([@@@equate_by_smt]h : handle)
: vprop =
  AR.anchored h.g_state Ready **
  handle_spotted p post h
  
(* Small to large *)
```pulse
ghost
fn ghost_spotted_s2l (#code:vcode)
  (p : pool code)
  (post : erased code.t)
  (h : handle)
  requires small_handle_list_inv p.g_runnable p.small_handle_list ** handle_spotted p post h
  ensures  small_handle_list_inv p.g_runnable p.small_handle_list ** big_handle_spotted p post h
{
  admit()
}
```

```pulse
unobservable
fn spotted_s2l (#code:vcode)
  (p : pool code)
  (post : erased code.t)
  (h : handle)
  requires handle_spotted p post h
  ensures  big_handle_spotted p post h
  opens add_inv emp_inames p.i
{
  with_invariants p.i {
    ghost_spotted_s2l p post h;
  }
}
```

```pulse
ghost
fn ghost_joinable_s2l (#code:vcode)
  (p : pool code) (post : erased code.t) (h : handle)
  requires small_handle_list_inv p.g_runnable p.small_handle_list ** joinable p post h
  ensures  small_handle_list_inv p.g_runnable p.small_handle_list ** big_joinable p post h
{
  unfold (joinable #code p post h);
  ghost_spotted_s2l p post h;
  fold (big_joinable #code p post h);
}
```

```pulse
unobservable
fn joinable_s2l (#code:vcode)
  (p : pool code) (post : erased code.t) (h : handle)
  requires joinable p post h
  ensures  big_joinable p post h
  opens add_inv emp_inames p.i
{
  unfold (joinable #code p post h);
  spotted_s2l p post h;
  fold (big_joinable #code p post h);
}
```


```pulse
ghost
fn ghost_spotted_l2s (#code:vcode)
  (p : pool code)
  (post : erased code.t)
  (h : handle)
  requires small_handle_list_inv p.g_runnable p.small_handle_list ** big_handle_spotted p post h
  ensures small_handle_list_inv p.g_runnable p.small_handle_list ** handle_spotted p post h
{
  admit()
}
```

```pulse
unobservable
fn spotted_l2s (#code:vcode)
  (p : pool code)
  (post : erased code.t)
  (h : handle)
  requires big_handle_spotted p post h
  ensures  handle_spotted p post h
  opens add_inv emp_inames p.i
{
  with_invariants p.i {
    ghost_spotted_l2s p post h;
  }
}
```

```pulse
ghost
fn ghost_joinable_l2s (#code:vcode)
  (p : pool code) (post : erased code.t) (h : handle)
  requires small_handle_list_inv p.g_runnable p.small_handle_list ** big_joinable p post h
  ensures  small_handle_list_inv p.g_runnable p.small_handle_list ** joinable p post h
{
  unfold (big_joinable #code p post h);
  ghost_spotted_l2s p post h;
  fold (joinable #code p post h);
}
```

```pulse
unobservable
fn joinable_l2s (#code:vcode)
  (p : pool code) (post : erased code.t) (h : handle)
  requires big_joinable p post h
  ensures  joinable p post h
  opens add_inv emp_inames p.i
{
  unfold (big_joinable #code p post h);
  spotted_l2s p post h;
  fold (joinable #code p post h);
}
```



```pulse
ghost
fn intro_big_task_spotted
    (#code:vcode) (p : pool code)
    (t : task_t code)
    (ts : list (task_t code))
  requires BAR.snapshot p.g_runnable ts
        ** pure (List.memP t ts)
  ensures  big_task_spotted p t
{
  fold (big_task_spotted p t);
}
```

```pulse
ghost
fn intro_big_handle_spotted
    (#code:vcode) (p : pool code)
    (t : task_t code)
    (ts : list (task_t code))
  requires BAR.snapshot p.g_runnable ts
        ** pure (List.memP t ts)
  ensures  big_handle_spotted p t.post t.h
{
  intro_big_task_spotted #code p t ts;
  fold (big_handle_spotted p t.post t.h);
}
```

```pulse
ghost
fn recall_task_spotted
  (#code:vcode) (p : pool code) (t : task_t code) (#ts : list (task_t code))
  (#f:perm)
  requires BAR.pts_to_full p.g_runnable #f ts ** big_task_spotted p t
  ensures  BAR.pts_to_full p.g_runnable #f ts ** big_task_spotted p t
           ** pure (List.memP t ts)
{
  unfold (big_task_spotted p t);
  BAR.recall_snapshot' p.g_runnable;
  fold (big_task_spotted p t);
}
```

```pulse
ghost
fn recall_handle_spotted
  (#code:vcode) (p : pool code) (post : erased code.t) (h : handle) (#ts : list (task_t code))
  (#f:perm)
  requires BAR.pts_to_full p.g_runnable #f ts ** big_handle_spotted p post h
  returns  task : erased (task_t code)
  ensures  BAR.pts_to_full p.g_runnable #f ts ** big_handle_spotted p post h **
            pure (task.post == post /\ task.h == h /\ List.memP (reveal task) ts)
{
  unfold (big_handle_spotted p post h);
  with t. assert (big_task_spotted p t);
  recall_task_spotted #code p t #ts;
  fold (big_handle_spotted p post h);
  hide t
}
```

```pulse
ghost
fn star_to_trade (p q : vprop)
  requires p ** q
  ensures  p ** trade p (p ** q)
{
  open Pulse.Lib.InvList;
  ghost
  fn aux (_:unit)
    requires (invlist_v invlist_empty ** q) ** p
    ensures   invlist_v invlist_empty ** (p ** q)
  {
    ()
  };
  intro_trade p (p ** q) q aux;
}
```

module SEM = FStar.StrongExcludedMiddle

```pulse
ghost
fn rec extract_state_pred
  (#code:vcode)
  (p : pool code) (t : task_t code)
  (#ts : list (task_t code))
  requires all_state_pred ts ** pure (List.memP t ts)
  ensures state_pred t.pre t.post t.h
       ** trade (state_pred t.pre t.post t.h) (all_state_pred ts) // trade to put things back together
  decreases ts
{
  open Pulse.Lib.InvList;
  match ts {
    Nil -> {
      unreachable ()
    }
    Cons t' ts' -> {
      let b = SEM.strong_excluded_middle (t == t');
      if not b {
        take_one_h11 t' ts';
        extract_state_pred p t #ts';

        ghost
        fn aux (_:unit)
          requires invlist_v invlist_empty **
                   state_pred t'.pre t'.post t'.h **
                   all_state_pred ts'
          ensures  invlist_v invlist_empty ** all_state_pred ts
        {
          add_one_state_pred t' ts';
        };
        intro_trade (all_state_pred ts') (all_state_pred ts)
                    (state_pred t'.pre t'.post t'.h) aux;

        trade_compose (state_pred t.pre t.post t.h) (all_state_pred ts') (all_state_pred ts);
      } else {
        rewrite each t' as t;
        take_one_h11 t ts';

        ghost
        fn aux (_:unit)
          requires (invlist_v invlist_empty ** (pure (ts == t'::ts') ** all_state_pred ts'))
                ** state_pred t'.pre t'.post t'.h
          ensures   invlist_v invlist_empty ** all_state_pred ts
        {
          add_one_state_pred t' ts';
        };
        intro_trade (state_pred t.pre t.post t.h) (all_state_pred ts)
                    (pure (ts == t'::ts') ** all_state_pred ts') aux;

        ()
      }
    }
  }
}
```

```pulse
ghost
fn push_handle (#a:Type) (x:a) (r : BAR.ref (list a) list_preorder list_anchor) (#xs:erased (list a))
  requires BAR.pts_to_full r xs
  ensures  BAR.pts_to_full r (x::xs)
{
  BAR.write_full r (x::xs);
}
```

```pulse
ghost
fn intro_state_pred
  (#code:vcode)
  (pre : erased code.t)
  (post : erased code.t)
  (h : handle)
  (v_state : task_state {~(Running? v_state)})
  requires
    pts_to h.state (unclaimed v_state) **
    AR.pts_to h.g_state v_state **
    state_res pre post h.g_state v_state
  ensures state_pred pre post h
{
  fold (state_pred pre post h);
}
```

```pulse
ghost
fn intro_state_pred_Running
  (#code:vcode)
  (pre : erased code.t)
  (post : erased code.t)
  (h : handle)
  requires
    pts_to h.state #(half_perm full_perm) Running **
    AR.pts_to h.g_state Running **
    state_res pre post h.g_state Running
  ensures state_pred pre post h
{
  rewrite (pts_to h.state #(half_perm full_perm) Running)
       as (pts_to h.state #(half_perm full_perm) (unclaimed Running));
  fold (state_pred pre post h);
}
```

```pulse
ghost
fn elim_state_pred
  (#code:vcode)
  (pre : erased code.t)
  (post : erased code.t)
  (h : handle)
  requires state_pred pre post h
  returns v_state : erased (task_state)
  ensures
    pts_to h.state #(if Running? v_state then half_perm full_perm else full_perm) (unclaimed v_state) **
    AR.pts_to h.g_state v_state **
    state_res pre post h.g_state v_state
{
  unfold (state_pred pre post h);
  with v_state. assert (state_res pre post h.g_state v_state);
  hide v_state
}
```

#set-options "--print_implicits"

```pulse
unobservable
fn add_task_and_handle 
    (#code:vcode)
    (p : pool code)
    (task : task_t code)
    (#v_runnable : erased (list (task_t code)))
    requires BAR.pts_to_full p.g_runnable #p12 v_runnable
    ensures  BAR.pts_to_full p.g_runnable #p12 (task :: v_runnable)
    opens add_inv emp_inames p.i
{
  with_invariants (p.i <: inv _)
  {
    unfold (small_handle_list_inv p.g_runnable p.small_handle_list);
    with v_runnable. assert (BAR.pts_to_full p.g_runnable #p12 v_runnable);
    with handles. assert (AR.pts_to_full p.small_handle_list handles);
    
    BAR.gather2' p.g_runnable;

    (* Update g_runnable queue *)
    BAR.write_full p.g_runnable (task :: v_runnable);
    
    (* Update small handle list *)
    AR.write_full p.small_handle_list (task.h :: handles);
    
    assert (handles_one_to_one v_runnable handles);
    
    (* Prove invariant. FIXME: a simple fold should do it. *)
    rewrite_by
      (pure (task.h == task.h) ** handles_one_to_one v_runnable handles)
      (handles_one_to_one (task :: v_runnable) (task.h :: handles))
      helper_tac
      ();
    
    BAR.share2' p.g_runnable;
    fold (small_handle_list_inv p.g_runnable p.small_handle_list);
  };
}
```

```pulse
fn __big_spawn (#code:vcode) (p:pool code)
    (#pf:perm)
    (#pre : erased code.t)
    (#post : erased code.t)
    (f : unit -> stt unit (code.up pre) (fun _ -> (code.up post)))
    requires pool_alive #pf p ** (code.up pre)
    returns  h : handle
    ensures  pool_alive #pf p ** big_joinable #code p post h
{
  let task_st : task_state = Ready;
  assert (pure (anchor_rel Ready Ready));
  let r_task_st : ref task_state = alloc task_st;
  let gr_task_st : AR.ref task_state p_st anchor_rel = AR.alloc #task_state task_st #p_st #anchor_rel;

  AR.drop_anchor gr_task_st;

  let handle : handle = {
    state = r_task_st;
    g_state = gr_task_st;
  };
  let task : task_t code = {
    h = handle;
    pre;
    post;
    thunk = f;
  };
  
  (* Probably the fragment above this line can be factored out. *)

  unfold (pool_alive #pf p);
  
  let lk = p.lk;
  let i = p.i;
  acquire lk;
  unfold (lock_inv p.runnable p.g_runnable);
  
  let v_runnable = Big.op_Bang p.runnable;

  Big.op_Colon_Equals p.runnable (task :: v_runnable);
  add_task_and_handle p task;

  rewrite each task_st as Ready;
  rewrite each gr_task_st as task.h.g_state;
  assert (AR.anchored task.h.g_state Ready);

  BAR.take_snapshot' p.g_runnable;
  
  assert (pure (List.memP task (task :: v_runnable)));
  // intro_task_spotted p task (task :: v_runnable);
  intro_big_handle_spotted p task (task :: v_runnable);

  fold (big_joinable #code p task.post task.h);

  fold (pool_alive #pf p);
  
  assert (pts_to #task_state r_task_st Ready);

  rewrite each r_task_st as handle.state;
  rewrite (code.up pre)
       as (state_res pre post gr_task_st Ready);
  rewrite each gr_task_st as handle.g_state;
  rewrite each handle as task.h;
  rewrite each pre as task.pre;
  rewrite each post as task.post;
   
  intro_state_pred task.pre task.post task.h Ready;
  // fold (state_pred #code task.pre task.post task.h);

  add_one_state_pred task v_runnable;

  fold (lock_inv p.runnable p.g_runnable);

  release lk;
  
  rewrite each task.post as post;

  task.h
}
```

```pulse
fn __spawn (#code:vcode) (p:pool code)
    (#pf:perm)
    (#pre : erased code.t)
    (#post : erased code.t)
    (f : unit -> stt unit (code.up pre) (fun _ -> (code.up post)))
    requires pool_alive #pf p ** (code.up pre)
    returns  h : handle
    ensures  pool_alive #pf p ** joinable #code p post h
{
  let h = __big_spawn p f;
  unfold (big_joinable #code p post h);
  spotted_l2s p post h;
  fold (joinable #code p post h);
  h
}
```

```pulse
ghost
fn claim_done_task
         (#code:vcode) (#p:pool code)
         (#pre : erased code.t) (#post : erased code.t)
         (h : handle)
  requires state_res pre post h.g_state Done    ** AR.pts_to h.g_state Done    ** AR.anchored h.g_state Ready
  ensures  state_res pre post h.g_state Claimed ** AR.pts_to h.g_state Claimed ** code.up post
{
  rewrite (state_res pre post h.g_state Done)
       as code.up post;

  AR.lift_anchor h.g_state Ready;

  AR.write_full h.g_state Claimed;

  AR.drop_anchor h.g_state;

  fold (state_res pre post h.g_state Claimed);

  ()
}
```

```pulse
fn __big_try_await
         (#code:vcode) (#p:pool code)
         (#post : erased code.t)
         (h : handle)
         (#f:perm)
  requires pool_alive #f p ** big_joinable p post h
  returns  ok : bool
  ensures  pool_alive #f p ** (if ok then code.up post else big_joinable p post h)
{
  unfold (pool_alive #f p);
  acquire p.lk;
  unfold (lock_inv p.runnable p.g_runnable);
  
  unfold (big_joinable p post h);

  with v_runnable. assert (Big.pts_to p.runnable v_runnable);

  unfold (big_handle_spotted p post h);

  with t. assert (big_task_spotted p t);
  recall_task_spotted #code p t #v_runnable;
  
  extract_state_pred p t #v_runnable;

  let v_state = elim_state_pred t.pre t.post t.h;

  rewrite (pts_to t.h.state #(if Running? v_state then half_perm full_perm else full_perm) (unclaimed (reveal v_state)))
       as (pts_to h.state #(if Running? v_state then half_perm full_perm else full_perm) (unclaimed (reveal v_state)));
  let task_st = !h.state;
  
  match task_st {
    Ready -> {
      (* NOOP *)
      rewrite (pts_to h.state (reveal v_state))
           as (pts_to t.h.state (reveal v_state));
      intro_state_pred t.pre t.post t.h Ready;
      elim_trade _ _; // undo extract_state_pred
      fold (lock_inv p.runnable p.g_runnable);
      release p.lk;
      fold (pool_alive #f p);
      fold (big_handle_spotted p post h);
      fold (big_joinable p post h);
      false;
    }
    Running -> {
      (* NOOP *)
      rewrite (pts_to h.state #(half_perm full_perm) (reveal v_state))
           as (pts_to t.h.state #(half_perm full_perm) (reveal v_state));
      intro_state_pred_Running t.pre t.post t.h;
      elim_trade _ _; // undo extract_state_pred
      fold (lock_inv p.runnable p.g_runnable);
      release p.lk;
      fold (pool_alive #f p);
      fold (big_handle_spotted p post h);
      fold (big_joinable p post h);
      false;
    }
    Done -> {
      (* First prove that ghost state cannot be Claimed,
      due to the anchor *)
      rewrite (AR.pts_to t.h.g_state v_state)
           as (AR.pts_to h.g_state v_state);
      assert (AR.pts_to h.g_state v_state);
      assert (AR.anchored h.g_state Ready);
      AR.recall_anchor h.g_state Ready;
      assert (pure (v_state =!= Claimed));
      assert (pure (v_state == Done));
      rewrite (AR.pts_to h.g_state v_state)
           as (AR.pts_to t.h.g_state v_state);

      (* Now claim it *)
      claim_done_task #code #p #t.pre #t.post t.h;

      rewrite (code.up post)
           as (if true then code.up post else joinable p post h);
           
      rewrite (pts_to h.state Done)
           as (pts_to t.h.state (unclaimed Claimed));
      intro_state_pred t.pre t.post t.h Claimed;
      elim_trade _ _; // undo extract_state_pred
      fold (lock_inv p.runnable p.g_runnable);
      release p.lk;
      fold (pool_alive #f p);
      drop_ (big_task_spotted p t);
      true
    }
    Claimed -> {
      (* Concrete state is never Claimed *)
      unreachable ();
    }
  }
}
```

```pulse
fn __try_await
         (#code:vcode) (#p:pool code)
         (#post : erased code.t)
         (h : handle)
         (#f:perm)
  requires pool_alive #f p ** joinable p post h
  returns  ok : bool
  ensures  pool_alive #f p ** (if ok then code.up post else joinable p post h)
{
  joinable_s2l p post h;
  let ok = __big_try_await #code #p #post h #f;
  if ok {
    // FIXME: I have no idea why this is enough, while a full rewrite
    // of the if+big_joinable to the if+joinable fails...
    rewrite (if ok then code.up post else big_joinable p post h)
         as code.up post;
    ok
  } else {
    joinable_l2s p post h;
    ok
  }
}
```

```pulse
// Busy waiting version of big_await
fn __big_await (#code:vcode) (#p:pool code)
         (#post : erased code.t)
         (h : handle)
         (#f:perm)
  requires pool_alive #f p ** big_joinable p post h
  ensures  pool_alive #f p ** code.up post
{
  let mut done = false;
  while (let v = !done; (not v))
    invariant b.
      exists* v_done.
        pool_alive #f p **
        pts_to done v_done **
        (if v_done then code.up post else big_joinable p post h) **
        pure (b == not v_done)
  {
    let b = __big_try_await #code #p #post h #f;
    done := b;
  };
}
```

```pulse
// Busy waiting version of await
fn __await (#code:vcode) (#p:pool code)
         (#post : erased code.t)
         (h : handle)
         (#f:perm)
  requires pool_alive #f p ** joinable p post h
  ensures  pool_alive #f p ** code.up post
{
  let mut done = false;
  while (let v = !done; (not v))
    invariant b.
      exists* v_done.
        pool_alive #f p **
        pts_to done v_done **
        (if v_done then code.up post else joinable p post h) **
        pure (b == not v_done)
  {
    let b = __try_await #code #p #post h #f;
    done := b;
  };
}
```

let handle_done (h:handle) : vprop =
  exists* (st : task_state).
    pure (st == Done \/ st == Claimed) **
    AR.snapshot h.g_state st

let task_done (#code:vcode) (t : task_t code)  : vprop =
  handle_done t.h

let rec all_tasks_done (#code:vcode) (ts : list (task_t code)) =
  match ts with
  | [] -> emp
  | t::ts' ->
    task_done t **
    all_tasks_done ts'

// FIXME: refactor this to provide task_done instead
```pulse
ghost
fn unfold_all_tasks_done_cons (#code:vcode) (t : task_t code) (ts : list (task_t code))
  requires all_tasks_done (t :: ts)
  returns  st : task_state
  ensures  pure (st == Done \/ st == Claimed) **
           AR.snapshot t.h.g_state st **
           all_tasks_done ts
{
  // This should not be so hard.
  rewrite_by
    (all_tasks_done (t :: ts))
    ((exists* (st : task_state).
      pure (st == Done \/ st == Claimed) **
      AR.snapshot t.h.g_state st) **
      all_tasks_done ts)
    helper_tac
    ();
  with st. assert AR.snapshot t.h.g_state st;
  st
}
```

```pulse
ghost
fn fold_all_tasks_done_cons (#code:vcode) (t : task_t code) (ts : list (task_t code))
  (st : task_state)
  requires pure (st == Done \/ st == Claimed) **
           AR.snapshot t.h.g_state st **
           all_tasks_done ts
  ensures  all_tasks_done (t :: ts)
{
  // This should not be so hard.
  rewrite_by
    ((exists* (st : task_state).
      pure (st == Done \/ st == Claimed) **
      AR.snapshot t.h.g_state st) **
      all_tasks_done ts)
    (all_tasks_done (t :: ts))
    helper_tac
    ();
}
```

instance dup_high_snapshot
  (#t:Type u#2)
  (#pre : preorder t)
  (#anc : FRAP.anchor_rel pre)
  (r:BAR.ref t pre anc)
  (v : t)
: duplicable (BAR.snapshot r v) = {
  // TODO: implement in BAR module, or tweak
  // take_snapshot to provide a snapshot of a possibly
  // "older" value. In that case this is easy to implement.
  dup_f = admit();
}

instance dup_snapshot
  (#t:Type u#0)
  (#pre : preorder t)
  (#anc : FRAP.anchor_rel pre)
  (r : AR.ref t pre anc)
  (v : t)
: duplicable (AR.snapshot r v) = {
  // TODO: implement in AR module, or tweak
  // take_snapshot to provide a snapshot of a possibly
  // "older" value. In that case this is easy to implement.
  dup_f = admit();
}

```pulse
ghost
fn rec all_tasks_done_inst (#code:vcode) (t : task_t code) (ts : list (task_t code))
  requires all_tasks_done ts ** pure (List.memP t ts)
  ensures  all_tasks_done ts ** task_done t
  decreases ts
{
  match ts {
    Nil -> {
      unreachable();
    }
    Cons t' ts' -> {
      let b = SEM.strong_excluded_middle (t == t');
      if b {
        rewrite each t' as t;
        let st = unfold_all_tasks_done_cons #code t ts';
        dup (AR.snapshot t.h.g_state st) ();
        fold (handle_done t.h);
        fold (task_done t);
        fold_all_tasks_done_cons #code t ts' st;
      } else {
        let st = unfold_all_tasks_done_cons #code t' ts';
        all_tasks_done_inst #code t ts';
        fold_all_tasks_done_cons #code t' ts' st;
      }
    }
  }
}
```

let pool_done (#code:vcode) (p : pool code) : vprop =
  exists* ts. BAR.pts_to_full p.g_runnable #p14 ts ** all_state_pred ts ** all_tasks_done ts

```pulse
ghost
fn disown_aux
  (#code:vcode) (#p:pool code)
  (#post : erased code.t)
  (h : handle)
  requires pool_done p ** big_joinable p post h
  ensures  pool_done p ** code.up post
{
  unfold (pool_done p);
  unfold (big_joinable p post h);
  unfold (big_handle_spotted p post h);

  with v_runnable. assert (BAR.pts_to_full p.g_runnable #p14 v_runnable);
  with t. assert (big_task_spotted p t);

  recall_task_spotted #code p t #v_runnable;
  extract_state_pred p t #v_runnable;

  unfold (state_pred t.pre t.post t.h);

  with st. assert (AR.pts_to t.h.g_state st);
  let st = reveal st;
  
  all_tasks_done_inst t v_runnable;

  match st {
    Done -> {
      rewrite (state_res t.pre t.post t.h.g_state Done)
           as code.up post;

      AR.lift_anchor t.h.g_state Ready;
      AR.write_full t.h.g_state Claimed;
      AR.drop_anchor t.h.g_state;

      fold (state_res t.pre t.post t.h.g_state Claimed);
      
      rewrite (pts_to t.h.state Done)
           as (pts_to t.h.state (unclaimed Claimed));
      
      intro_state_pred t.pre t.post t.h Claimed;

      drop_ (big_task_spotted p t);
      
      rewrite emp as invlist_v invlist_empty;
      elim_trade_ghost _ _;
      rewrite invlist_v invlist_empty as emp;
      
      drop_ (task_done t);
      
      fold (pool_done p);
    }
    Claimed -> {
      assert (AR.anchored h.g_state Ready);
      AR.recall_anchor t.h.g_state Ready;
      unreachable();
    }
    Ready -> {
      unfold (task_done t);
      unfold (handle_done t.h);
      with st. assert (AR.snapshot t.h.g_state st);
      AR.recall_snapshot t.h.g_state;
      unreachable();
    }
    Running -> { 
      unfold (task_done t);
      unfold (handle_done t.h);
      with st. assert (AR.snapshot t.h.g_state st);
      AR.recall_snapshot t.h.g_state;
      unreachable();
    }
  }
}
```

```pulse
ghost
fn __big_disown_aux
  (#code:vcode) (#p:pool code)
  (#post : erased code.t)
  (h : handle)
  (_:unit)
  requires invlist_v invlist_empty ** (pool_done p ** big_joinable p post h)
  ensures  invlist_v invlist_empty ** (pool_done p ** code.up post)
{
  disown_aux #code #p #post h;
}
```

```pulse
ghost
fn __big_disown (#code:vcode) (#p:pool code)
      (#post : erased code.t)
      (h : handle)
  requires big_joinable p post h
  ensures  pledge [] (pool_done p) (code.up post)
{
  make_pledge [] (pool_done p) (code.up post) (big_joinable p post h)
      (__big_disown_aux #code #p #post h)
}
```

```pulse
ghost
fn __disown_aux
  (#code:vcode) (#p:pool code)
  (#post : erased code.t)
  (h : handle)
  (_:unit)
  requires invlist_v (pool_invlist p) ** (pool_done p ** joinable p post h)
  ensures  invlist_v (pool_invlist p) ** (pool_done p ** code.up post)
{
  // Need the emp!!!
  rewrite invlist_v (pool_invlist p)
       as (small_handle_list_inv p.g_runnable p.small_handle_list ** emp);

  ghost_joinable_s2l p post h;
  disown_aux #code #p #post h;
  rewrite (small_handle_list_inv p.g_runnable p.small_handle_list ** emp)
       as invlist_v (pool_invlist p);
}
```

```pulse
ghost
fn __disown (#code:vcode) (#p:pool code)
      (#post : erased code.t)
      (h : handle)
  requires joinable p post h
  ensures  pledge (pool_invlist p) (pool_done p) (code.up post) // could be small pledge
{
  make_pledge _ (pool_done p) (code.up post) (joinable p post h)
      (__disown_aux #code #p #post h)
}
```

```pulse
fn __big_spawn_ (#code:vcode) (p:pool code)
    (#pf:perm)
    (#pre : erased code.t)
    (#post : erased code.t)
    (f : unit -> stt unit (code.up pre) (fun _ -> (code.up post)))
    requires pool_alive #pf p ** (code.up pre)
    ensures  pool_alive #pf p ** pledge [] (pool_done p) (code.up post)
{
  let h = __big_spawn p f;
  __big_disown #code h // FIXME: crash without the #code annotation
}
```

```pulse
fn __spawn_ (#code:vcode) (p:pool code)
    (#pf:perm)
    (#pre : erased code.t)
    (#post : erased code.t)
    (f : unit -> stt unit (code.up pre) (fun _ -> (code.up post)))
    requires pool_alive #pf p ** (code.up pre)
    ensures  pool_alive #pf p ** pledge (pool_invlist p) (pool_done p) (code.up post)
{
  let h = __spawn p f;
  __disown #code h // FIXME: crash without the #code annotation
}
```

```pulse
ghost
fn rec __pool_done_task_done_aux (#code:vcode)
      (t : task_t code)
      (ts : list (task_t code))
  requires all_tasks_done ts ** pure (List.memP t ts)
  ensures  all_tasks_done ts ** task_done t
  decreases ts
{
  match ts {
    Nil -> {
      unreachable();
    }
    Cons t' ts' -> {
      let b = SEM.strong_excluded_middle (t == t');
      if b {
        rewrite each t' as t;
        let st = unfold_all_tasks_done_cons #code t ts';
        dup (AR.snapshot t.h.g_state st) ();
        fold (handle_done t.h);
        fold (task_done t);
        
        fold_all_tasks_done_cons #code t ts' st;
      } else {
        (* Must be in the tail *)
        assert (pure (List.memP t ts'));
        let st = unfold_all_tasks_done_cons #code t' ts';
        __pool_done_task_done_aux #code t ts';
        fold_all_tasks_done_cons #code t' ts' st;
      }
    }
  }
}
```

```pulse
ghost
fn __pool_done_handle_done_aux2 (#code:vcode) (#p:pool code)
      (#post : erased code.t)
      (h : handle)
      (ts : list (task_t code))
  requires BAR.pts_to_full p.g_runnable #p14 ts ** all_tasks_done ts ** big_handle_spotted p post h
  ensures  BAR.pts_to_full p.g_runnable #p14 ts ** all_tasks_done ts ** handle_done h
{
  let t = recall_handle_spotted #code p post h #ts;
  __pool_done_task_done_aux #code t ts;
  unfold (task_done t);
  rewrite each t.h as h;
  drop_ (big_handle_spotted p post h);
}
```

```pulse
ghost
fn __pool_done_handle_done (#code:vcode) (#p:pool code)
      (#post : erased code.t)
      (h : handle)
      (_ : unit)
  requires emp ** (pool_done p ** big_handle_spotted p post h)
  ensures  emp ** (pool_done p ** handle_done h)
{
  unfold (pool_done p);
  __pool_done_handle_done_aux2 #code #p #post h _;
  fold (pool_done p);
}
```

```pulse
ghost
fn pool_done_handle_done (#code:vcode) (#p:pool code)
      (#post : erased code.t)
      (h : handle)
  requires big_handle_spotted p post h
  ensures pledge [] (pool_done p) (handle_done h)
{
  make_pledge [] (pool_done p) (handle_done h) (big_handle_spotted p post h)
    (__pool_done_handle_done #code #p #post h)
}
```

let vopt (#a:Type) ([@@@equate_by_smt]o : option a) (p : a -> vprop) =
  match o with
  | Some x -> p x
  | None -> emp

```pulse
ghost
fn intro_vopt_none (#a:Type u#2) (#p : a -> vprop) ()
  requires emp
  ensures vopt None p
{
  fold (vopt None p);
}
```

```pulse
ghost
fn intro_vopt_some (#a:Type u#2) (x : a) (#p : a -> vprop)
  requires p x
  ensures vopt (Some x) p
{
  fold (vopt (Some x) p);
}
```

```pulse
ghost
fn get_vopt (#a:Type u#2) (#x : a) (#p : a -> vprop) ()
  requires vopt (Some x) p
  ensures p x
{
  unfold vopt (Some x) p;
}
```

```pulse
ghost
fn weaken_vopt (#a:Type u#2) (o : option a)
    (#p1 #p2 : a -> vprop)
    (extra : vprop) // CAUTION: this can be dropped!
    (f : (x:a) -> stt_ghost unit (extra ** p1 x) (fun _ -> p2 x))
  requires extra ** vopt o p1
  ensures  vopt o p2
{
  match o {
    None -> {
      unfold (vopt None p1);
      fold (vopt None p2);
      drop_ extra;
      ()
    }
    Some v -> {
      rewrite (vopt o p1) as p1 v;
      f v;
      fold (vopt o p2);
    }
  }
}
``` 

```pulse
(* Called with pool lock taken *)
fn rec grab_work'' (#code:vcode) (p:pool code) (v_runnable : list (task_t code))
  requires all_state_pred v_runnable
  returns  topt : option (task_t code)
  ensures  all_state_pred v_runnable
        ** vopt topt (fun t ->
             code.up t.pre ** pts_to t.h.state #(half_perm full_perm) Running ** pure (List.memP t v_runnable))
{
  match v_runnable {
    Nil -> {
      // intro_vopt_none;
      // fails with variable not found...

      let topt : option (task_t code) = None #(task_t code);
      (* Funnily enough whatever we put in the vopt predicate
      works here, since it trigger the unifier+SMT for the matcher,
      which works since we have a None. *)
      rewrite emp
          //  as vopt topt (fun t -> emp);
          as vopt topt (fun t -> code.up t.pre ** pts_to t.h.state #(half_perm full_perm) Running ** pure (List.memP t v_runnable));
      topt
    }
    Cons t ts -> {
      take_one_h11 t ts;
      unfold (state_pred t.pre t.post t.h);
      
      let st = !t.h.state;
      match st {
        Ready -> {
          let topt = Some #(task_t code) t;
          rewrite (emp ** state_res t.pre t.post t.h.g_state Ready)
               as (state_res t.pre t.post t.h.g_state Running ** code.up t.pre);

          t.h.state := Running;
          AR.write t.h.g_state Running;
          
          share2 t.h.state;

          intro_state_pred_Running t.pre t.post t.h;
          add_one_state_pred t ts;

          rewrite code.up t.pre ** pts_to t.h.state #(half_perm full_perm) Running ** pure (List.memP t v_runnable)
               as vopt topt (fun t -> code.up t.pre ** pts_to t.h.state #(half_perm full_perm) Running ** pure (List.memP t v_runnable));
          
          topt
        }
        _ -> {
          fold (state_pred t.pre t.post t.h);
          let topt = grab_work'' #code p ts;
          add_one_state_pred t ts;
          
          (* Weaken the pure inside the vopt *)
          ghost fn weaken (t : task_t code)
            requires emp ** (code.up t.pre ** pts_to t.h.state #(half_perm full_perm) Running ** pure (List.memP t ts))
            ensures  code.up t.pre ** pts_to t.h.state #(half_perm full_perm) Running ** pure (List.memP t v_runnable)
          {
            ()
          };
          weaken_vopt topt emp weaken;

          topt
        }
      }
    }
  }
}
```


```pulse
(* Called with pool lock taken *)
fn rec grab_work' (#code:vcode) (p:pool code)
  requires lock_inv p.runnable p.g_runnable
  returns  topt : option (task_t code)
  ensures  lock_inv p.runnable p.g_runnable
        ** vopt topt (fun t ->
             code.up t.pre ** pts_to t.h.state #(half_perm full_perm) Running ** big_task_spotted p t)
{
  unfold (lock_inv p.runnable p.g_runnable);
  let v_runnable = Big.op_Bang p.runnable;
  let topt = grab_work'' #code p v_runnable;

  BAR.take_snapshot' p.g_runnable;

  (* If Some, the task is spotted *)
  ghost fn spot (t:task_t code)
    requires BAR.snapshot p.g_runnable v_runnable ** (code.up t.pre ** pts_to t.h.state #(half_perm full_perm) Running ** pure (List.memP t v_runnable))
    ensures  code.up t.pre ** pts_to t.h.state #(half_perm full_perm) Running ** big_task_spotted p t
  {
    intro_big_task_spotted #code p t v_runnable;
  };
  weaken_vopt topt (BAR.snapshot p.g_runnable v_runnable) spot;

  fold (lock_inv p.runnable p.g_runnable);
  topt
}
```

```pulse
fn grab_work (#code:vcode) (p:pool code)
  requires pool_alive #f p
  returns  topt : option (task_t code)
  ensures  pool_alive #f p
        ** vopt topt (fun t ->
             code.up t.pre ** pts_to t.h.state #(half_perm full_perm) Running ** big_task_spotted p t)
{
  unfold (pool_alive #f p);
  acquire p.lk;
  let res = grab_work' #code p;
  release p.lk;
  fold (pool_alive #f p);
  res
}
```

```pulse
fn perf_work (#code:vcode) (t : task_t code)
  requires code.up t.pre
  returns  _:unit
  ensures  code.up t.post
{
  let f = t.thunk;
  f ()
}
```

```pulse
fn put_back_result (#code:vcode) (p:pool code) (t : task_t code)
  requires pool_alive #f p **
           big_task_spotted p t **
           code.up t.post **
           pts_to t.h.state #(half_perm full_perm) Running
  ensures  pool_alive #f p
{
  acquire p.lk;
  unfold (lock_inv p.runnable p.g_runnable);
  recall_task_spotted p t;
  extract_state_pred p t;

  (* Advance the state and place the post condition back into the pool *)
  assert (state_pred t.pre t.post t.h ** pts_to t.h.state #(half_perm full_perm) Running);
    unfold (state_pred t.pre t.post t.h);
    with v_st. assert (AR.pts_to t.h.g_state v_st);
    pts_to_injective_eq t.h.state;
    assert (pure (v_st == Running));
    rewrite (pts_to t.h.state #(if Running? v_st then half_perm full_perm else full_perm) (unclaimed v_st))
         as (pts_to t.h.state #(half_perm full_perm) v_st);
    gather2 t.h.state;
    t.h.state := Done; // Only concrete step (except for mutex taking)
    AR.write t.h.g_state Done;

    rewrite (state_res t.pre t.post t.h.g_state Running) as emp;
    rewrite code.up t.post as (state_res t.pre t.post t.h.g_state Done);

    intro_state_pred t.pre t.post t.h Done;
  assert (state_pred t.pre t.post t.h);

  (* Restore full pool invariant with trade. *)
  elim_trade _ _;

  fold (lock_inv p.runnable p.g_runnable);
  release p.lk;
  drop_ (big_task_spotted p t);
}
```

```pulse
fn rec worker (#code:vcode) (#f:perm) (p : pool code)
  requires pool_alive #f p
  ensures  pool_alive #f p
{
  let topt = grab_work p;
  match topt {
    None -> {
      rewrite (if Some? topt then code.up (Some?.v topt).pre else emp)
           as emp;
      worker p
    }
    Some t -> {
      rewrite each topt as Some t;
      get_vopt #(task_t code) #t ();
      (* sigh *)
      rewrite (fun t -> code.up t.pre ** pts_to t.h.state #(half_perm full_perm) Running ** big_task_spotted p t) t
           as code.up t.pre ** pts_to t.h.state #(half_perm full_perm) Running ** big_task_spotted p t;
      perf_work t;
      put_back_result p t;
      worker p
    }
  }
}
```

let ite (b:bool) (p q : vprop) : vprop =
  if b then p else q

```pulse
fn rec check_if_all_done
  (#code:vcode)
  (ts : list (task_t code))
  requires all_state_pred ts
  returns  b : bool
  ensures  all_state_pred ts ** ite b (all_tasks_done ts) emp
{
  match ts {
    Nil -> {
      rewrite emp as (all_tasks_done ts);
      fold (ite true (all_tasks_done ts) emp);
      true;
    }
    Cons t ts' -> {
      take_one_h11 t ts';
      unfold (state_pred t.pre t.post t.h);
      let st = !t.h.state;
      match st {
        Done -> {
          let bb = check_if_all_done ts';
          if bb {
            rewrite (ite bb (all_tasks_done ts') emp) as (all_tasks_done ts');
            with g_st. assert (AR.pts_to t.h.g_state g_st);
            assert (pure (g_st == Done \/ g_st == Claimed));
            AR.take_snapshot t.h.g_state;
            fold_all_tasks_done_cons #code t ts' g_st;
            rewrite (all_tasks_done (t::ts')) as (all_tasks_done ts);
            fold (ite true (all_tasks_done ts) emp);
            fold (state_pred t.pre t.post t.h);
            add_one_state_pred t ts';
            true;
          } else {
            drop_ (ite bb (all_tasks_done ts') emp);
            fold (state_pred t.pre t.post t.h);
            add_one_state_pred t ts';
            rewrite emp as ite false (all_tasks_done ts) emp;
            false;
          }
        }
        Running -> {
          fold (state_pred t.pre t.post t.h);
          add_one_state_pred t ts';
          rewrite emp as ite false (all_tasks_done ts) emp;
          false;
        }
        Ready -> {
          fold (state_pred t.pre t.post t.h);
          add_one_state_pred t ts';
          rewrite emp as ite false (all_tasks_done ts) emp;
          false;
        }
        Claimed -> {
          unreachable();
        }
      }
    }
  }
}
```

```pulse
fn try_await_pool
  (#code:vcode)
  (p:pool code) (#f:perm) (q : vprop)
  requires pool_alive #f p ** pledge (pool_invlist p) (pool_done p) q
  returns  b : bool
  ensures  pool_alive #f p ** ite b q (pledge (pool_invlist p) (pool_done p) q)
{
  unfold (pool_alive #f p);
  let lk = p.lk;
  acquire lk;
  unfold (lock_inv p.runnable p.g_runnable);

  let runnable = Big.op_Bang p.runnable;
  let done = check_if_all_done #code runnable;
  if done {
    rewrite each done as true;
    rewrite (ite true (all_tasks_done runnable) emp)
         as all_tasks_done runnable;

    (* We have permission on the queues + all_tasks_done. Obtain pool_done
    temporarilly to redeem. *)
    BAR.share4' p.g_runnable;
    fold (pool_done p);
    redeem_pledge _ _ _;
    (*!*) assert q;
    unfold (pool_done p);
    BAR.gather4' p.g_runnable;

    fold (ite true q (pledge [] (pool_done p) q));
    fold (lock_inv p.runnable p.g_runnable);
    release lk;
    fold (pool_alive #f p);

    drop_ (all_tasks_done runnable);

    true
  } else {
    rewrite each done as false;
    rewrite (ite false (all_tasks_done runnable) emp)
         as emp;
    fold (lock_inv p.runnable p.g_runnable);
    release lk;
    fold (pool_alive #f p);

    fold (ite false q (pledge (pool_invlist p) (pool_done p) q));
    false
  }
}
```

```pulse
fn __await_pool
  (#code:vcode)
  (p:pool code) (#f:perm) (q : vprop)
  requires pool_alive #f p ** pledge (pool_invlist p) (pool_done p) q
  ensures  pool_alive #f p ** q
{
  let mut done = false;
  fold (ite false q (pledge (pool_invlist p) (pool_done p) q));
  while (let v = !done; not v)
    invariant b.
      exists* v_done.
        pool_alive #f p **
        pts_to done v_done **
        ite v_done q (pledge (pool_invlist p) (pool_done p) q) **
        pure (b == not v_done)
  {
    with v_done. assert (pts_to done v_done);
    rewrite each v_done as false;
    unfold (ite false q (pledge (pool_invlist p) (pool_done p) q));
    let b = try_await_pool #code p #f q;
    done := b;
  };
  with v_done. assert (pts_to done v_done);
  rewrite each v_done as true;
  unfold (ite true q (pledge (pool_invlist p) (pool_done p) q));
}
```

```pulse
fn rec __teardown_pool
  (#code:vcode)
  (p:pool code) (#f:perm)
  requires pool_alive #f p
  ensures  pool_done p
{
  unfold (pool_alive #f p);
  let lk = p.lk;
  acquire lk;
  unfold (lock_inv p.runnable p.g_runnable);

  let runnable = Big.op_Bang p.runnable;
  let b = check_if_all_done #code runnable;
  if b {
    rewrite ite b (all_tasks_done runnable) emp
         as all_tasks_done runnable;
    BAR.share4' p.g_runnable;
    fold (pool_done p);

    (* Drop the other ghost half. *)
    drop_ (BAR.pts_to_full p.g_runnable #p14 runnable);

    (* TODO: actually teardown. *)
    drop_ (Big.pts_to p.runnable runnable);
    drop_ (lock_alive #_ #(half_perm f) p.lk);
  } else {
    rewrite ite b (all_tasks_done runnable) emp
         as emp;
    (* Spin *)
    fold (lock_inv p.runnable p.g_runnable);
    release lk;
    fold (pool_alive #f p);
    __teardown_pool p;
  }
}
```

assume
val share_lock
  (#p:vprop)
  (#[exact (`full_perm)] f : perm)
  (l : lock p)
  : stt_ghost unit (lock_alive #p #f l)
                   (fun _ -> lock_alive #p #(half_perm f) l ** lock_alive #p #(half_perm f) l)

```pulse
ghost
fn share
  (#code:vcode)
  (p : pool code)
  (#f:perm)
  requires pool_alive #f p
  ensures  pool_alive #(half_perm f) p ** pool_alive #(half_perm f) p
{
  unfold (pool_alive #f p);
  share_lock #_ #(half_perm f) p.lk;
  fold (pool_alive #(half_perm f) p);
  fold (pool_alive #(half_perm f) p);
}
```

(* Very basic model of a thread fork *)
assume
val fork
  (#p #q : vprop)
  (f : unit -> stt unit p (fun _ -> q))
  : stt unit p (fun _ -> emp)

```pulse
fn spawn_worker
  (#code:vcode)
  (p:pool code)
  (#f:perm)
  requires pool_alive #f p
  ensures  emp
{
  fork (fun () -> worker #code #f p)
}
```

```pulse
fn rec spawn_workers
  (#code:vcode)
  (p:pool code) (#f:perm)
  (n:pos)
  requires pool_alive #f p
  ensures  emp
{
  if (n = 1) {
    spawn_worker p;
  } else {
    share #code p #f;
    spawn_worker p;
    spawn_workers p #(half_perm f) (n - 1);
  }
}
```

```pulse
fn __setup_pool
  (#code:vcode)
  (n : pos)
  requires emp
  returns p : pool code
  ensures pool_alive p
{
  let runnable = Big.alloc ([] <: list (task_t code));
  assert (pure (list_preorder #(task_t code) [] [] /\ True));
  let g_runnable = BAR.alloc #(list (task_t code)) [] #list_preorder #list_anchor;
  assert (pure (list_preorder #handle [] [] /\ True));
  let small_handle_list = AR.alloc #(list (handle)) [] #list_preorder #list_anchor;
  rewrite emp as (all_state_pred #code []);
  
  BAR.share2' g_runnable;
  fold (lock_inv runnable g_runnable);
  
  rewrite emp as (handles_one_to_one #code [] []);
  fold (small_handle_list_inv g_runnable small_handle_list);
  let i = new_invariant (small_handle_list_inv g_runnable small_handle_list);
  
  let lk = new_lock (lock_inv runnable g_runnable);
  let p = {runnable; g_runnable; small_handle_list; i; lk};
  assume_ (lock_alive p.lk); // To be obtained from new lock module, plus a share call
  share_lock #_ #full_perm p.lk;
  fold (pool_alive p);
  fold (pool_alive p);

  spawn_workers #code p #full_perm n;

  p
}
```

let small_handle_spotted (#code:vcode) (p:pool code) (post:erased code.t) (h : handle)
  : Lemma (is_small (handle_spotted p post h)) =
    let aux (small_handle_list : list handle)
      : Lemma (is_small (AR.snapshot p.small_handle_list small_handle_list ** pure (List.memP h small_handle_list)))
      =
      assume (is_small (AR.snapshot p.small_handle_list small_handle_list)); // FIXME
      pure_is_small (List.memP h small_handle_list);
      small_star (AR.snapshot p.small_handle_list small_handle_list) (pure (List.memP h small_handle_list))
    in
    Classical.forall_intro aux;
    small_exists (fun v_small_handle_list -> AR.snapshot p.small_handle_list v_small_handle_list ** pure (List.memP h v_small_handle_list));
    assert_norm
      (handle_spotted p post h ==
            op_exists_Star (fun v_small_handle_list -> AR.snapshot p.small_handle_list v_small_handle_list ** pure (List.memP h v_small_handle_list)));
    assert (is_small (handle_spotted p post h));
    ()

let joinable_is_small (#code:vcode) (p:pool code) (post:erased code.t) (h : handle)
  : Lemma (is_small (joinable p post h)) =
    assume (is_small (AR.anchored h.g_state Ready)); // FIXME
    small_handle_spotted p post h;
    small_star (AR.anchored h.g_state Ready) (handle_spotted p post h)

let big_spawn #code = __big_spawn #code
let spawn #code = __spawn #code
let big_disown = __big_disown
let disown = __disown
let big_spawn_ = __big_spawn_
let spawn_ = __spawn_
let big_try_await = __big_try_await
let big_await = __big_await
let try_await = __try_await
let await = __await
let await_pool = __await_pool
let teardown_pool = __teardown_pool
let setup_pool = __setup_pool
