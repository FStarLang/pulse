module NuPool

 // TODO: can we remove permission to the pool in await / try_await?
 // Ideally we do not lock the pool or even care much about it.

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open FStar.Tactics
open FStar.Preorder
open Pulse.Lib.Par.Pledge
open Pulse.Lib.Trade
module SmallTrade = Pulse.Lib.SmallTrade

module FRAP = Pulse.Lib.FractionalAnchoredPreorder
module AR = Pulse.Lib.AnchoredReference
open Pulse.Lib.CoreRef

open Pulse.Class.Duplicable
module R = Pulse.Lib.RSpinLock
module Big = Pulse.Lib.BigReference
module BigGhost = Pulse.Lib.BigGhostReference
module Ghost = Pulse.Lib.GhostReference

module MS = MonotonicSet

let gref = Pulse.Lib.GhostReference.ref

#set-options "--debug NuPool --debug_level SMTQuery --log_failing_queries"
// #set-options "--print_implicits"
// #set-options "--print_universes"

noeq
type vcode = {
    t : Type u#2;
    up : t -> v:vprop{is_small v};
    emp : (emp:t{up emp == Pulse.Lib.Core.emp});
}

type task_state =
  | Ready
  | Running
  | Done
  | Claimed
  
let v (s : task_state) : int =
  match s with
  | Ready -> 0
  | Running -> 1
  | Done -> 2
  | Claimed -> 3
  
let p_st : preorder task_state = fun x y -> b2t (v x <= v y)

let anchor_rel : FRAP.anchor_rel p_st =
  fun x y ->
    match x, y with
    | Ready, Claimed -> false
    | x, y -> squash (p_st x y)

let anchor_rel_refl (x:task_state) : Lemma (anchor_rel x x) [SMTPat (anchor_rel x x)] =
  assert_norm (anchor_rel Ready Ready);
  assert_norm (anchor_rel Running Running);
  assert_norm (anchor_rel Done Done);
  assert_norm (anchor_rel Claimed Claimed)

unfold let p12 : perm = half_perm full_perm

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
type task_handle : Type u#0 = {
  state   : ref task_state;
  g_state : AR.ref task_state p_st anchor_rel; (* these two refs are kept in sync *)
}

assume val task_handle_eq (h1 h2 : task_handle) : b:bool{b <==> h1 == h2}

noeq
type task_t (code : vcode) : Type u#2 = {
  h : task_handle;

  pre :  erased code.t;
  post : erased code.t;
  thunk : unit -> stt unit (code.up pre) (fun _ -> code.up post);

  // lk : lock (exists* v_state.
  //   pts_to h.state v_state **
  //   AR.pts_to h.g_state v_state **
  //   state_res pre post h.g_state v_state);

  (* Does this task have a handle?
  If so, after executing the task, set to Done and release lock.
  If not, it's disowned, and the worker who executes it will free it. *)
  // owned : ref bool;
}

// let state_live #code (t : task_t code) =
//   exists* (v_state : task_state).
//     pts_to t.state v_state **
//     AR.pts_to t.g_state v_state ** 
//     state_res t v_state

// let rec all_live #code (v_runnable : list (task_t code)) =
//   match v_runnable with
//   | [] -> emp
//   | r :: rs ->
//     exists* (v_task : task_t code).
//       Big.pts_to r #p12 v_task ** (* state_live v_task ** *) all_live rs

// let __growing_list (#a:Type) (l1 l2 : list a) : prop =
//   exists (l : list a). l @ l1 == l2
  
// let growing_list (#a:Type) : preorder (list a) =
//   admit(); __growing_list
  
let list_extension #a (t0 t1 : list a)
  : prop
  = Cons? t1 /\ t0 == List.Tot.tail t1
 
let list_preorder #a
  : FStar.Preorder.preorder (list a)
  = FStar.ReflexiveTransitiveClosure.closure list_extension

let list_anchor : FRAP.anchor_rel list_preorder = fun x y -> list_preorder x y /\ True

let state_pred
  (#code:vcode)
  ([@@@equate_by_smt]pre : code.t)
  ([@@@equate_by_smt]post : code.t)
  (h : task_handle)
: vprop =
  exists* (v_state : task_state).
    pts_to h.state v_state **
    AR.pts_to h.g_state v_state **
    state_res pre post h.g_state v_state

// equate_by_smt due to #22
let rec handles_one_to_one
  (#code:vcode)
  ([@@@equate_by_smt] v_runnable : list (task_t code))
  ([@@@equate_by_smt] v_handles : list task_handle)
: vprop
= match v_runnable, v_handles with
  | [], [] -> emp
  | r :: rs, h :: hs ->
    pure (r.h == h) **
    state_pred r.pre r.post h **
    handles_one_to_one rs hs
  | _, _ -> pure False

```pulse
ghost
fn add_one_h11 (#code:vcode)
  (t : task_t code) (h : task_handle)
  (v_runnable : list (task_t code)) (v_handles : list task_handle)
  requires pure (t.h == h) ** state_pred t.pre t.post h ** handles_one_to_one v_runnable v_handles
  returns _:unit
  ensures  handles_one_to_one (t :: v_runnable) (h :: v_handles)
{
  fold (handles_one_to_one (t :: v_runnable) (h :: v_handles));
}
```

```pulse
ghost
fn take_one_h11 (#code:vcode)
  (t : task_t code) (h : task_handle)
  (v_runnable : list (task_t code)) (v_handles : list task_handle)
  requires handles_one_to_one (t :: v_runnable) (h :: v_handles)
  returns _:unit
  ensures  pure (t.h == h) ** state_pred t.pre t.post h ** handles_one_to_one v_runnable v_handles
{
  unfold (handles_one_to_one (t :: v_runnable) (h :: v_handles));
}
```

let rec state_res_forall
  (#code:vcode) (v_runnable : list (task_t code))
: vprop
= match v_runnable with
  | [] -> emp
  | r :: rs ->
    state_pred r.pre r.post r.h **
    state_res_forall rs

let lock_inv (#code:vcode)
  (runnable   : Big.ref (list (task_t code)))
  (g_runnable : BigGhost.ref (list (task_t code)))
  (handles : AR.ref (list task_handle) list_preorder list_anchor)
: vprop
= 
  exists*
    (v_runnable : list (task_t code))
    (v_handles : list task_handle)
  .
    Big.pts_to      runnable v_runnable **
    BigGhost.pts_to g_runnable v_runnable **
    AR.pts_to_full handles v_handles **
    handles_one_to_one v_runnable v_handles ** 
    state_res_forall v_runnable

noeq
type pool_st (code:vcode) : Type u#0 = {
  runnable   : Big.ref  (list (task_t code));
  g_runnable : BigGhost.ref (list (task_t code));

  handles    : AR.ref (list task_handle) list_preorder list_anchor;

  lk : lock (lock_inv runnable g_runnable handles);
}

assume val lock_alive
  (#p:vprop)
  (#[exact (`full_perm)] f : perm)
  (l : lock p)
  : (v:vprop{is_small v})

type pool (code:vcode) = pool_st code

let pool_alive (#[exact (`full_perm)] f : perm) (#code:vcode) (p:pool code) : vprop =
  lock_alive #_ #f p.lk

type handle = task_handle

let state_res' #code (post : erased code.t) ([@@@equate_by_smt] st : task_state) =
  match st with
  | Done -> code.up post
  | Claimed -> emp
  | _ -> pure False

let snapshot_mem (#code:vcode) (p : pool code) (h : handle) : vprop =
  exists* v_handles.
    AR.snapshot p.handles v_handles **
    pure (List.memP h v_handles)

let mem_lemma (#a:Type) (x:a) (l1 l2:list a)
: Lemma (requires List.memP x l1 /\ list_preorder l1 l2)
        (ensures List.memP x l2)
= admit()

```pulse
ghost
fn recall_snapshot_mem
  (#code:vcode) (p : pool code) (h : handle) (#hs : list handle)
  requires AR.pts_to p.handles hs ** snapshot_mem p h
  ensures  AR.pts_to p.handles hs ** snapshot_mem p h ** pure (List.memP h hs)
{
  unfold (snapshot_mem p h);
  with hs0. assert (AR.snapshot p.handles hs0);
  AR.recall_snapshot p.handles;
  assert (pure (list_preorder hs0 hs /\ True));
  fold (snapshot_mem p h);
  mem_lemma h hs0 hs;
  ();
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

```pulse
ghost // or concrete?
fn extract_state_res
  (#code:vcode) (p : pool code) (h : handle) (#ts : list (task_t code)) (#hs : list handle)
  requires handles_one_to_one ts hs
        ** state_res_forall ts
        ** pure (List.memP h hs)
  returns et : erased (task_t code)
  ensures  handles_one_to_one ts hs
        ** pure (et.h == h)
        ** state_pred et.pre et.post h
        ** trade (state_pred et.pre et.post h) (state_res_forall ts) // wand to put things back together
{
  match hs {
    Nil -> { unreachable () }
    Cons h' hs' -> {
      if task_handle_eq h h' {
        admit();
      } else {
        match ts {
          Nil -> {
            rewrite (handles_one_to_one ts hs) as pure False;
            unreachable ()
          }
          Cons t' ts' -> {
            take_one_h11 t' h' ts' hs';

            assert (pure (t'.h == h'));
            rewrite each t'.h as h';
            // rewrite each ts as (t'::ts');
            rewrite (state_res_forall (t'::ts'))
                 as (state_pred t'.pre t'.post t'.h ** state_res_forall ts');
            star_to_trade (state_pred t'.pre t'.post t'.h) (state_res_forall ts');
            rewrite (state_pred t'.pre t'.post t'.h) as state_pred t'.pre t'.post t'.h;
            assert (state_pred t'.pre t'.post t'.h);

            add_one_h11 t' h' ts' hs'; (* fold back *)

            hide t'
          }
        }
      }
    }
  }
}
```

```pulse
ghost
fn intro_snapshot_mem
    (#code:vcode) (p : pool code) (h : handle)
    (v_handles : list handle)
  requires AR.snapshot p.handles v_handles ** pure (List.memP h v_handles)
  ensures  snapshot_mem p h
{
  fold (snapshot_mem p h);
}
```

let joinable (#code:vcode) (p : pool code) ([@@@equate_by_smt]post:erased code.t) (h : handle) : vprop =
  AR.anchored h.g_state Ready **
  snapshot_mem p h

```pulse
ghost
fn setup_task_eliminator0
  (#code:vcode)
  (post:erased code.t)
  (r : AR.ref task_state p_st anchor_rel)
  (_:unit)
  (* invlist_v [] needed to make the trade introduction below work... *)
  requires Pulse.Lib.InvList.invlist_v [] **
           AR.anchored r Ready **
           (exists* (s : task_state). AR.pts_to r s ** state_res' post s)
  ensures  Pulse.Lib.InvList.invlist_v [] **
           code.up post
{
  with s. assert (AR.pts_to r s);
  let ss = reveal s;
  (* Important! We match on the reveal of the existentially
  quantified s, not on the result of reading the reference, which
  could be "ahead". *)
  match ss {
    Ready -> {
      rewrite (state_res' post s) as pure False;
      unreachable ();
    }
    Running -> {
      rewrite (state_res' post s) as pure False;
      unreachable ();
    }
    Done -> { 
      rewrite (state_res' post s) as code.up post;
      drop_ (AR.anchored r Ready);
      drop_ (AR.pts_to r Done);
      ()
    }
    Claimed -> {
      assert (AR.pts_to r Claimed);
      assert (AR.anchored r Ready);
      AR.recall_anchor r Ready;
      unreachable ();
    }
  }
}
```

#set-options "--split_queries always"

```pulse
ghost
fn setup_task_eliminator (#code:vcode) (post:erased code.t) (r : AR.ref task_state p_st anchor_rel)
  requires AR.anchored r Ready
  ensures  emp // task_eliminator post r
{
  SmallTrade.intro_trade #[] (exists* (s : task_state).
     AR.pts_to r s ** state_res' post s
   ) (code.up post) (AR.anchored r Ready) (setup_task_eliminator0 #code post r);
  admit();
  // fold (task_eliminator post r);
}
```

```pulse
ghost
fn push_handle (#a:Type) (x:a) (r : AR.ref (list a) list_preorder list_anchor) (#xs:erased (list a))
  requires AR.pts_to_full r xs
  ensures  AR.pts_to_full r (x::xs)
{
  AR.write_full r (x::xs);
}
```

```pulse
fn spawn' (code:vcode) (p:pool code)
    (#pf:perm)
    (#pre : code.t)
    (#post : code.t)
    (f : unit -> stt unit (code.up pre) (fun _ -> (code.up post)))
    requires pool_alive #pf p ** (code.up pre)
    returns  h : handle
    ensures  pool_alive #pf p ** joinable #code p post h
{
  let task_st = Ready;
  assert (pure (anchor_rel Ready Ready));
  let r_task_st : ref task_state = alloc task_st;
  let gr_task_st : AR.ref task_state p_st anchor_rel = AR.alloc #task_state task_st #p_st #anchor_rel;
  
  AR.drop_anchor gr_task_st;
  
  let handle : task_handle = {
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
  acquire lk;
  unfold (lock_inv p.runnable p.g_runnable p.handles);
  
  let v_runnable = Big.op_Bang p.runnable;
  Big.op_Colon_Equals p.runnable (task :: v_runnable);
  BigGhost.op_Colon_Equals p.g_runnable (task :: v_runnable);
  with v_handles. assert (AR.pts_to_full p.handles v_handles);

  push_handle handle p.handles;
  assert (Big.pts_to p.runnable (task :: v_runnable));
  
  rewrite each task_st as Ready;
  
  rewrite each gr_task_st as task.h.g_state;
  assert (AR.anchored task.h.g_state Ready);

  with v_handles'. assert (AR.pts_to_full p.handles v_handles');
  AR.take_snapshot' p.handles;
  
  assert (pure (List.memP handle v_handles'));
  intro_snapshot_mem p task.h v_handles';

  assert (snapshot_mem p task.h);

  fold (joinable #code p post task.h);
  
  fold (pool_alive #pf p);

  rewrite (code.up pre)
       as (state_res pre post gr_task_st Ready);
  rewrite each r_task_st as handle.state;
  rewrite each gr_task_st as handle.g_state;
  rewrite each handle as task.h;
  rewrite each pre as task.pre;
  rewrite each post as task.post;
  fold (state_pred task.pre task.post task.h);

  add_one_h11 task task.h v_runnable v_handles;
  
  assert  (Big.pts_to      p.runnable (task :: v_runnable));
  assert  (BigGhost.pts_to p.g_runnable (task :: v_runnable));
  assert  (AR.pts_to_full p.handles (handle :: v_handles));
  assert  (handles_one_to_one (task :: v_runnable) (handle :: v_handles));
  
  // FIXME: an explicit rewrite of the above 4 vprops into this
  // here fails. The fold is anyway better, but would be good to investigate.
  fold (lock_inv p.runnable p.g_runnable p.handles);

  release lk;

  task.h
}
```

```pulse
ghost
fn claim_done_task
         (#code:vcode) (#p:pool code)
         (#pre : code.t) (#post : code.t)
         (h : task_handle)
  requires state_res pre post h.g_state Done    ** AR.pts_to h.g_state Done    ** AR.anchored h.g_state Ready
  ensures  state_res pre post h.g_state Claimed ** AR.pts_to h.g_state Claimed ** code.up post
{
  unfold (state_res pre post h.g_state Done);
  rewrite
    (match Done with
    | Ready -> code.up pre
    | Running -> emp
    | Done -> code.up post
    | Claimed -> AR.anchored h.g_state Claimed)
  as
    code.up post;

  AR.lift_anchor h.g_state Ready;

  AR.write_full h.g_state Claimed;

  AR.drop_anchor h.g_state;

  rewrite (code.up post) as code.up post;

  fold (state_res pre post h.g_state Claimed);

  ()
}
```

(* Trying to await for a spawned task. Note: no preconditions about the pool
here. The task contains its own lock, and we can modify it without synchronizing
with the pool. *)
```pulse
fn try_await
         (#code:vcode) (#p:pool code)
         (#pre : code.t)
         (#post : code.t)
         (h : handle)
         (#f:perm)
  requires pool_alive #f p ** joinable p post h
  returns  ok : bool
  ensures  pool_alive #f p ** (if ok then code.up post else joinable p post h)
{
  unfold (joinable p post h);
  
  // FIXME: from pool. Also what about pre?
  assume_ (state_pred pre post h);
  unfold (state_pred pre post h);

  let task_st = !h.state;
  
  match task_st {
    Ready -> {
      (* NOOP *)
      fold (joinable p post h);
      fold (state_pred pre post h);
      drop_ (state_pred pre post h); // fixme
      false;
    }
    Running -> {
      (* NOOP *)
      fold (joinable p post h);
      fold (state_pred pre post h);
      drop_ (state_pred pre post h); // fixme
      false;
    }
    Done -> {
      h.state := Claimed;

      claim_done_task #code #p #pre #post h;

      rewrite (code.up post)
           as (if true then code.up post else joinable p post h);
           
      fold (state_pred pre post h);
      drop_ (state_pred pre post h); // fixme
      drop_ (snapshot_mem p h);
      true
    }
    Claimed -> {
      assert (pts_to h.state Claimed);
      assert (AR.pts_to h.g_state Claimed);
      assert (AR.anchored h.g_state Ready);
      AR.recall_anchor h.g_state Ready;
      unreachable ();
    }
  }
}
```

```pulse
// Busy waiting version of await
fn await (#code:vcode) (#p:pool code)
         (#pre  : code.t)
         (#post : code.t)
         (h : handle)
         (#f:perm) // TODO: remove permission on pool. If h is joinable, pool must be alive
  requires pool_alive #f p ** joinable p post h
  ensures  pool_alive #f p ** code.up post
{
  let mut done = false;
  while (let v = !done; (not v))
    invariant b.
      exists* v_done.
        pts_to done v_done **
        (if v_done then code.up post else joinable p post h) **
        pure (b == not v_done)
  {
    let b = try_await #code #p #pre #post h #f;
    done := b;
  };
}
```

// ```pulse
// ghost
// fn reedem_disowned
//          (#code:vcode) (#p:pool code)
//          (#post : code.t)
//          (t : task_t code)
//          (#f:perm) // TODO: remove permission on pool. If h is joinable, pool must be alive
//   requires pool_done p **
//            AR.anchored t.g_state Ready
//   ensures  pool_done p ** code.up post
// {
//   admit();
// }
// ```

// ```pulse
// fn disown
//          (#code:vcode) (#p:pool code)
//          (#post : code.t)
//          (h : handle p post)
//          (#f:perm) // TODO: remove permission on pool. If h is joinable, pool must be alive
//   requires pool_alive #f p ** joinable h
//   returns  _:unit
//   ensures  pool_alive #f p ** pledge [] (pool_done p) (code.up post)
// {
//   // unfold (joinable h);
//   admit();
// }
// ```

(* Trying to await for a spawned task. Note: no preconditions about the pool
here. The task contains its own lock, and we can modify it without synchronizing
with the pool. *)
```pulse
fn grab_work (#code:vcode) (p:pool code)
  requires pool_alive #f p
  returns  topt : option (post: erased (code.t) & h : handle p post)
  ensures  pool_alive #f p **
           (if Some? topt then task_alive (Some?.v topt)._2 else emp)
{
  unfold (pool_alive #f p);
  let pv = !p;
  let lk = pv.lk;
  acquire lk;
  unfold (lock_inv pv.runnable pv.g_runnable pv.disowned pv.g_disowned);

  let runnable0 = !pv.runnable;
  match runnable0 {
    Nil -> {
      fold (lock_inv pv.runnable pv.g_runnable pv.disowned pv.g_disowned);
      release lk;
      fold (pool_alive #f p);
      
      let topt = None #(post: erased (code.t) & h : handle p post);
      rewrite emp as
        (if Some? topt then task_alive (Some?.v topt)._2 else emp);
      topt
    }
    Cons t ts -> {
      let v_task = get_one_live t ts;
      
      pv.runnable := ts;
      fold (lock_inv pv.runnable pv.g_runnable pv.disowned pv.g_disowned);
      release lk;
      fold (pool_alive #f p);
      let topt = Some #(post: erased (code.t) & h : handle p post) (| v_task.post, t |);
      fold (task_alive #code #p #v_task.post t);
      
      assert (pure (Some? topt));
      assert (pure ((Some?.v topt)._1 == v_task.post ));
      assert (pure ((Some?.v topt)._2 == t));

      rewrite
        task_alive #code #p #v_task.post t
      as
        (if true then task_alive #code #p #v_task.post (Some?.v topt)._2 else emp);

      (* FIXME: This should be trivial *)
      rewrite_by 
        (if true       then task_alive #code #p #v_task.post (Some?.v topt)._2 else emp)
        (if Some? topt then task_alive #code #p #v_task.post (Some?.v topt)._2 else emp)
        tadmit
        ();

      topt
    }
  }
}
```

```pulse
fn perf_work (#code:vcode) (#p : pool code) (post : erased (code.t)) (t : handle p post)
  requires task_alive t (* ** task_ready t ? *)
  returns  _:unit
  ensures  task_alive t (* ** task_done t ? *)
{
  unfold (task_alive t);
  let tv = !t;
  let tlk = tv.lk;
  acquire tlk;
  let task_st = !tv.state;
  match task_st {
    Ready -> {
      assert (state_res tv.pre tv.post tv.g_state Ready);
      rewrite (state_res tv.pre tv.post tv.g_state Ready) as code.up tv.pre;

      (* Needed? We are not releasing the lock. *)
      // tv.state := Running;
      // AR.write tv.g_state Running;
      
      let f = tv.thunk;
      f ();
      
      assert (code.up tv.post);
      rewrite code.up tv.post as (state_res tv.pre tv.post tv.g_state Done);

      tv.state := Done;
      AR.write tv.g_state Done;
      
      release tlk;
      fold (task_alive t);
      ();
    }
    _ -> {
      (* Anything else should be impossible *)
      admit();
    }
  }
}
```

let await_pool'= magic()
let await_pool= magic()
let deallocate_pool = magic()
