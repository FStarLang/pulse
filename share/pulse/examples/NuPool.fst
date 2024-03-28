module NuPool

 // TODO
 //
 // 1- can we remove permission to the pool in await / try_await?
 // Ideally we do not lock the pool or even care much about it.

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open FStar.Tactics
open FStar.Preorder
open Pulse.Lib.Par.Pledge
open Pulse.Lib.Trade
module SmallTrade = Pulse.Lib.SmallTrade

open Pulse.Lib.InvList

module FRAP = Pulse.Lib.FractionalAnchoredPreorder
module AR = Pulse.Lib.AnchoredReference
module BAR = Pulse.Lib.BigAnchoredReference
open Pulse.Lib.CoreRef

open Pulse.Class.Duplicable
module R = Pulse.Lib.RSpinLock
module Big = Pulse.Lib.BigReference
module BigGhost = Pulse.Lib.BigGhostReference
module Ghost = Pulse.Lib.GhostReference

// #set-options "--debug NuPool --debug_level SMTQuery --log_failing_queries"
// #set-options "--print_implicits"
// #set-options "--print_universes"
// #set-options "--split_queries always"

noeq
type vcode : Type u#3 = {
    t : Type u#2;
    up : t -> vprop;
    emp : (emp:t{up emp == Pulse.Lib.Core.emp});
}

noeq
type task_state (#code:vcode) : (post:erased code.t) -> Type u#2 =
  | Ready    : #post:erased code.t -> task_state post
  | Running  : #post:erased code.t -> task_state post
  | Done     : #post:erased code.t -> task_state post
  | Claimed  : #post:erased code.t -> task_state post

let unclaimed (#code:_) (#post:code.t) (s : task_state post) : task_state post =
  match s with
  | Claimed -> Done
  | x -> x

let v #code (#post:code.t) (s : task_state post) : int =
  match s with
  | Ready -> 0
  | Running -> 1
  | Done -> 2
  | Claimed -> 3
  
let p_st #code (#post : code.t) : preorder (task_state post) = fun x y -> b2t (v x <= v y)

let anchor_rel #code (#post:code.t) : FRAP.anchor_rel (p_st #code #post) =
  fun (x y : task_state post) ->
    if Ready? x && Claimed? y then False else squash (p_st x y)
    // match x, y with
    // | Ready, Claimed -> False
    // | x, y -> squash (p_st x y)
    // ^ Fails with Variable "uu___#178" not found. See F* bug #3230

let anchor_rel_refl (#code:_) (#post:code.t) (x:task_state post) :
  Lemma (anchor_rel x x) [SMTPat (anchor_rel x x)]
  =
  assert_norm (anchor_rel #_ #post Ready Ready);
  assert_norm (anchor_rel #_ #post Running Running);
  assert_norm (anchor_rel #_ #post Done Done);
  assert_norm (anchor_rel #_ #post Claimed Claimed)

unfold let p12 : perm = half_perm full_perm

let state_res #code
  ([@@@equate_by_smt]pre : erased code.t)
  ([@@@equate_by_smt]post : erased code.t)
  (g_state : BAR.ref (task_state post) p_st anchor_rel)
  ([@@@equate_by_smt] st : task_state post)
=
  match st with
  | Ready -> code.up pre
  | Running -> emp
  | Done -> code.up post
  | Claimed -> BAR.anchored g_state Claimed

noeq
type handle (#code:vcode) (post : erased code.t) : Type u#0 = {
  state   : Big.ref (task_state post);
  g_state : BAR.ref (task_state post) p_st anchor_rel; (* these two refs are kept in sync *)
}

let state_pred
  (#code:vcode)
  ([@@@equate_by_smt] pre : erased code.t)
  ([@@@equate_by_smt] post : erased code.t)
  ([@@@equate_by_smt] h : handle post)
: vprop =
   exists* (v_state : task_state post).
     Big.pts_to h.state (unclaimed v_state) **
     BAR.pts_to h.g_state v_state **
     state_res pre post h.g_state v_state

noeq
type task_t (code : vcode) : Type u#2 = {
  pre :  erased code.t;
  post : erased code.t;

  h : handle post;

  thunk : unit -> stt unit (code.up pre) (fun _ -> code.up post);
}


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

let mem_lemma (#a:Type) (x:a) (l1 l2:list a)
: Lemma (requires List.memP x l1 /\ list_preorder l1 l2)
        (ensures List.memP x l2)
= admit()

let lock_inv (#code:vcode)
  (runnable   : Big.ref (list (task_t code)))
  (g_runnable : BAR.ref (list (task_t code)) list_preorder list_anchor)
: vprop
= 
  exists*
    (v_runnable : list (task_t code))
  .
    Big.pts_to runnable v_runnable **
    BAR.pts_to_full g_runnable v_runnable **
    all_state_pred v_runnable

noeq
type pool_st (code:vcode) : Type u#0 = {
  runnable   : Big.ref (list (task_t code));
  g_runnable : BAR.ref (list (task_t code)) list_preorder list_anchor;

  lk : lock (lock_inv runnable g_runnable);
}
type pool (code:vcode) = pool_st code

(* Assuming a vprop for lock ownership. *)
assume val lock_alive
  (#p:vprop)
  (#[exact (`full_perm)] f : perm)
  (l : lock p)
  : (v:vprop{is_small v})

let pool_alive (#[exact (`full_perm)] f : perm) (#code:vcode) (p:pool code) : vprop =
  lock_alive #_ #f p.lk

let state_res' #code (post : erased code.t) ([@@@equate_by_smt] st : task_state post) =
  match st with
  | Done -> code.up post
  | Claimed -> emp
  | _ -> pure False

let handle_in_task_list
  (#code:vcode) (#post : erased code.t)
  (h : handle post)
  (ts : list (task_t code))
  : prop
  =
  exists (task : task_t code).
    task.post == post
    /\ task.h == h
    /\ List.memP task ts

let snapshot_mem (#code:vcode)
  (p : pool code)
  (#[@@@equate_by_smt]post : erased code.t)
  (h : handle post)
: vprop =
  exists* v_runnable.
    BAR.snapshot p.g_runnable v_runnable **
    pure (handle_in_task_list h v_runnable)

```pulse
ghost
fn intro_snapshot_mem
    (#code:vcode) (p : pool code)
    (#post:erased code.t) (h : handle post)
    (task : task_t code)
    (ts : list (task_t code))
  requires BAR.snapshot p.g_runnable ts
      ** pure (task.post == post /\ task.h == h /\ List.memP task ts)
  ensures  snapshot_mem p h
{
  fold (snapshot_mem p h);
}
```

```pulse
ghost
fn recall_snapshot_mem0
  (#code:vcode) (p : pool code) (#post : erased code.t) (h : handle post) (#ts : list (task_t code))
  requires BAR.pts_to_full p.g_runnable ts ** snapshot_mem p h
  ensures  BAR.pts_to_full p.g_runnable ts ** snapshot_mem p h **
            pure (handle_in_task_list h ts)
{
  admit();
}
```

```pulse
ghost
fn elim_exists_explicit (#a:Type u#2) (p : a -> prop)
  requires pure (exists x. p x)
  returns  x : a
  ensures  pure (p x)
{
  admit();
}
```
```pulse
ghost
fn recall_snapshot_mem
  (#code:vcode) (p : pool code) (#post : erased code.t) (h : handle post) (#ts : list (task_t code))
  requires BAR.pts_to_full p.g_runnable ts ** snapshot_mem p h
  returns  task : erased (task_t code)
  ensures  BAR.pts_to_full p.g_runnable ts ** snapshot_mem p h **
            pure (task.post == post /\ task.h == h /\ List.memP (reveal task) ts /\
                  handle_in_task_list h ts)
{
  unfold (snapshot_mem p h);
  with ts0. assert (BAR.snapshot p.g_runnable ts0);
  BAR.drop_anchor p.g_runnable;
  BAR.recall_snapshot p.g_runnable;
  BAR.lift_anchor p.g_runnable ts;
  assert (pure (list_preorder ts0 ts /\ True));
  assert (pure (handle_in_task_list h ts0));
  fold (snapshot_mem p h);
  assert (pure (handle_in_task_list h ts0));
  assert (pure (exists (task : task_t code). 
      (task.post == post /\ task.h == h /\ List.memP task ts0)));
  let task = elim_exists_explicit (fun (task : task_t code) ->
      (task.post == post /\ task.h == h /\ List.memP task ts0));
      ();
  mem_lemma task ts0 ts;
  hide task
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
ghost // or concrete?
fn rec extract_state_pred
  (#code:vcode)
  (p : pool code) (#post:code.t) (h : handle post)
  (#ts : list (task_t code))
  requires all_state_pred ts ** pure (handle_in_task_list h ts)
  returns task : erased (task_t code)
  ensures pure (task.post == post /\ task.h == h /\ List.memP (reveal task) ts)
       ** state_pred task.pre task.post task.h
       ** trade (state_pred task.pre task.post task.h) (all_state_pred ts) // trade to put things back togtaskher
  decreases ts
{
  open Pulse.Lib.InvList;
  match ts {
    Nil -> { unreachable () }
    Cons t' ts' -> {
      let b = SEM.strong_excluded_middle (t'.post == post /\ t'.h == h /\ List.memP t' ts);
      if not b {
        take_one_h11 t' ts';
        let ret = extract_state_pred p h #ts';

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

        trade_compose (state_pred ret.pre ret.post ret.h) (all_state_pred ts') (all_state_pred ts);

        ret
      } else {
        let ret = hide t';
        take_one_h11 t' ts';

        ghost
        fn aux (_:unit)
          requires (invlist_v invlist_empty ** (pure (ts == t'::ts') ** all_state_pred ts'))
                ** state_pred t'.pre t'.post t'.h
          ensures   invlist_v invlist_empty ** all_state_pred ts
        {
          add_one_state_pred t' ts';
        };
        intro_trade (state_pred ret.pre ret.post ret.h) (all_state_pred ts)
                    (pure (ts == t'::ts') ** all_state_pred ts') aux;

        ret
      }
    }
  }
}
```

let joinable
  (#code:vcode) (p : pool code)
  ([@@@equate_by_smt]post:erased code.t)
  ([@@@equate_by_smt]h : handle post)
: vprop =
  BAR.anchored h.g_state Ready **
  snapshot_mem p h

```pulse
ghost
fn setup_task_eliminator0
  (#code:vcode)
  (#post:erased code.t)
  (r : BAR.ref (task_state post) p_st anchor_rel)
  (_:unit)
  (* invlist_v [] needed to make the trade introduction below work... *)
  requires Pulse.Lib.InvList.invlist_v [] **
           BAR.anchored r Ready **
           (exists* (s : task_state post). BAR.pts_to r s ** state_res' post s)
  ensures  Pulse.Lib.InvList.invlist_v [] **
           code.up post
{
  with s. assert (BAR.pts_to r s);
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
      drop_ (BAR.anchored r Ready);
      drop_ (BAR.pts_to r Done);
      ()
    }
    Claimed -> {
      assert (BAR.pts_to r Claimed);
      assert (BAR.anchored r Ready);
      BAR.recall_anchor r Ready;
      unreachable ();
    }
  }
}
```

```pulse
ghost
fn setup_task_eliminator (#code:vcode) (#post:erased code.t) (r : BAR.ref (task_state post) p_st anchor_rel)
  requires BAR.anchored r Ready
  ensures  SmallTrade.trade (exists* (s : task_state post). BAR.pts_to r s ** state_res' post s) (code.up post)
{
  SmallTrade.intro_trade #Pulse.Lib.InvList.invlist_empty (exists* (s : task_state post).
     BAR.pts_to r s ** state_res' post s
   ) (code.up post) (BAR.anchored r Ready) (setup_task_eliminator0 #code #post r);
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
  (h : handle post)
  (v_state : task_state post)
  requires
    Big.pts_to h.state (unclaimed v_state) **
    BAR.pts_to h.g_state v_state **
    state_res pre post h.g_state v_state
  ensures state_pred pre post h
{
  fold (state_pred pre post h);
}
```

```pulse
ghost
fn elim_state_pred
  (#code:vcode)
  (pre : erased code.t)
  (post : erased code.t)
  (h : handle post)
  requires state_pred pre post h
  returns v_state : erased (task_state post)
  ensures
    Big.pts_to h.state (unclaimed v_state) **
    BAR.pts_to h.g_state v_state **
    state_res pre post h.g_state v_state
{
  unfold (state_pred pre post h);
  with v_state. assert (state_res pre post h.g_state v_state);
  hide v_state
}
```

```pulse
fn spawn' (code:vcode) (p:pool code)
    (#pf:perm)
    (#pre : erased code.t)
    (#post : erased code.t)
    (f : unit -> stt unit (code.up pre) (fun _ -> (code.up post)))
    requires pool_alive #pf p ** (code.up pre)
    returns  h : handle post
    ensures  pool_alive #pf p ** joinable #code p post h
{
  let task_st : task_state #code post = Ready #code #post;
  assert (pure (anchor_rel #code #post Ready Ready));
  let r_task_st : Big.ref (task_state post) = Big.alloc task_st;
  let gr_task_st : BAR.ref (task_state post) p_st anchor_rel = BAR.alloc #(task_state post) task_st #p_st #anchor_rel;

  BAR.drop_anchor gr_task_st;

  let handle : handle post = {
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
  unfold (lock_inv p.runnable p.g_runnable);
  
  let v_runnable = Big.op_Bang p.runnable;

  Big.op_Colon_Equals p.runnable (task :: v_runnable);
  BAR.write_full p.g_runnable (task :: v_runnable);

  rewrite each task_st as (Ready #code #post);
  rewrite each gr_task_st as task.h.g_state;
  assert (BAR.anchored task.h.g_state (Ready #code #post));
  

  BAR.take_snapshot' p.g_runnable;
  
  assert (pure (List.memP task (task :: v_runnable)));
  intro_snapshot_mem p task.h task (task :: v_runnable);

  fold (joinable #code p post task.h);


  fold (pool_alive #pf p);
  
  assert (Big.pts_to #(task_state post) r_task_st (Ready #code #post));

  rewrite each r_task_st as handle.state;
  rewrite (code.up pre)
       as (state_res pre post gr_task_st Ready);
  rewrite each gr_task_st as handle.g_state;
  rewrite each handle as task.h;
  rewrite each pre as task.pre;
  rewrite each post as task.post;
   
  intro_state_pred task.pre task.post task.h (Ready #code #task.post);
  // fold (state_pred #code task.pre task.post task.h);

  add_one_state_pred task v_runnable;

  fold (lock_inv p.runnable p.g_runnable);

  release lk;

  task.h
}
```

```pulse
ghost
fn claim_done_task
         (#code:vcode) (#p:pool code)
         (#pre : erased code.t) (#post : erased code.t)
         (h : handle post)
  requires state_res pre post h.g_state Done    ** BAR.pts_to h.g_state Done    ** BAR.anchored h.g_state Ready
  ensures  state_res pre post h.g_state Claimed ** BAR.pts_to h.g_state Claimed ** code.up post
{
  rewrite (state_res pre post h.g_state Done)
       as code.up post;

  BAR.lift_anchor h.g_state Ready;

  BAR.write_full h.g_state Claimed;

  BAR.drop_anchor h.g_state;

  fold (state_res pre post h.g_state Claimed);

  ()
}
```

assume
val ar_get_addr : #a:Type0 -> #p:preorder a -> #anc:FRAP.anchor_rel p -> AR.ref a p anc -> core_ref

assume
val same_ref_anchor (#a #b : Type0)
  (#p1 : preorder a) (#p2 : preorder b)
  (#a1 : FRAP.anchor_rel p1) (#a2 : FRAP.anchor_rel p2)
  (r1 : AR.ref a p1 a1) (r2 : AR.ref b p2 a2)
  (v1 : a) (v2 : b)
  (_ : squash (ar_get_addr r1 == ar_get_addr r2))
: stt_ghost unit
      (AR.pts_to r1 v1 ** AR.anchored r2 v2)
      (fun _ -> AR.pts_to r1 v1 ** AR.anchored r2 v2 ** pure (a == b))

(* Trying to await for a spawned task. Note: no preconditions about the pool
here. The task contains its own lock, and we can modify it without synchronizing
with the pool. *)
```pulse
fn try_await
         (#code:vcode) (#p:pool code)
         (#post : erased code.t)
         (h : handle post)
         (#f:perm)
  requires pool_alive #f p ** joinable p post h
  returns  ok : bool
  ensures  pool_alive #f p ** (if ok then code.up post else joinable p post h)
{
  unfold (joinable p post h);

  unfold (pool_alive #f p);
  acquire p.lk;
  unfold (lock_inv p.runnable p.g_runnable);
  
  with v_runnable. assert (Big.pts_to p.runnable v_runnable);

  // let task = recall_snapshot_mem #code p #post h #v_runnable;
  // ^fails: ill-typed substitution or solver could not prove uvar
  // let task : erased (task_t code) = magic u#2 #(erased (task_t code)) ();
  // assume_ (pure (task.post == post /\ task.h == h /\ List.memP (reveal task) v_runnable));

  assert (BAR.pts_to_full p.g_runnable v_runnable);
  assert (snapshot_mem p h);
  
  recall_snapshot_mem0 #code p #post h #v_runnable;

  // recall_snapshot_mem #code p #post h #v_runnable;
  // - Tactic logged issue:
  // - prover error: ill-typed substitutions (prover could not prove uvar _#11)
  
  assert (pure (handle_in_task_list h v_runnable));
  let task = extract_state_pred p h #v_runnable;

  // assume_ (pure (post == task.post)); // fixme: core ref construction

  let v_state = elim_state_pred task.pre task.post task.h;
  
  rewrite (Big.pts_to task.h.state (unclaimed (reveal v_state)))
       as (Big.pts_to h.state (unclaimed (reveal v_state)));
  let task_st = Big.op_Bang h.state;
  
  match task_st {
    Ready -> {
      (* NOOP *)
      rewrite (Big.pts_to h.state (reveal v_state))
           as (Big.pts_to task.h.state (reveal v_state));
      intro_state_pred task.pre task.post task.h Ready;
      elim_trade _ _; // undo extract_state_pred
      fold (lock_inv p.runnable p.g_runnable);
      release p.lk;
      fold (pool_alive #f p);
      fold (joinable p post h);
      false;
    }
    Running -> {
      (* NOOP *)
      rewrite (Big.pts_to h.state (reveal v_state))
           as (Big.pts_to task.h.state (reveal v_state));
      intro_state_pred task.pre task.post task.h Running;
      elim_trade _ _; // undo extract_state_pred
      fold (lock_inv p.runnable p.g_runnable);
      release p.lk;
      fold (pool_alive #f p);
      fold (joinable p post h);
      false;
    }
    Done -> {
      (* First prove that ghost state cannot be Claimed,
      due to the anchor *)
      rewrite (BAR.pts_to task.h.g_state v_state)
           as (BAR.pts_to h.g_state v_state);
      assert (BAR.pts_to h.g_state v_state);
      assert (BAR.anchored h.g_state Ready);
      BAR.recall_anchor h.g_state Ready;
      assert (pure (v_state =!= Claimed));
      assert (pure (v_state == Done));
      rewrite (BAR.pts_to h.g_state v_state)
           as (BAR.pts_to task.h.g_state v_state);

      (* Now claim it *)
      claim_done_task #code #p #task.pre #task.post task.h;

      rewrite (code.up post)
           as (if true then code.up post else joinable p post h);
           
      rewrite (Big.pts_to h.state Done)
           as (Big.pts_to task.h.state (unclaimed Claimed));
      intro_state_pred task.pre task.post task.h Claimed;
      elim_trade _ _; // undo extract_state_pred
      fold (lock_inv p.runnable p.g_runnable);
      release p.lk;
      fold (pool_alive #f p);
      drop_ (snapshot_mem p h);
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
// Busy waiting version of await
fn await (#code:vcode) (#p:pool code)
         (#post : erased code.t)
         (h : handle post)
         (#f:perm) // TODO: remove permission on pool. If h is joinable, pool must be alive
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
    let b = try_await #code #p #post h #f;
    done := b;
  };
}
```

let handle_done (#code:vcode) (#post:erased code.t) (h:handle post) : vprop =
  BAR.snapshot h.g_state Done
  
```pulse
ghost
fn disown_aux
  (#code:vcode) (#p:pool code)
  (#post : erased code.t)
  (h : handle post)
  (_:unit)
  requires invlist_v invlist_empty ** ((lock_inv p.runnable p.g_runnable ** handle_done h) ** joinable p post h)
  ensures  invlist_v invlist_empty ** ((lock_inv p.runnable p.g_runnable ** handle_done h) ** code.up post)
{
  unfold (handle_done h);
  unfold (lock_inv p.runnable p.g_runnable);
  unfold (joinable p post h);

  with v_runnable. assert (Big.pts_to p.runnable v_runnable);

  (* FIXME: calling recall_snapshot_mem (not the 0 version) fails *)
  recall_snapshot_mem0 #code p #post h #v_runnable;
  let et = extract_state_pred p h #v_runnable;

  unfold (state_pred et.pre et.post et.h);

  with st. assert (BAR.pts_to et.h.g_state st);
  let st = reveal st;

  match st {
    Done -> {
      rewrite (state_res et.pre et.post et.h.g_state Done)
           as code.up post;

      BAR.lift_anchor et.h.g_state Ready;
      BAR.write_full et.h.g_state Claimed;
      BAR.drop_anchor et.h.g_state;

      fold (state_res et.pre et.post et.h.g_state Claimed);
      
      rewrite (Big.pts_to et.h.state Done)
           as (Big.pts_to et.h.state (unclaimed Claimed));
      
      intro_state_pred et.pre et.post et.h Claimed;

      fold (handle_done h);
      drop_ (snapshot_mem p h);
      
      elim_trade_ghost _ _;
      
      fold (lock_inv p.runnable p.g_runnable);
      
      ();
    }
    Claimed -> {
      assert (BAR.anchored h.g_state Ready);
      BAR.recall_anchor et.h.g_state Ready;
      unreachable();
    }
    Ready -> {
      rewrite (BAR.pts_to et.h.g_state Ready)
           as BAR.pts_to h.g_state Ready;
      BAR.recall_snapshot h.g_state;
      unreachable();
    }
    Running -> { 
      rewrite (BAR.pts_to et.h.g_state Running)
           as BAR.pts_to h.g_state Running;
      BAR.recall_snapshot h.g_state;
      unreachable();
    }
  }
}
```

```pulse
fn disown (#code:vcode) (#p:pool code)
      (#post : erased code.t)
      (h : handle post)
  requires joinable p post h
  ensures  pledge [] (lock_inv p.runnable p.g_runnable ** handle_done h) (code.up post)
{
  make_pledge [] (lock_inv p.runnable p.g_runnable ** handle_done h) (code.up post) (joinable p post h)
      (disown_aux #code #p #post h)
}
```

let pool_done (#code:vcode) (p : pool code) = emp // what is pool_done ????
```pulse
ghost
fn pool_done_handle_done (#code:vcode) (#p:pool code)
      (#post : erased code.t)
      (h : handle post)
  requires emp
  ensures pledge [] (pool_done p) (handle_done h)
{
  admit();
}
```

```pulse
(* Called with pool lock taken *)
fn rec grab_work' (#code:vcode) (p:pool code)
  requires lock_inv p.runnable p.g_runnable
  returns  topt : option (task_t code)
  ensures  lock_inv p.runnable p.g_runnable ** (if Some? topt then code.up (Some?.v topt).pre else emp)
{
  unfold (lock_inv p.runnable p.g_runnable);
  with v_runnable. assert (Big.pts_to p.runnable v_runnable);

  let runnable0 = Big.op_Bang p.runnable;
  match runnable0 {
    Nil -> {
      let topt : option (task_t code) = None #(task_t code);
      rewrite emp as
        (if Some? topt then code.up (Some?.v topt).pre else emp);
      fold (lock_inv p.runnable p.g_runnable);
      topt
    }
    Cons t ts -> {
      take_one_h11 t ts;
      unfold (state_pred t.pre t.post t.h);
      
      let st = Big.op_Bang t.h.state;
      match st {
        Ready -> {
          let topt = Some #(task_t code) t;
          rewrite (emp ** state_res t.pre t.post t.h.g_state Ready)
               as (state_res t.pre t.post t.h.g_state Running ** code.up t.pre);

          Big.op_Colon_Equals t.h.state Running;
          BAR.write t.h.g_state Running;

          intro_state_pred t.pre t.post t.h Running;
          add_one_state_pred t ts;
          fold (lock_inv p.runnable p.g_runnable);
          
          rewrite code.up t.pre as
            (if Some? topt then code.up (Some?.v topt).pre else emp);
          
          topt
        }
        _ -> {
          (* recurse. should be straightforward after refactoring this fn *)
          admit();
        }
      }
    }
  }
}
```

```pulse
fn grab_work (#code:vcode) (p:pool code)
  requires pool_alive #f p
  returns  topt : option (task_t code)
  ensures  pool_alive #f p ** (if Some? topt then code.up (Some?.v topt).pre else emp)
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
  requires pool_alive #f p ** code.up t.post
  ensures  pool_alive #f p
{
  admit();
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
      perf_work t;
      put_back_result p t;
      worker p
    }
  }
}
```

let await_pool'= magic()
let await_pool= magic()
let deallocate_pool = magic()
