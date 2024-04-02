module NuPool.Code

open Pulse.Lib.Pervasives
module T = FStar.Tactics
open Pulse.Lib.Pledge
open Pulse.Lib.Codeable
module InvTokens = Pulse.Lib.InvTokens
module P = NuPool

```pulse
fn __spawn
  (#base:vcode) (p:pool' base)
  (#pf:perm)
  (#pre : vprop) {| codeable (poolcode base) pre  |}
  (#post: vprop) {| codeable (poolcode base) post |}
  (f : unit -> stt unit pre (fun _ -> post))
  requires pool_alive #pf p ** pre
  returns  h : handle
  ensures  pool_alive #pf p ** joinable p post h
{
  unfold (pool_alive #pf p);

  rewrite pre
       as ((poolcode base).up (encode pre));

  let h = P.spawn #(poolcode base) p.p #pf #(encode pre) #(encode post) f;

  fold (pool_alive #pf p);
  fold (joinable p post h);
  h
}
```

```pulse
ghost
fn __disown
  (#base:vcode) (#p:pool' base)
  (#post: vprop) {| d2 : codeable (poolcode base) post |}
  (h:handle)
  requires joinable p post h
  ensures  pledge emp_inames (pool_done p) post
{
  unfold (joinable p post h);
  P.disown #(poolcode base) h;
  rewrite (pledge emp_inames (P.pool_done (poolcode base) p.p) ((poolcode base).up (encode post)))
       as (pledge emp_inames (pool_done p) post);
  ()
}
```

```pulse
fn __spawn_
  (#base:vcode) (p:pool' base)
  (#pf:perm)
  (#pre : vprop) {| d1 : codeable (poolcode base) pre  |}
  (#post: vprop) {| d2 : codeable (poolcode base) post |}
  (f : unit -> stt unit pre (fun _ -> post))
  requires pool_alive #pf p ** pre
  ensures  pool_alive #pf p ** pledge emp_inames (pool_done p) post
{
  let h = __spawn p d1 d2 f;
  __disown d2 h;
}
```

```pulse
fn __await
  (#base:vcode) (#p:pool' base)
  (#post: vprop) {| d2 : codeable (poolcode base) post |}
  (h : handle)
  (#pf : perm)
  requires pool_alive #pf p ** joinable p post h
  ensures  pool_alive #pf p ** post
{
  unfold (pool_alive #pf p);
  unfold (joinable p post h);
  P.await #(poolcode base) h;
  rewrite ((poolcode base).up (encode post))
       as post;
  fold (pool_alive #pf p);
  ();
}
```

```pulse
fn __await_pool
  (#base:vcode) (p:pool' base)
  (#is : inames)
  (#pf : perm)
  (q : vprop)
  requires pool_alive #pf p ** pledge is (pool_done p) q
  ensures  pool_alive #pf p ** q
{
  unfold (pool_alive #pf p);
  rewrite (pledge is (pool_done p) q)
       as (pledge is (P.pool_done (poolcode base) p.p) q);
  P.await_pool #(poolcode base) p.p q;
  fold (pool_alive #pf p);
  ()
}
```

```pulse
fn __teardown_pool
  (#base:vcode) (p:pool' base)
  requires pool_alive p
  ensures  pool_done p
{
  unfold (pool_alive p);
  P.teardown_pool #(poolcode base) p.p;
  fold (pool_done p);
}
```

```pulse
fn __setup_pool
  (#base:vcode) (n:pos)
  requires emp
  returns p : pool' base
  ensures pool_alive p
{
  let pp = P.setup_pool #(poolcode base) n;
  P.get_pool_alive0 pp;
  let i = new_invariant (P.pool_alive0 (poolcode base) pp);
  let itok = InvTokens.witness i;
  let p = { p=pp; i; itok};
  rewrite each base as base;
  rewrite each pp as p.p;
  fold (pool_alive #1.0R p);
  drop_ (inv i _);
  p
}
```

```pulse
ghost
fn __share_alive
  (#base:vcode) (p:pool' base)
  (e:perm)
  requires pool_alive #e p
  ensures  pool_alive #(e /. 2.0R) p ** pool_alive #(e /. 2.0R) p
{
  unfold (pool_alive #e p);
  P.share_alive #(poolcode base) p.p e;
  fold (pool_alive #(e /. 2.0R) p);
  fold (pool_alive #(e /. 2.0R) p);
}
```

```pulse
ghost
fn __gather_alive
  (#base:vcode) (p:pool' base)
  (e:perm)
  requires pool_alive #(e /. 2.0R) p ** pool_alive #(e /. 2.0R) p
  ensures  pool_alive #e p
{
  unfold (pool_alive #(e /. 2.0R) p);
  unfold (pool_alive #(e /. 2.0R) p);
  P.gather_alive #(poolcode base) p.p e;
  fold (pool_alive #e p);
}
```

```pulse
atomic
fn __recover_alive (#base:vcode) (p : pool' base) (#f:perm)
  requires alive_proxy f p
  ensures  pool_alive #f p
  opens add_iname emp_inames (iname_of p.i)
{
  unfold (alive_proxy f p);
  recall p.itok;
  with_invariants p.i
    returns _:unit
    ensures P.pool_alive #f (poolcode base) p.p ** inv p.i (P.pool_alive0 (poolcode base) p.p)
  {
    unfold (__alive_proxy f p.p);
    P.pool_alive0_inj_r
      (*code1*) ({t = poolcode_t base.t; up = _}) (* thankfully pulse fills the _ *)
      (*code2*) (poolcode base)
      (*p*) p.p
      (*f2*) f;
  };
  drop_ (inv p.i _);
  fold (pool_alive #f p);
}
```

```pulse
ghost
fn __stash_alive (#base:vcode) (p : pool' base) (#f:perm)
  requires pool_alive #f p
  ensures  alive_proxy f p
{
  unfold (pool_alive #f p);
  rewrite
    P.pool_alive #f (poolcode base) p.p
  as
    P.pool_alive #f ({t=poolcode_t base.t; up=poolcode_up base}) p.p;
  fold (__alive_proxy f p.p);
  fold (alive_proxy f p);
}
```

```pulse
ghost
fn __share_alive_proxy (#base:vcode) (p:pool' base) (#f:perm)
  requires alive_proxy f p
  ensures  alive_proxy (f /. 2.0R) p ** alive_proxy (f /. 2.0R) p
{
  unfold alive_proxy;
  unfold __alive_proxy;
  (* For whatever reason we have to give part of the code by hand *)
  P.share_alive
    #({t = poolcode_t base.t; up = _})
    p.p _;
  fold (__alive_proxy (f /. 2.0R) p.p);
  fold alive_proxy;
  fold __alive_proxy;
  fold alive_proxy;
}
```


[@@allow_ambiguous]
let pool_alive_inj_ambig =
  P.pool_alive_inj_l

```pulse
ghost
fn __gather_alive_proxy (#base:vcode) (p:pool' base) (#f:perm)
  requires alive_proxy (f /. 2.0R) p ** alive_proxy (f /. 2.0R) p
  ensures  alive_proxy f p
{
  unfold alive_proxy;
  unfold alive_proxy;
  unfold __alive_proxy;
  unfold __alive_proxy;
  pool_alive_inj_ambig
      (*code1*) ({t = poolcode_t base.t; up = _})
      (*code2*) ({t = poolcode_t base.t; up = _})
      (*p*) p.p
      (*f1*) _
      (*f2*) _;
  P.gather_alive
    #({t = poolcode_t base.t; up = _})
    p.p _;
  fold __alive_proxy;
  fold alive_proxy;
}
```

```pulse
ghost
fn __ghost_recover_done (#base:vcode) (p : pool' base)
  requires done_proxy p ** inv p.i (P.pool_alive0 (poolcode base) p.p)
  ensures  pool_done p
  opens add_iname emp_inames (iname_of p.i)
{
  with_invariants p.i
    returns _:unit
    ensures P.pool_done (poolcode base) p.p ** inv p.i (P.pool_alive0 (poolcode base) p.p)
  {
    unfold (done_proxy p);
    unfold (__done_proxy p.p);
    P.pool_done0_inj_r
      (*code1*) ({t = poolcode_t base.t; up = _}) (* thankfully pulse fills the _ *)
      (*code2*) (poolcode base)
      (*p*) p.p
      #(); // without this we blow up...
    ()
  };
  drop_ (inv p.i _);
  fold (pool_done p);
}
```

```pulse
atomic
fn __recover_done (#base:vcode) (p : pool' base)
  requires done_proxy p
  ensures  pool_done p
  opens add_iname emp_inames (iname_of p.i)
{
  recall p.itok;
  __ghost_recover_done p;
}
```

```pulse
ghost
fn __stash_done (#base:vcode) (p : pool' base)
  requires pool_done p
  ensures  done_proxy p
{
  unfold (pool_done p);
  rewrite
    P.pool_done (poolcode base) p.p
  as
    P.pool_done ({t=poolcode_t base.t; up=poolcode_up base}) p.p;
  fold (__done_proxy p.p);
  fold (done_proxy p);
}
```

```pulse
atomic
fn __weaken_done_proxy_pledge
  (#base:vcode) (p : pool' base)
  (post : vprop)
  requires pledge (pool_inames p) (done_proxy p) post
  ensures  pledge (pool_inames p) (pool_done p) post
{
  Pulse.Lib.InvTokens.recall p.itok;
  ghost
  fn aux (_:unit)
    requires pool_done p ** (pledge (pool_inames p) (done_proxy p) post ** inv p.i (P.pool_alive0 (poolcode base) p.p))
    ensures  pool_done p ** post
    opens pool_inames p
  {
    __stash_done p;
    redeem_pledge _ _ _;
    __ghost_recover_done p;
  };
  make_pledge
    (pool_inames p)
    (pool_done p) post
    (*extra*) (pledge (pool_inames p) (done_proxy p) post ** inv p.i (P.pool_alive0 (poolcode base) p.p))
    aux;
}
```

```pulse
atomic
fn __strengthen_done_proxy_pledge
  (#base:vcode) (p : pool' base)
  (post : vprop)
  requires pledge (pool_inames p) (pool_done p) post
  ensures  pledge (pool_inames p) (done_proxy p) post
{
  Pulse.Lib.InvTokens.recall p.itok;
  ghost
  fn aux (_:unit)
    requires done_proxy p ** (pledge (pool_inames p) (pool_done p) post ** inv p.i (P.pool_alive0 (poolcode base) p.p))
    ensures  done_proxy p ** post
    opens pool_inames p
  {
    __ghost_recover_done p;
    redeem_pledge _ _ _;
    __stash_done p;
  };
  make_pledge
    (pool_inames p)
    (done_proxy p) post
    (*extra*) (pledge (pool_inames p) (pool_done p) post ** inv p.i (P.pool_alive0 (poolcode base) p.p))
    aux;
}
```

(* Eta expand to get back the typeclass annotation. See issue #34. *)

let spawn p #pf #pre #cpre #post #cpost f = __spawn p #pf #pre cpre #post cpost f
let disown #base #p #post #cpost h = __disown #base #p cpost h
let spawn_ p #pf #pre #cpre #post #cpost f = __spawn_ p #pf #pre cpre #post cpost f
let await #base #p #post #cpost h #pf = __await #base #p cpost h #pf
let await_pool p #pf q = __await_pool p #pf q
let teardown_pool p = __teardown_pool p
let setup_pool #base n = __setup_pool #base n
let share_alive p e = __share_alive p e
let gather_alive p e = __gather_alive p e

let recover_alive = __recover_alive
let stash_alive = __stash_alive
let share_alive_proxy = __share_alive_proxy
let gather_alive_proxy = __gather_alive_proxy

let recover_done = __recover_done
let stash_done = __stash_done

let weaken_done_proxy_pledge p post = __weaken_done_proxy_pledge p post
let strengthen_done_proxy_pledge p post = __strengthen_done_proxy_pledge p post
