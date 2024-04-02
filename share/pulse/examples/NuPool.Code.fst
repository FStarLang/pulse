module NuPool.Code

open Pulse.Lib.Pervasives
module T = FStar.Tactics
open Pulse.Lib.Par.Pledge
open Codeable

module P = NuPool

module TC = FStar.Tactics.Typeclasses

#set-options "--print_implicits"

```pulse
fn __spawn
  (p:pool)
  (#pf:perm)
  (#pre : vprop) {| codeable (poolcode p.base) pre  |}
  (#post: vprop) {| codeable (poolcode p.base) post |}
  (f : unit -> stt unit pre (fun _ -> post))
  requires pool_alive #pf p ** pre
  returns  h : handle
  ensures  pool_alive #pf p ** joinable p post h
{
  unfold (pool_alive #pf p);

  rewrite pre
       as ((poolcode p.base).up (encode pre));

  let h = P.spawn #(poolcode p.base) p.p #pf #(encode pre) #(encode post) f;
  fold (pool_alive #pf p);

  rewrite (P.joinable #(poolcode p.base).t p.p (encode post) h) 
       as (joinable p post h); // FIXME: fold fails
  h
}
```
  
```pulse
ghost
fn __disown (#p:pool)
  (#post: vprop) {| d2 : codeable (poolcode p.base) post |}
  (h:handle)
  requires joinable p post h
  ensures  pledge [] (pool_done p) post
{
  unfold (joinable p post h);
  P.disown #(poolcode p.base) h;
  rewrite (pledge [] (P.pool_done (poolcode p.base) p.p) ((poolcode p.base).up (encode post)))
       as (pledge [] (pool_done p) post);
  ()
}
```

```pulse
fn __spawn_
  (p:pool)
  (#pf:perm)
  (#pre : vprop) {| d1 : codeable (poolcode p.base) pre  |}
  (#post: vprop) {| d2 : codeable (poolcode p.base) post |}
  (f : unit -> stt unit pre (fun _ -> post))
  requires pool_alive #pf p ** pre
  ensures  pool_alive #pf p ** pledge [] (pool_done p) post
{
  let h = __spawn p d1 d2 f;
  __disown #p #post d2 h;
}
```

```pulse
fn __await
 
  (#p : pool)
  (#post: vprop) {| d2 : codeable (poolcode p.base) post |}
  (h : handle)
  (#pf : perm)
  requires pool_alive #pf p ** joinable p post h
  ensures  pool_alive #pf p ** post
{
  unfold (pool_alive #pf p);
  unfold (joinable p post h);
  P.await #(poolcode p.base) h;
  rewrite ((poolcode p.base).up (encode post))
       as post;
  fold (pool_alive #pf p);
  ();
}
```

```pulse
fn __await_pool
  
   (p : pool)
   (#is : Pulse.Lib.InvList.invlist)
   (#pf : perm)
   (q : vprop)
   requires pool_alive #pf p ** pledge is (pool_done p) q
   ensures  pool_alive #pf p ** q
{
  unfold (pool_alive #pf p);
  rewrite (pledge is (pool_done p) q)
       as (pledge is (P.pool_done (poolcode p.base) p.p) q);
  P.await_pool #(poolcode p.base) p.p q;
  fold (pool_alive #pf p);
  ()
}
```

```pulse
fn __teardown_pool
 
  (p : pool)
  requires pool_alive p
  ensures  pool_done p
{
  unfold (pool_alive p);
  P.teardown_pool #(poolcode p.base) p.p;
  fold (pool_done p);
}
```

```pulse
fn __setup_pool
  (#base:vcode) (n:pos)
  requires emp
  returns p : pool
  ensures pool_alive p ** pure (p.base == base)
{
  let pp = P.setup_pool #(poolcode base) n;
  let p = { base; p=pp };
  rewrite each base as p.base;
  rewrite each pp as p.p;
  fold (pool_alive #full_perm p);
  p
}
```

```pulse
ghost
fn __share_alive
 
  (p:pool)
  (e:perm)
  requires pool_alive #e p
  ensures  pool_alive #(half_perm e) p ** pool_alive #(half_perm e) p
{
  unfold (pool_alive #e p);
  P.share_alive #(poolcode p.base) p.p e;
  fold (pool_alive #(half_perm e) p);
  fold (pool_alive #(half_perm e) p);
}
```

```pulse
ghost
fn __gather_alive
 
  (p:pool)
  (e:perm)
  requires pool_alive #(half_perm e) p ** pool_alive #(half_perm e) p
  ensures  pool_alive #e p
{
  unfold (pool_alive #(half_perm e) p);
  unfold (pool_alive #(half_perm e) p);
  P.gather_alive #(poolcode p.base) p.p e;
  fold (pool_alive #e p);
}
```

(* Eta expand to get back the typeclass annotation. See issue #34. *)

let spawn p #pf #pre #cpre #post #cpost f = __spawn p #pf #pre cpre #post cpost f
let disown #p #post #cpost h = __disown #p cpost h
let spawn_ p #pf #pre #cpre #post #cpost f = __spawn_ p #pf #pre cpre #post cpost f
let await #p #post #cpost h #pf = __await #p cpost h #pf
let await_pool p #pf q = __await_pool p #pf q
let teardown_pool p = __teardown_pool p
let setup_pool #base n = __setup_pool #base n
let share_alive p e = __share_alive p e
let gather_alive p e = __gather_alive p e
