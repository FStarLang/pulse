module NuPool.Code

open Pulse.Lib.Pervasives
open Pulse.Lib.Pledge
open Pulse.Lib.Codeable
open FStar.FunctionalExtensionality

module P = NuPool
module T = FStar.Tactics.V2

open Pulse.Lib.InvTokens

(* A reminder: if we index this type by the actual pool `p` too,
instead of quantifying over it in Alive/Done, we would not be able
to even create a pool in the first place, as we would have to do
a circular defintion like

  let p = P.setup_pool (poolcode base p) n in
  ...

which would not work. It would also limit the ability to interoperate
between different pools of the same code. *)

noeq
type poolcode_t (code_t:Type u#2) : Type u#2 =
  | Base   : code_t -> poolcode_t code_t
  | Star   : poolcode_t code_t -> poolcode_t code_t -> poolcode_t code_t
  | Emp    : poolcode_t code_t
  | J      : p:P.pool (poolcode_t code_t) -> poolcode_t code_t -> P.handle -> poolcode_t code_t
  | Pledge : is:inames -> pre:poolcode_t code_t -> post:poolcode_t code_t -> poolcode_t code_t
  | Ex0    : a:Type u#0 -> (a -> poolcode_t code_t) -> poolcode_t code_t
  | Alive  : f:perm -> p:P.pool (poolcode_t code_t) -> poolcode_t code_t
  | Done   : p:P.pool (poolcode_t code_t) -> poolcode_t code_t

let __alive_proxy (#base_t:Type u#2) (f:perm) (p:P.pool (poolcode_t base_t)) : boxable =
  exists* (code_interp : poolcode_t base_t -> boxable).
    P.pool_alive #f ({t=poolcode_t base_t; up=code_interp}) p

let __done_proxy (#base_t:Type u#2) (p:P.pool (poolcode_t base_t)) : boxable =
  exists* (code_interp : poolcode_t base_t -> boxable).
    P.pool_done ({t=poolcode_t base_t; up=code_interp}) p

let rec poolcode_up
  (base : vcode)
  (c : poolcode_t base.t)
  : Tot boxable
=
  match c with
  | Base v -> base.up v
  | Star p q -> poolcode_up base p ** poolcode_up base q
  | Emp -> emp
  | J p post h ->
    P.joinable p post h
  | Pledge is pre post ->
    admit();
    pledge is (poolcode_up base pre) (poolcode_up base post)
  | Ex0 ty f ->
    op_exists_Star #ty (fun (x:ty) -> poolcode_up base (f x))
  | Alive f p ->
    __alive_proxy #base.t f p
  | Done p ->
    __done_proxy #base.t p

let poolcode (base:vcode)
  : Tot (v:vcode{v.t == poolcode_t base.t})
= {
  t = poolcode_t base.t;
  up = poolcode_up base
}

noeq
type pool' (base : vcode) = {
  p : P.pool (poolcode_t base.t);
  i : iref;
  itok : inv_token i (P.pool_alive0 (poolcode base) p);
}

let pool_inames (#base:_) (p : pool' base) : inames = add_inv emp_inames p.i

(* Hopefully, this is what most users use. *)
let pool = pool' small_code

let alive_proxy (#base:vcode) (f:perm) (p:pool' base) : vprop =
  __alive_proxy f p.p

let done_proxy (#base:vcode) (p:pool' base) : vprop =
    __done_proxy p.p

let handle : Type u#0 = P.handle

(* These can be hidden *)
let pool_alive
  (#[T.exact (`1.0R)] pf : perm)
  (#base:vcode)
  (p : pool' base)
  : vprop
  = P.pool_alive #pf (poolcode base) p.p

let pool_done
  (#base:vcode)
  (p : pool' base)
  : vprop
  = P.pool_done (poolcode base) p.p

let joinable
  (#base:vcode)
  (p : pool' base)
  (post: vprop) {| codeable (poolcode base) post |}
  (h:handle)
  : vprop
  = P.joinable #(poolcode base).t p.p (encode post) h

val spawn
  (#base:vcode)
  (p : pool' base)
  (#pf : perm)
  (#pre : vprop) {| codeable (poolcode base) pre  |}
  (#post: vprop) {| codeable (poolcode base) post |}
  (f : unit -> stt unit pre (fun _ -> post))
  : stt handle (pool_alive #pf p ** pre)
               (fun h -> pool_alive #pf p ** joinable p post h)

val disown
  (#base:vcode)
  (#p : pool' base)
  (#post: vprop) {| codeable (poolcode base) post |}
  (h : handle)
  : stt_ghost unit emp_inames
                   (joinable p post h)
                   (fun _ -> pledge emp_inames (pool_done p) post)

(* spawn + disown *)
val spawn_
  (#base:vcode)
  (p : pool' base)
  (#pf : perm)
  (#pre : vprop) {| codeable (poolcode base) pre  |}
  (#post: vprop) {| codeable (poolcode base) post |}
  (f : unit -> stt unit pre (fun _ -> post))
  : stt unit (pool_alive #pf p ** pre)
             (fun _ -> pool_alive #pf p ** pledge emp_inames (pool_done p) post)

val await
  (#base:vcode)
  (#p : pool' base)
  (#post: vprop) {| codeable (poolcode base) post |}
  (h : handle)
  (#pf : perm)
  : stt unit (pool_alive #pf p ** joinable p post h)
             (fun _ -> pool_alive #pf p ** post)

val await_pool
  (#base:vcode)
  (p : pool' base)
  (#is:inames)
  (#pf:perm)
  (q : vprop)
  : stt unit (pool_alive #pf p ** pledge is (pool_done p) q)
             (fun _ -> pool_alive #pf p ** q)

val teardown_pool
  (#base:vcode)
  (p : pool' base)
  : stt unit (pool_alive p)
             (fun _ -> pool_done p)

val setup_pool
  (#base:vcode)
  (n : pos)
  : stt (pool' base)
        emp
        (fun p -> pool_alive p)

val share_alive
  (#base:vcode)
  (p : pool' base)
  (e:perm)
  : stt_ghost unit emp_inames
              (pool_alive #e p)
              (fun () -> pool_alive #(e /. 2.0R) p ** pool_alive #(e /. 2.0R) p)

val gather_alive
  (#base:vcode)
  (p : pool' base)
  (e:perm)
  : stt_ghost unit emp_inames
              (pool_alive #(e /. 2.0R) p ** pool_alive #(e /. 2.0R) p)
              (fun () -> pool_alive #e p)


val recover_alive (#base:vcode) (p:pool' base) (#f:perm)
  : stt_atomic unit
      (add_iname emp_inames (iname_of p.i))
      (alive_proxy f p)
      (fun _ -> pool_alive #f p)

val stash_alive (#base:vcode) (p:pool' base) (#f:perm)
  : stt_ghost unit
      emp_inames
      (pool_alive #f p)
      (fun _ -> alive_proxy f p)

val share_alive_proxy (#base:vcode) (p:pool' base) (#f:perm)
  : stt_ghost unit
      emp_inames
      (alive_proxy f p)
      (fun _ -> alive_proxy (f /. 2.0R) p ** alive_proxy (f /. 2.0R) p)

val gather_alive_proxy (#base:vcode) (p:pool' base) (#f:perm)
  : stt_ghost unit
      emp_inames
      (alive_proxy (f /. 2.0R) p ** alive_proxy (f /. 2.0R) p)
      (fun _ -> alive_proxy f p)

val recover_done (#base:vcode) (p:pool' base)
  : stt_atomic unit
      (add_iname emp_inames (iname_of p.i))
      (done_proxy p)
      (fun _ -> pool_done p)

val stash_done (#base:vcode) (p:pool' base)
  : stt_ghost unit
      emp_inames
      (pool_done p)
      (fun _ -> done_proxy p)

val weaken_done_proxy_pledge
  (#base:vcode) (p : pool' base)
  (post : vprop)
  : stt_atomic unit
        emp_inames
        (pledge (pool_inames p) (done_proxy p) post)
        (fun _ -> pledge (pool_inames p) (pool_done p) post)

val strengthen_done_proxy_pledge
  (#base:vcode) (p : pool' base)
  (post : vprop)
  : stt_atomic unit
        emp_inames
        (pledge (pool_inames p) (pool_done p) post)
        (fun _ -> pledge (pool_inames p) (done_proxy p) post)
