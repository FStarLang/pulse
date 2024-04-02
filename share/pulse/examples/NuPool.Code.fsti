module NuPool.Code

open Pulse.Lib.Pervasives
open Pulse.Lib.Par.Pledge
open Codeable
open FStar.FunctionalExtensionality

module P = NuPool
module T = FStar.Tactics.V2

noeq
type poolcode_t (code_t:Type u#2) : Type u#2 =
  | Base  : code_t -> poolcode_t code_t
  | Star  : poolcode_t code_t -> poolcode_t code_t -> poolcode_t code_t
  | Emp   : poolcode_t code_t
  | J     : p:P.pool (poolcode_t code_t) -> poolcode_t code_t -> P.handle -> poolcode_t code_t
  | Pl    : pre:poolcode_t code_t -> post:poolcode_t code_t -> poolcode_t code_t
  | Ex0   : a:Type u#0 -> (a ^-> poolcode_t code_t) -> poolcode_t code_t

let rec poolcode_up
  (base : vcode)
  (c : poolcode_t base.t)
  : Tot vprop
=
  match c with
  | Base v -> base.up v
  | Star p q -> poolcode_up base p ** poolcode_up base q
  | Emp -> emp
  | J p post h ->
    P.joinable p post h
  | Pl pre post ->
    pledge [] (poolcode_up base pre) (poolcode_up base post)
  | Ex0 ty f ->
    op_exists_Star #ty (fun (x:ty) -> poolcode_up base (f x))

let poolcode (base:vcode)
  : Tot (v:vcode{v.t == poolcode_t base.t}) 
= {
  t = poolcode_t base.t;
  up = poolcode_up base
}

noeq
type pool = {
  base : vcode;
  p : P.pool (poolcode_t base.t);
}

let handle : Type u#0 = P.handle

let pool_alive
  (#[T.exact (`full_perm)] pf : perm)
  (p : pool)
  : vprop
  = P.pool_alive #pf (poolcode p.base) p.p

let pool_done
  (p : pool)
  : vprop
  = P.pool_done (poolcode p.base) p.p
  
let joinable
  (p:pool)
  (post: vprop) {| codeable (poolcode p.base) post |}
  (h:handle)
  : vprop
  = P.joinable #(poolcode p.base).t p.p (encode post <: (poolcode p.base).t) h

val spawn
  (p : pool)
  (#pf : perm)
  (#pre : vprop) {| codeable (poolcode p.base) pre  |}
  (#post: vprop) {| codeable (poolcode p.base) post |}
  (f : unit -> stt unit pre (fun _ -> post))
  : stt handle (pool_alive #pf p ** pre)
               (fun h -> pool_alive #pf p ** joinable p post h)

val disown
  (#p : pool)
  (#post: vprop) {| codeable (poolcode p.base) post |}
  (h : handle)
  : stt_ghost unit (joinable p post h)
                   (fun _ -> pledge [] (pool_done p) post)

(* spawn + disown *)
val spawn_
  (p : pool)
  (#pf : perm)
  (#pre : vprop) {| codeable (poolcode p.base) pre  |}
  (#post: vprop) {| codeable (poolcode p.base) post |}
  (f : unit -> stt unit pre (fun _ -> post))
  : stt unit (pool_alive #pf p ** pre)
             (fun _ -> pool_alive #pf p ** pledge [] (pool_done p) post)

val await
  (#p : pool)
  (#post: vprop) {| codeable (poolcode p.base) post |}
  (h : handle)
  (#pf : perm)
  : stt unit (pool_alive #pf p ** joinable p post h)
             (fun _ -> pool_alive #pf p ** post)

val await_pool
  (p:pool)
  (#is:Pulse.Lib.InvList.invlist)
  (#pf:perm)
  (q : vprop)
  : stt unit (pool_alive #pf p ** pledge is (pool_done p) q)
             (fun _ -> pool_alive #pf p ** q)

val teardown_pool
  (p:pool)
  : stt unit (pool_alive p)
             (fun _ -> pool_done p)

val setup_pool
  (#base:vcode)
  (n : pos)
  : stt pool emp
             (fun p -> pool_alive p ** pure (p.base == base))

val share_alive
  (p:pool)
  (e:perm)
  : stt_ghost unit
              (pool_alive #e p)
              (fun () -> pool_alive #(half_perm e) p ** pool_alive #(half_perm e) p)

val gather_alive
  (p:pool)
  (e:perm)
  : stt_ghost unit
              (pool_alive #(half_perm e) p ** pool_alive #(half_perm e) p)
              (fun () -> pool_alive #e p)
