module NuPool

open Pulse.Lib.Pervasives
open Pulse.Lib.Par.Pledge
module T = FStar.Tactics.V2
open Codeable

val handle : Type u#0
val pool ([@@@strictly_positive] code_t:Type u#2) : Type u#0
val pool_alive (#[T.exact (`full_perm)] f : perm) (code:vcode) (p:pool code.t) : vprop

val joinable (#code_t:Type u#2) (p:pool code_t) (post:erased code_t) (h : handle) : vprop

val spawn
  (#code:vcode)
  (p : pool code.t)
  (#pf : perm)
  (#pre : erased code.t)
  (#post : erased code.t)
  (f : unit -> stt unit (code.up pre) (fun _ -> code.up post))
  : stt handle (pool_alive #pf code p ** code.up pre)
               (fun h -> pool_alive #pf code p ** joinable p post h)

val pool_done (code:vcode) (p:pool code.t) : vprop

val disown
  (#code:vcode)
  (#p : pool code.t)
  (#post : erased code.t)
  (h : handle)
  : stt_ghost unit (joinable p post h)
                   (fun _ -> pledge [] (pool_done code p) (code.up post))

(* spawn + disown *)
val spawn_
  (#code:vcode)
  (p : pool code.t)
  (#pf : perm)
  (#pre : erased code.t)
  (#post : erased code.t)
  (f : unit -> stt unit (code.up pre) (fun _ -> code.up post))
  : stt unit (pool_alive #pf code p ** code.up pre)
             (fun _ -> pool_alive #pf code p ** pledge [] (pool_done code p) (code.up post))

val await
  (#code:vcode)
  (#p : pool code.t)
  (#post : erased code.t)
  (h : handle)
  (#f : perm)
  : stt unit (pool_alive #f code p ** joinable p post h)
             (fun _ -> pool_alive #f code p ** code.up post)

val await_pool
  (#code:vcode)
  (p:pool code.t)
  (#is:Pulse.Lib.InvList.invlist)
  (#f:perm)
  (q : vprop)
  : stt unit (pool_alive #f code p ** pledge is (pool_done code p) q)
             (fun _ -> pool_alive #f code p ** q)

val teardown_pool
  (#code:vcode)
  (p:pool code.t)
  : stt unit (pool_alive code p)
             (fun _ -> pool_done code p)

val setup_pool
  (#code:vcode)
  (n : pos)
  : stt (pool code.t)
         emp
         (fun p -> pool_alive code p)

val share_alive
  (#code:vcode)
  (p:pool code.t)
  (e:perm)
  : stt_ghost unit
              (pool_alive #e code p)
              (fun () -> pool_alive #(half_perm e) code p ** pool_alive #(half_perm e) code p)

val gather_alive
  (#code:vcode)
  (p:pool code.t)
  (e:perm)
  : stt_ghost unit
              (pool_alive #(half_perm e) code p ** pool_alive #(half_perm e) code p)
              (fun () -> pool_alive #e code p)
