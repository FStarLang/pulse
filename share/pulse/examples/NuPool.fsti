module NuPool

open Pulse.Lib.Pervasives
open Pulse.Lib.Par.Pledge
module T = FStar.Tactics.V2

noeq
type vcode : Type u#3 = {
    t : Type u#2;
    up : t -> vprop;
}

val handle : Type u#0


val pool (code:vcode) : Type u#0
val pool_alive (#[T.exact (`full_perm)] f : perm) (#code:vcode) (p:pool code) : vprop

val joinable (#code:vcode) (p:pool code) (post:erased code.t) (h : handle) : vprop

val spawn
  (#code:vcode)
  (p : pool code)
  (#pf : perm)
  (#pre : erased code.t)
  (#post : erased code.t)
  (f : unit -> stt unit (code.up pre) (fun _ -> code.up post))
  : stt handle (pool_alive #pf p ** code.up pre)
               (fun h -> pool_alive #pf p ** joinable p post h)

val pool_done (#code:vcode) (p:pool code) : vprop

val disown
  (#code:vcode)
  (#p : pool code)
  (#post : erased code.t)
  (h : handle)
  : stt_ghost unit (joinable p post h)
                   (fun _ -> pledge [] (pool_done p) (code.up post))

(* spawn + disown *)
val spawn_
  (#code:vcode)
  (p : pool code)
  (#pf : perm)
  (#pre : erased code.t)
  (#post : erased code.t)
  (f : unit -> stt unit (code.up pre) (fun _ -> code.up post))
  : stt unit (pool_alive #pf p ** code.up pre)
             (fun _ -> pool_alive #pf p ** pledge [] (pool_done p) (code.up post))

val await
  (#code:vcode)
  (#p : pool code)
  (#post : erased code.t)
  (h : handle)
  (#f : perm)
  : stt unit (pool_alive #f p ** joinable p post h)
             (fun _ -> pool_alive #f p ** code.up post)

val await_pool
  (#code:vcode)
  (p:pool code)
  (#f:perm)
  (q : vprop)
  : stt unit (pool_alive #f p ** pledge [] (pool_done p) q)
             (fun _ -> pool_alive #f p ** q)

val teardown_pool
  (#code:vcode)
  (p:pool code)
  (#f:perm)
  : stt unit (pool_alive #f p)
             (fun _ -> pool_done p)

val setup : (#code:vcode) -> nat -> stt (pool code) emp (fun p -> pool_alive p)
