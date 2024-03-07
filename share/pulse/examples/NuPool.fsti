module NuPool

open Pulse.Lib.Pervasives
open Pulse.Lib.Par.Pledge

// val pool : Type u#0
// val pool_alive : pool -> vprop
// val pool_done : pool -> vprop

// val handle : p:pool -> post:vprop -> Type u#0
// val joinable (#p:pool) (#post:vprop) (h : handle p post) : vprop

// val setup : nat -> stt pool emp (fun p -> pool_alive p)

// val spawn
//     (p : pool)
//     (#pre : vprop)
//     (#post : vprop)
//     (f : unit -> stt unit pre (fun _ -> post))
//     : stt (handle p post) (pool_alive p) (fun h -> pool_alive p ** joinable h)

// val await
//     (#p : pool)
//     (#post : vprop)
//     (h : handle p post)
//     : stt unit (pool_alive p ** joinable h) (fun _ -> pool_alive p ** post)

// val disown
//     (#p : pool)
//     (#post : vprop)
//     (h : handle p post)
//     : stt unit (joinable h) (fun _ -> pledge [] (pool_done p) post)

// val await_pool'
//     (#f:perm)
//     (p : pool)
//     : stt unit (pool_alive #f p ** pledge [] (pool_done p) (pool_alive #(1-f) p))
//                (fun _ -> pool_done p)

// val await_pool
//     (p : pool)
//     (#f : perm)
//     : stt unit (pool_alive #f p ** pledge [] (pool_done p) q) (fun _ -> pool_alive #f p ** q)

// val deallocate_pool
//     (p : pool)
//     : stt unit (pool_done p) (fun _ -> emp)
