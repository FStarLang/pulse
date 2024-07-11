(*
   Copyright REDACTED

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.Task

open Pulse.Lib.Pervasives
open Pulse.Lib.Pledge
module T = FStar.Tactics

val pool : Type0
val pool_alive : (#[T.exact (`1.0R)]p : perm) -> pool -> slprop
val pool_done : pool -> slprop

val setup_pool (n:pos)
  : stt pool emp (fun p -> pool_alive #1.0R p)

val task_handle : pool -> a:Type0 -> (a -> slprop) -> Type0
val joinable : #p:pool -> #a:Type0 -> #post:_ -> th:(task_handle p a post) -> slprop
val joined   : #p:pool -> #a:Type0 -> #post:_ -> th:(task_handle p a post) -> slprop

val handle_solved
  (#p : pool) 
  (#a : Type0)
  (#post : a -> slprop)
  (th : task_handle p a post)
  : slprop

(* NOTE! Spawn only requires an *epsilon* of permission over the pool.
We do not have to be exclusive owners of it in order to queue a job,
even if that modifies it. How to model this under the hood? *)
val spawn
  (#a : Type0)
  (#pre : slprop) (#post : a -> slprop)
  (p : pool)
  (#[T.exact (`1.0R)] e : perm)
  ($f : unit -> stt a pre (fun (x:a) -> post x))
  : stt (task_handle p a post)
        (pool_alive #e p ** pre)
        (fun th -> pool_alive #e p ** joinable th)

(* Spawn of a unit-returning task with no intention to join, simpler. *)
val spawn_
  (#pre #post : _)
  (p:pool)
  (#[T.exact (`1.0R)] e : perm)
  (f : unit -> stt unit pre (fun _ -> post))
  : stt unit (pool_alive #e p ** pre)
             (fun prom -> pool_alive #e p ** pledge emp_inames (pool_done p) post)

(* If the pool is done, all pending joinable threads must be done *)
val must_be_done
  (#p : pool)
  (#a: Type0)
  (#post : a -> slprop)
  (th : task_handle p a post)
  : stt_ghost unit emp_inames (pool_done p ** joinable th) (fun () -> pool_done p ** handle_solved th)

val join0
  (#p:pool)
  (#a:Type0)
  (#post : a -> slprop)
  (th : task_handle p a post)
  : stt unit (joinable th) (fun () -> handle_solved th)

val extract
  (#p:pool)
  (#a:Type0)
  (#post : a -> slprop)
  (th : task_handle p a post)
  : stt a (handle_solved th) (fun x -> post x)
  
val share_alive
  (p:pool)
  (e:perm)
  : stt_ghost unit
              emp_inames
              (pool_alive #e p)
              (fun () -> pool_alive #(e /. 2.0R) p ** pool_alive #(e /. 2.0R) p)

val gather_alive
  (p:pool)
  (e:perm)
  : stt_ghost unit
              emp_inames
              (pool_alive #(e /. 2.0R) p ** pool_alive #(e /. 2.0R) p)
              (fun () -> pool_alive #e p)

val join
  (#p:pool)
  (#a:Type0)
  (#post : a -> slprop)
  (th : task_handle p a post)
  : stt a (joinable th) (fun x -> post x)

(* We must exclusively own the pool in order to terminate it. *)
val teardown_pool
  (p:pool)
  : stt unit (pool_alive #1.0R p) (fun _ -> pool_done p)

(* Or, have at least an epsilon of permission over it, and know that
the rest of it (1-e) is "sunk" into the pool itself. *)
val teardown_pool'
  (#is:inames)
  (p:pool) (f:perm{f <. 1.0R})
  : stt unit (pool_alive #f p ** pledge is (pool_done p) (pool_alive #(1.0R -. f) p))
             (fun _ -> pool_done p)
