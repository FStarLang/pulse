module NuPool

open Pulse.Lib.Pervasives
open Pulse.Lib.Pledge
module T = FStar.Tactics.V2
open Pulse.Lib.Codeable

val handle : Type u#0
val pool ([@@@strictly_positive] code_t:Type u#2) : Type u#0
val pool_alive (#[T.exact (`1.0R)] f : perm) (code:vcode) (p:pool code.t) : vprop

val pool_alive_is_big (f:perm) (code:vcode) (p:pool code.t)
  : Lemma (is_big (pool_alive #f code p)) [SMTPat (pool_alive #f code p)]

(* Relating the pool to the code, without claiming any permission to it. See lock_alive0. *)
val pool_alive0 (code:vcode) (p:pool code.t) : vprop

val pool_alive0_is_big (code:vcode) (p:pool code.t)
  : Lemma (is_big (pool_alive0 code p)) [SMTPat (pool_alive0 code p)]

val joinable (#code_t:Type u#2) (p:pool code_t) (post:erased code_t) (h : handle) : vprop

val joinable_is_big
  (#code_t:Type u#2)
  (p : pool code_t)
  (post : erased code_t)
  (h : handle)
  : Lemma (is_big (joinable p post h)) [SMTPat (joinable p post h)]

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

val pool_done_is_big (code:vcode) (p:pool code.t)
  : Lemma (is_big (pool_done code p)) [SMTPat (pool_done code p)]

val disown
  (#code:vcode)
  (#p : pool code.t)
  (#post : erased code.t)
  (h : handle)
  : stt_ghost unit emp_inames
      (joinable p post h)
      (fun _ -> pledge emp_inames (pool_done code p) (code.up post))

(* spawn + disown *)
val spawn_
  (#code:vcode)
  (p : pool code.t)
  (#pf : perm)
  (#pre : erased code.t)
  (#post : erased code.t)
  (f : unit -> stt unit (code.up pre) (fun _ -> code.up post))
  : stt unit (pool_alive #pf code p ** code.up pre)
             (fun _ -> pool_alive #pf code p ** pledge emp_inames (pool_done code p) (code.up post))

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
  (#is:inames)
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
              emp_inames
              (pool_alive #e code p)
              (fun () -> pool_alive #(e /. 2.0R) code p ** pool_alive #(e /. 2.0R) code p)

val gather_alive
  (#code:vcode)
  (p:pool code.t)
  (e:perm)
  : stt_ghost unit
              emp_inames
              (pool_alive #(e /. 2.0R) code p ** pool_alive #(e /. 2.0R) code p)
              (fun () -> pool_alive #e code p)

(* From two pool_alives, the code must match *)
val pool_alive_inj_l
  (code1 code2 : vcode) (p : pool code1.t)
  (#_ : squash (code1.t == code2.t))
  (f1 f2 : perm)
  : stt_ghost unit
              emp_inames
              (pool_alive #f1 code1 p ** pool_alive #f2 code2 p)
              (fun _ -> pool_alive #f1 code1 p ** pool_alive #f2 code1 p)
val pool_alive_inj_r
  (code1 code2 : vcode) (p : pool code1.t)
  (#_ : squash (code1.t == code2.t))
  (f1 f2 : perm)
  : stt_ghost unit
              emp_inames
              (pool_alive #f1 code1 p ** pool_alive #f2 code2 p)
              (fun _ -> pool_alive #f1 code2 p ** pool_alive #f2 code2 p)

(* From pool_done + pool_alive, the codes must match *)
val pool_done_inj
  (code1 code2 : vcode) (p : pool code1.t)
  (#_ : squash (code1.t == code2.t))
  (f1 : perm)
  : stt_ghost unit
              emp_inames
              (pool_alive #f1 code1 p ** pool_done code2 p)
              (fun _ -> pool_alive #f1 code1 p ** pool_done code1 p)

val get_pool_alive0
  (#code : vcode) (p : pool code.t)
  (#f : perm)
  : stt_ghost unit
              emp_inames
              (pool_alive #f code p)
              (fun _ -> pool_alive #f code p ** pool_alive0 code p)

val pool_alive0_inj_l
  (code1 code2 : vcode) (p : pool code1.t)
  (#_:squash (code1.t == code2.t))
  (f1 : perm)
  : stt_ghost unit
              emp_inames
              (pool_alive #f1 code1 p ** pool_alive0 code2 p)
              (fun _ -> pool_alive #f1 code1 p ** pool_alive0 code1 p)

val pool_alive0_inj_r
  (code1 code2 : vcode) (p : pool code1.t)
  (#_:squash (code1.t == code2.t))
  (f1 : perm)
  : stt_ghost unit
              emp_inames
              (pool_alive #f1 code1 p ** pool_alive0 code2 p)
              (fun _ -> pool_alive #f1 code2 p ** pool_alive0 code2 p)

val pool_done0_inj_r
  (code1 code2 : vcode) (p : pool code1.t)
  (#_:squash (code1.t == code2.t))
  : stt_ghost unit
              emp_inames
              (pool_done code1 p ** pool_alive0 code2 p)
              (fun _ -> pool_done code2 p ** pool_alive0 code2 p)
