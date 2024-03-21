module Pulse.Lib.CoreRef

open Pulse.Lib.Pervasives
open PulseCore.FractionalPermission

val core_ref : Type0

val get_addr : #a:Type0 -> ref a -> core_ref

val same_ref (#f1 #f2 : perm) (#a #b : Type0) (r1 : ref a) (r2 : ref b)
  (v1 : a) (v2 : b)
  (_ : squash (get_addr r1 == get_addr r2))
  : stt_ghost unit
      (pts_to r1 #f1 v1 ** pts_to r2 #f2 v2)
      (fun _ -> pts_to r1 #f1 v1 ** pts_to r2 #f2 v2 ** pure (a == b /\ v1 === v2))
