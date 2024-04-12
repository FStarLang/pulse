module Pulse.Lib.InvTokens

open Pulse.Lib.Core

val inv_token : iref -> vprop -> Type u#4

val witness (i:iref) (#p:vprop)
  : stt_atomic (inv_token i p)
          emp_inames
          (inv i p)
          (fun _ -> inv i p)

val recall (#i:iref) (#p:vprop) (tok : inv_token i p)
  : stt_atomic unit
          emp_inames
          emp
          (fun _ -> inv i p)
