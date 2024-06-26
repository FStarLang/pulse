module Pulse.Class.Duplicable

open Pulse.Lib.Core

instance dup_inv (i : iref) (p : vprop)
  : duplicable (inv i p) = {
  dup_f = (fun () -> dup_inv i p);
}
