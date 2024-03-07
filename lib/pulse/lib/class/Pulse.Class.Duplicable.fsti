module Pulse.Class.Duplicable

open Pulse.Lib.Core

class duplicable (p : vprop) = {
  dup : unit -> stt_ghost unit p (fun _ -> p ** p);
}
