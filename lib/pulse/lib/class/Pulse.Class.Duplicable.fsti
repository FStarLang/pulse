module Pulse.Class.Duplicable

open Pulse.Lib.Core

class duplicable (p : vprop) = {
  dup_f : unit -> stt_ghost unit p (fun _ -> p ** p);
}

let dup (p : vprop) {| d : duplicable p |} ()
  : stt_ghost unit p (fun _ -> p ** p) = d.dup_f ()
