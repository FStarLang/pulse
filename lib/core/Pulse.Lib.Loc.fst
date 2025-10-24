module Pulse.Lib.Loc

[@@erased]
noeq type loc_id = {
  process: nat;
  thread: nat;
}

let process_of l = { l with thread = 0 }
let process_of_idem l = ()

let dummy_loc = { process = 0; thread = 0 }