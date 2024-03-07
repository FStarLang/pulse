(*
   Copyright 2023 Microsoft Research

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

module Pulse.Lib.RSpinLock

open Pulse.Lib.Core
open Pulse.Class.Duplicable

val lock : Type u#0

val protects : lock -> vprop -> vprop

instance val duplicable_protects l p : duplicable (l `protects` p)

val new_lock
        (p:vprop)
  : stt lock
        (requires p)
        (ensures (fun l -> l `protects` p))

val acquire
        (#p:vprop)
        (l:lock)
  : stt unit 
        (requires l `protects` p)
        (ensures (fun _ -> p))

val release
        (#p:vprop)
        (l:lock)
  : stt unit
        (requires p ** l `protects` p)
        (ensures (fun _ -> emp))
