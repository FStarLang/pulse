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

module Pulse.Lib.CondVar

module M = Pulse.Lib.SpinLock (* Should be an actual OS mutex, but this is a model anyway... *)

open Pulse.Lib.Core

val cv (#p:vprop) (l : M.lock p) : Type u#0

val new_cv
        (#p : vprop)
        (l : M.lock p)
  : stt (cv l)
        (requires emp)
        (ensures fun _ -> emp)

val wait
        (#p : vprop)
        (#l : M.lock p)
        (cv : cv l)
  : stt unit
        (requires emp) //acquired l)
        (ensures fun _ -> emp) // acquired l)

val signal
        (#p : vprop)
        (#l : M.lock p)
        (cv : cv l)
  : stt unit
        (requires emp)
        (ensures fun _ -> emp)
