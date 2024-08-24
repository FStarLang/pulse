(*
   Copyright 2024 Microsoft Research

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

module Pulse.Class.Droppable

open Pulse.Lib.Core

class droppable (p : slprop) = {
  drop_f : unit -> stt unit p (fun _ -> emp);
}

inline_for_extraction
let drop (p : slprop) {| droppable p |} ()
  : stt unit p (fun _ -> emp) = drop_f #p ()

inline_for_extraction instance val droppable_emp : droppable emp
inline_for_extraction instance val droppable_pure (p: prop) : droppable (pure p)
inline_for_extraction instance val droppable_star (p q: slprop) {| droppable p |} {| droppable q |} : droppable (p ** q)

inline_for_extraction instance val droppable_inv (i : iname) (p : slprop) : droppable (inv i p)
