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
#lang-pulse

open Pulse.Lib.Core
module _ = Pulse.Main // required for --ide?

inline_for_extraction fn drop_emp () requires emp ensures emp { () }
inline_for_extraction instance droppable_emp : droppable emp =
  { drop_f = drop_emp }

inline_for_extraction fn drop_pure p () requires pure p ensures emp { () }
inline_for_extraction instance droppable_pure (p: prop) : droppable (pure p) =
  { drop_f = drop_pure p }

inline_for_extraction fn drop_star (p q: slprop) {| droppable p |} {| droppable q |} ()
  requires p ** q
  ensures emp
{
  drop p ();
  drop q ();
}
inline_for_extraction instance droppable_star (p q: slprop) {| droppable p |} {| droppable q |} : droppable (p ** q) =
  { drop_f = drop_star p q }

inline_for_extraction fn drop_inv i p () requires inv i p ensures emp { drop_ (inv i p) }
inline_for_extraction instance droppable_inv (i : iname) (p : slprop) : droppable (inv i p) =
  { drop_f = drop_inv i p }
