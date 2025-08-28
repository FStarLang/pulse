(*
   Copyright 2025 Microsoft Research

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

module Pulse.Checker.ImpureSpec
module T = FStar.Tactics.V2
open Pulse.Syntax.Base
open Pulse.Syntax.Pure
open Pulse.Typing

noeq type ctxt = {
  ctxt_now: slprop;
  ctxt_old: option slprop;
}

val purify_spec (g: env) (ctxt: ctxt) (t: slprop) :
  T.Tac slprop

val purify_and_check_spec (g: env) (ctxt: ctxt) (t: slprop) :
  T.Tac (t:slprop & tot_typing g t tm_slprop)