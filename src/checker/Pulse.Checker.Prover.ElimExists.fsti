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

module Pulse.Checker.Prover.ElimExists

open Pulse.Syntax
open Pulse.Typing

open Pulse.Checker.Base
open Pulse.Checker.Prover.Base

module T = FStar.Tactics.V2

val elim_exists (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt tm_slprop)
   : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' tm_slprop &
            continuation_elaborator g ctxt g' ctxt')

val elim_exists_pst (#preamble:_) (pst:prover_state preamble)
  : T.Tac (list (list Pprint.document) & pst':prover_state preamble { pst' `pst_extends` pst })
  ///\ pst'.unsolved == pst.unsolved })
