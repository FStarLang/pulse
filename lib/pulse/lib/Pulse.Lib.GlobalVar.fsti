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

module Pulse.Lib.GlobalVar
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Class.Duplicable
open FStar.ExtractAs
open Pulse.Lib.Trade

val gvar (#a:Type0) (p:a -> slprop) : Type0

val mk_gvar
      (#a:Type0)
      (#p:a -> slprop) 
      {| (x:a -> duplicable (p x)) |}
      (init:unit -> stt a emp (fun x -> p x))
: gvar p

val read_gvar_ghost (#a:Type0) (#p:a -> slprop) (x:gvar p) : GTot a

fn read_gvar (#a:Type0) (#p:a -> slprop) (x:gvar p)
  returns  r : a
  ensures  p r
  ensures  rewrites_to r (read_gvar_ghost x)
