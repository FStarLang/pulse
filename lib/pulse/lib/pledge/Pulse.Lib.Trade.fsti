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

module Pulse.Lib.Trade

open Pulse.Lib.Core
open Pulse.Lib.Pervasives
open Pulse.Lib.InvList
module T = FStar.Tactics

val trade :
  (#[T.exact (`invlist_empty)] is : invlist) ->
  (hyp : vprop) ->
  (concl : vprop) ->
  vprop

let ( ==>* ) :
  (#[T.exact (`invlist_empty)] is : invlist) ->
  (hyp : vprop) ->
  (concl : vprop) ->
  vprop
  = fun #is -> trade #is

val intro_trade
  (#[T.exact (`invlist_empty)] is : invlist)
  (hyp concl: vprop)
  (extra: vprop)
  (f_elim: unit -> (
    stt_ghost unit
    (invlist_v is ** extra ** hyp)
    (fun _ -> invlist_v is ** concl)
  ))
: stt_ghost unit
    extra
    (fun _ -> trade #is hyp concl)

val elim_trade_ghost
  (#[T.exact (`invlist_empty)] is : invlist)
  (hyp concl: vprop)
: stt_ghost unit
    (invlist_v is ** (trade #is hyp concl) ** hyp)
    (fun _ -> invlist_v is ** concl)

val elim_trade
  (#[T.exact (`invlist_empty)] is : invlist)
  (hyp concl: vprop)
: stt_atomic unit #Unobservable (invlist_names is)
    ((trade #is hyp concl) ** hyp)
    (fun _ -> concl)

val trade_sub_inv
  (#os1 : invlist)
  (#os2 : invlist{invlist_sub os1 os2})
  (hyp concl: vprop)
: stt_ghost unit
    (trade #os1 hyp concl)
    (fun _ -> trade #os2 hyp concl)

val trade_map
  (#os : invlist)
  (p q r : vprop)
  (f : unit -> stt_ghost unit q (fun _ -> r))
: stt_ghost unit
    (trade #os p q)
    (fun _ -> trade #os p r)

val trade_compose
  (#os : invlist)
  (p q r : vprop)
: stt_ghost unit
    (trade #os p q ** trade #os q r)
    (fun _ -> trade #os p r)
