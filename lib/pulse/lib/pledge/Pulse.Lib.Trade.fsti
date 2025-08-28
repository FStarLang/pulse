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
#lang-pulse

open Pulse.Lib.Pervasives

module T = FStar.Tactics

[@@erasable]
let trade_f (#[T.exact (`emp_inames)] is: inames) (hyp: slprop) (#[T.exact (`emp)] extra: slprop) (concl: slprop) =
  stt_ghost unit is (requires extra ** hyp) (ensures fun _ -> concl)

val trade
  (#[T.exact (`emp_inames)] is:inames)
  ([@@@mkey] hyp:slprop)
  ([@@@mkey] concl:slprop)
  : slprop

unfold
let ( ==>* ) :
  (#[T.exact (`emp_inames)] is:inames) ->
  (hyp:slprop) ->
  (concl:slprop) ->
  slprop
  = fun #is -> trade #is

(* Specialized to no inames *)
unfold
let ( @==> ) :
  (hyp:slprop) ->
  (concl:slprop) ->
  slprop
  = trade #emp_inames

ghost
fn intro_trade
  (#[T.exact (`emp_inames)]is:inames)
  (hyp concl extra:slprop)
  (f_elim: unit -> trade_f #is hyp #extra concl)
  requires extra
  ensures trade #is hyp concl

val elim_trade
  (#[T.exact (`emp_inames)] is:inames)
  (hyp concl:slprop)
: stt_ghost unit is
    (trade #is hyp concl ** hyp)
    (fun _ -> concl)

ghost
fn trade_sub_inv
  (#is1:inames)
  (#is2:inames { inames_subset is1 is2 })
  (hyp concl:slprop)
  requires trade #is1 hyp concl
  ensures trade #is2 hyp concl

ghost
fn trade_map
  (#is : inames)
  (p q r : slprop)
  (f : unit -> stt_ghost unit emp_inames q (fun _ -> r))
  requires trade #is p q
  ensures  trade #is p r

ghost
fn trade_compose
  (#is : inames)
  (p q r : slprop)
  requires trade #is p q ** trade #is q r
  ensures  trade #is p r

ghost
fn rewrite_with_trade
  (p1 p2 : slprop)
  requires p1 ** pure (p1 == p2)
  ensures  p2 ** (p2 @==> p1)
