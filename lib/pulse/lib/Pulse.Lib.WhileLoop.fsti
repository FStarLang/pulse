module Pulse.Lib.WhileLoop
#lang-pulse

open Pulse.Main
open Pulse.Lib.Core

(* Not to be called directly. *)

fn while_loop
  (inv : bool -> slprop)
  (cond : stt bool (exists* x. inv x) (fun b -> inv b))
  (body : stt unit (inv true) (fun _ -> exists* x. inv x))
  requires exists* x. inv x
  ensures inv false

fn nuwhile_loop
  (inv : slprop)
  (cpost : bool -> slprop)
  (cond : stt bool inv (fun b -> cpost b))
  (body : stt unit (cpost true) (fun _ -> inv))
  requires inv
  ensures  cpost false
