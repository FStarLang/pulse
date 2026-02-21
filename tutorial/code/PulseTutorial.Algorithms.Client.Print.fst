module PulseTutorial.Algorithms.Client.Print
open Pulse
#lang-pulse

assume val puts : string -> stt unit emp (fun _ -> emp)
assume val printf : string -> UInt32.t -> stt unit emp (fun _ -> emp)