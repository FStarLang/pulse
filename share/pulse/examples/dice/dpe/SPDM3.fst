module SPDM3
#lang-pulse

open Pulse.Lib.Pervasives
open PulseCore.Preorder

module G = FStar.Ghost

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

module V = Pulse.Lib.Vec
module FP = Pulse.Lib.PCM.FractionalPreorder
module L = FStar.List.Tot
module E = FStar.Endianness

open FStar.Mul
open Pulse.Lib.Pervasives
open DPETypes
open HACL
open EngineTypes
open EngineCore
open L0Types
open L0Core

module G = FStar.Ghost
module PCM = FStar.PCM
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module PP = PulseCore.Preorder
module PM = Pulse.Lib.PCMMap
module FP = Pulse.Lib.PCM.FractionalPreorder
module M = Pulse.Lib.MutexToken
module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module HT = Pulse.Lib.HashTable
module PHT = Pulse.Lib.HashTable.Spec

open PulseCore.Preorder
open Pulse.Lib.OnRange

// We assume a combinator to run pulse computations for initialization of top-level state, it gets primitive support in extraction
assume val run_stt (#a:Type) (#post:a -> slprop) (f:stt a emp post) : a

// We assume this code will be executed on a machine where u32 fits the word size
assume SZ_fits_u32 : SZ.fits_u32


fn initialize_global_state ()
  requires emp
   
  ensures emp
{
  admit()
}

let gst : (r:gref & mutex (dpe_inv r)) = run_stt (initialize_global_state ())
