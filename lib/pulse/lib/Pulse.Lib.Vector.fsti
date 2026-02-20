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

(**
  A dynamically-resizable vector for Pulse.

  Doubles capacity on push_back when full.
  Halves capacity on pop_back when size == floor(capacity / 2).
  Backed by a flat array with a stored default value for unused slots.
*)

module Pulse.Lib.Vector

#lang-pulse

open Pulse.Lib.Pervasives
module Seq = FStar.Seq
module SZ = FStar.SizeT

/// Abstract vector type
val vector (t:Type0) : Type0

/// Predicate relating a vector to its logical contents and capacity
val is_vector (#t:Type0) ([@@@mkey]v:vector t) (s:Seq.seq t) (cap:SZ.t) : slprop

/// Create a new vector with n elements all set to default.
/// Capacity is initially n. Requires n > 0.
fn create (#t:Type0) (default:t) (n:SZ.t{SZ.v n > 0})
  returns v:vector t
  ensures is_vector v (Seq.create (SZ.v n) default) n

/// Read element at index i.
/// Requires: i < size
fn at (#t:Type0) (v:vector t) (i:SZ.t)
  (#s:erased (Seq.seq t){SZ.v i < Seq.length s}) (#cap:erased SZ.t)
  preserves is_vector v s cap
  returns x:t
  ensures pure (x == Seq.index s (SZ.v i))

/// Write element at index i.
/// Requires: i < size
fn set (#t:Type0) (v:vector t) (i:SZ.t) (x:t)
  (#s:erased (Seq.seq t){SZ.v i < Seq.length s}) (#cap:erased SZ.t)
  requires is_vector v s cap
  ensures is_vector v (Seq.upd s (SZ.v i) x) cap

/// Get the current number of elements
fn size (#t:Type0) (v:vector t) (#s:erased (Seq.seq t)) (#cap:erased SZ.t)
  preserves is_vector v s cap
  returns n:SZ.t
  ensures pure (SZ.v n == Seq.length s)

/// Get the current capacity
fn capacity (#t:Type0) (v:vector t) (#s:erased (Seq.seq t)) (#cap:erased SZ.t)
  preserves is_vector v s cap
  returns n:SZ.t
  ensures pure (n == cap)

/// Append element to end. Doubles capacity if full.
/// Precondition: either there is room, or doubling is representable.
fn push_back (#t:Type0) (v:vector t) (x:t)
  (#s:erased (Seq.seq t)) (#cap:erased SZ.t)
  requires is_vector v s cap **
           pure (Seq.length s < SZ.v cap \/ SZ.fits (SZ.v cap + SZ.v cap))
  ensures exists* (cap':SZ.t).
    is_vector v (Seq.snoc s x) cap' **
    pure (SZ.v cap' >= Seq.length s + 1 /\ SZ.v cap' > 0 /\
          (Seq.length s < SZ.v cap ==> cap' == cap) /\
          (Seq.length s == SZ.v cap ==> SZ.v cap' == SZ.v cap + SZ.v cap))

/// Remove and return the last element. Halves capacity when size == floor(cap/2).
/// Requires: vector is non-empty
fn pop_back (#t:Type0) (v:vector t)
  (#s:erased (Seq.seq t){Seq.length s > 0}) (#cap:erased SZ.t)
  requires is_vector v s cap
  returns x:t
  ensures exists* (cap':SZ.t).
    is_vector v (Seq.slice s 0 (Seq.length s - 1)) cap' **
    pure (x == Seq.index s (Seq.length s - 1) /\
          SZ.v cap' >= Seq.length s - 1 /\ SZ.v cap' > 0 /\
          (Seq.length s - 1 == SZ.v cap / 2 /\ SZ.v cap / 2 > 0
             ==> SZ.v cap' == SZ.v cap / 2) /\
          (~(Seq.length s - 1 == SZ.v cap / 2 /\ SZ.v cap / 2 > 0)
             ==> cap' == cap))

/// Resize the vector to new_size elements.
/// Preserves the first min(old_size, new_size) elements.
fn resize (#t:Type0) (v:vector t) (new_size:SZ.t{SZ.v new_size > 0})
  (#s:erased (Seq.seq t)) (#cap:erased SZ.t)
  requires is_vector v s cap
  ensures exists* (s':Seq.seq t) (cap':SZ.t).
    is_vector v s' cap' **
    pure (Seq.length s' == SZ.v new_size /\
          SZ.v cap' >= SZ.v new_size /\ SZ.v cap' > 0 /\
          (forall (i:nat). i < Seq.length s /\ i < SZ.v new_size ==>
            Seq.index s' i == Seq.index s i))

/// Free the vector and its backing storage
fn free (#t:Type0) (v:vector t) (#s:erased (Seq.seq t)) (#cap:erased SZ.t)
  requires is_vector v s cap
