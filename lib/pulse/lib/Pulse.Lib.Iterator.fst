module Pulse.Lib.Iterator
#lang-pulse
open Pulse
open Pulse.Lib.WithPure

inline_for_extraction
let iter_live_t t elt =
  t -> Seq.seq elt -> (elt -> slprop) -> slprop

inline_for_extraction
let iter_next_t #t #elt (iter_live : iter_live_t t elt) (iter_done : t -> slprop) =
  x:ref t -> #xs: erased (Seq.seq elt) -> #ps: (elt -> slprop) ->
    stt (option elt) (exists* (vx:t). x |-> vx ** iter_live vx xs ps) (fun res ->
      exists* (vx:t). x |-> vx ** (match res with
        | Some next -> with_pure (Seq.length xs > 0) fun _ -> 
          pure (next == Seq.head xs) ** ps next ** iter_live vx (Seq.tail xs) ps
        | None -> pure (Seq.length xs == 0) ** iter_done vx))

inline_for_extraction
let iter_stop_t #t #elt (iter_live : iter_live_t t elt) (iter_done : t -> slprop) =
  x:ref t -> #xs: erased (Seq.seq elt) -> #ps: (elt -> slprop) ->
    stt unit (exists* (vx:t). x |-> vx ** iter_live vx xs ps) (fun res ->
      exists* (vx:t). x |-> vx ** iter_done vx)

inline_for_extraction noextract
[@@FStar.Tactics.Typeclasses.fundeps [1]]
class iter (t: Type u#iter) (elt: Type u#elt) = {
  iter_live : ([@@@mkey] x: t) -> Seq.seq elt -> (elt -> slprop) -> slprop;
  iter_done : ([@@@mkey] x: t) -> slprop;
  iter_next : iter_next_t iter_live iter_done;
  iter_stop : iter_stop_t iter_live iter_done;
}

unfold let iter_live_ref #t #elt {| iter t elt |} (x: ref t) (xs: Seq.seq elt) (ps: elt -> slprop) =
  exists* (vx:t). x |-> vx ** iter_live vx xs ps

inline_for_extraction noextract
noeq type array_iter_t elt = {
  array_iter_t_arr : array elt;
  array_iter_t_perm : perm;
  array_iter_t_idx : SizeT.t;
  array_iter_t_len : SizeT.t;
}

unfold let array_iter_live #elt : iter_live_t (array_iter_t elt) elt =
  fun it xs ps ->
    exists* (xs_full: Seq.seq elt).
    it.array_iter_t_arr |-> Frac it.array_iter_t_perm xs_full **
    pure (forall i. ps i == emp) **
    pure (SizeT.v it.array_iter_t_idx + Seq.length xs == SizeT.v it.array_iter_t_len /\
      Seq.length xs_full == SizeT.v it.array_iter_t_len /\
      (forall (i: nat). i < Seq.length xs ==> Seq.index xs_full (SizeT.v it.array_iter_t_idx + i) == Seq.index xs i))

unfold let array_iter_done #elt : array_iter_t elt -> slprop =
  fun it ->
    exists* (xs_full: Seq.seq elt).
    it.array_iter_t_arr |-> Frac it.array_iter_t_perm xs_full

inline_for_extraction noextract
fn array_iter_next u#a (#elt: Type u#a) : iter_next_t (array_iter_live #elt) (array_iter_done #elt) = it #xs #ps {
  if ((!it).array_iter_t_idx `SizeT.lt` (!it).array_iter_t_len) {
    let next = ((!it).array_iter_t_arr).((!it).array_iter_t_idx);
    let vit = !it;
    it := { vit with array_iter_t_idx = vit.array_iter_t_idx `SizeT.add` 1sz };
    rewrite emp as ps next;
    Some next
  } else {
    None
  }
}

inline_for_extraction noextract
fn array_iter_stop u#a (#elt: Type u#a) : iter_stop_t (array_iter_live #elt) (array_iter_done #elt) = it #xs #ps {}

inline_for_extraction noextract
instance inst_array_iter elt : iter (array_iter_t elt) elt = {
  iter_live = array_iter_live;
  iter_done = array_iter_done;
  iter_next = array_iter_next;
  iter_stop = array_iter_stop;
}

type map_iter_t it 
