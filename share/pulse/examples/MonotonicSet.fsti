module MonotonicSet

open Pulse.Lib.Pervasives

module S = FStar.TSet

let s_insert #a (x:a) (s : S.set a) : S.set a =
  S.union (S.singleton x) s

[@@erasable]
new
val set (a:Type0) (p : a -> vprop) : Type0

val models (#a:Type0) (#p : a -> vprop)
            (c : set a p) (s : S.set a)
: vprop

val empty (#a:Type0) (p : a -> vprop) (_:unit)
  : stt (set a p)
        (requires emp)
        (ensures fun c -> c `models` S.empty)
        
val insert (#a:Type0) (#p : a -> vprop) (c : set a p) (x : a) (#s : erased (S.set a))
  : stt (set a p)
        (requires p x ** c `models` s)
        (ensures fun c' -> c' `models` s_insert x s)

val stable_is_in (#a:_) (#p:_) (x:a) (c : set a p) : vprop

val witness_mem (#a:Type0) (#p : a -> vprop) (c : set a p) (x : a) (#s : erased (S.set a))
  : stt_ghost unit
        (requires c `models` s ** pure (S.mem x s /\ True))
        (ensures fun _ -> c `models` s ** stable_is_in x c)

val recall_mem (#a:Type0) (#p : a -> vprop) (c : set a p) (x : a) (#s : erased (S.set a))
  : stt_ghost unit
        (requires c `models` s ** stable_is_in x c)
        (ensures fun _ -> c `models` s ** pure (S.mem x s /\ True))

val operate_under (#a:Type0) (#p : a -> vprop) (c : set a p) (x : a) (#s : erased (S.set a))
            (#pre #post : vprop)
            (f : unit -> stt_ghost unit (p x ** pre) (fun _ -> p x ** post))
  : stt_ghost unit
        (requires c `models` s ** pure (S.mem x s /\ True) ** pre)
        (ensures fun _ -> c `models` s ** post)
