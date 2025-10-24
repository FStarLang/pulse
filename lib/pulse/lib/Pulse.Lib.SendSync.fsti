module Pulse.Lib.SendSync
open Pulse.Lib.Core
open Pulse.Class.Duplicable
open Pulse.Main
#lang-pulse

let in_same_process p = exists* l. loc l ** pure (process_of l == process_of p)
instance val duplicable_in_same_process p : duplicable (in_same_process p)

val can_see_writes_from (other_loc: loc_id) : slprop
let writes_visible_in (other_loc: loc_id) =
  exists* l. loc l ** on other_loc (can_see_writes_from l)

ghost fn can_see_writes_from_prop other_loc
  preserves can_see_writes_from other_loc
  ensures in_same_process other_loc

ghost fn writes_visible_in_prop other_loc
  preserves writes_visible_in other_loc
  ensures in_same_process other_loc

[@@deprecated "UNSAFE"]
ghost fn unsafe_attest_can_see_writes_from (other_loc: loc_id)
    pre post (k: unit -> stt_ghost unit emp_inames (can_see_writes_from other_loc ** pre)
      (fun _ -> can_see_writes_from other_loc ** post))
  preserves in_same_process other_loc
  requires pre
  ensures post

[@@deprecated "UNSAFE"]
ghost fn unsafe_attest_writes_visible_in (other_loc: loc_id)
    pre post (k: unit -> stt_ghost unit emp_inames (writes_visible_in other_loc ** pre)
      (fun _ -> writes_visible_in other_loc ** post))
  preserves in_same_process other_loc
  requires pre
  ensures post

[@@Tactics.Typeclasses.tcclass; erasable]
type is_send (p: slprop) =
  other_loc: loc_id ->
    stt_ghost unit emp_inames
      (can_see_writes_from other_loc ** on other_loc p)
      (fun _ -> can_see_writes_from other_loc ** p)

ghost fn is_send_acq (p: slprop) {| is_send p |} (other_loc: loc_id)
  preserves can_see_writes_from other_loc
  requires on other_loc p
  ensures p

ghost fn is_send_rel (p: slprop) {| is_send p |} (other_loc: loc_id)
  preserves writes_visible_in other_loc
  requires p
  ensures on other_loc p

[@@deprecated "UNSAFE"]
ghost fn unsafe_attest_released (p: slprop) {| is_send p |} (#l:loc_id)
  preserves loc l
  requires p
  ensures on (process_of l) p

[@@deprecated "UNSAFE"]
ghost fn unsafe_attest_acquired (p: slprop) {| is_send p |} (#l:loc_id)
  preserves loc l
  requires on (process_of l) p
  ensures p

instance val is_send_placeless p {| placeless p |} : is_send p
instance val is_send_star p q {| is_send p, is_send q |} : is_send (p ** q)
instance val is_send_exists #a (p: a->slprop) {| ((x:a) -> is_send (p x)) |} : is_send (exists* x. p x)

[@@Tactics.Typeclasses.tcclass; erasable]
type is_sync (p: slprop) =
  l:loc_id -> l':loc_id { process_of l == process_of l' } ->
    stt_ghost unit emp_inames (on l p) (fun _ -> on l' p)

ghost fn is_sync_elim p {| inst: is_sync p |} #l l'
  requires on l p
  requires pure (process_of l == process_of l')
  ensures on l' p

ghost fn is_sync_elim_on p {| is_sync p |} #l
  preserves in_same_process l
  requires on l p
  ensures p

ghost fn is_sync_intro_on p {| is_sync p |} l
  preserves in_same_process l
  requires p
  ensures on l p

instance val is_sync_placeless p {| inst: placeless p |} : is_sync p
instance val is_sync_in_same_process p : is_sync (in_same_process p)
instance val is_send_of_is_sync p {| is_sync p |} : is_send p
instance val is_sync_star p q {| is_sync p, is_sync q |} : is_sync (p ** q)
instance val is_sync_exists #a (p: a->slprop) {| ((x:a) -> is_sync (p x)) |} :
  is_sync (exists* x. p x)

inline_for_extraction noextract fn fork'
  (pre:slprop) {| is_send pre |}
  (f: (unit -> stt unit pre (fun _ -> emp)))
  requires pre