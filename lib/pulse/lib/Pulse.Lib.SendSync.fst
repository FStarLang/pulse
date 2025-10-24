module Pulse.Lib.SendSync
open Pulse.Lib.Core
open Pulse.Class.Duplicable
open Pulse.Main
#lang-pulse

ghost fn dup_in_same_process p () : duplicable_f (in_same_process p) = {
  unfold in_same_process p;
  loc_dup _;
  fold in_same_process p;
  fold in_same_process p;
}

instance duplicable_in_same_process p : duplicable (in_same_process p) =
  { dup_f = dup_in_same_process p }

let can_see_writes_from (other_loc: loc_id) : slprop =
  in_same_process other_loc **
    emp // extra assumptions

ghost fn can_see_writes_from_prop other_loc
  preserves can_see_writes_from other_loc
  ensures in_same_process other_loc
{
  unfold can_see_writes_from other_loc;
  dup (in_same_process other_loc) ();
  fold can_see_writes_from other_loc;
}

ghost fn writes_visible_in_prop other_loc
  preserves writes_visible_in other_loc
  ensures in_same_process other_loc
{
  unfold writes_visible_in other_loc;
  with l. assert loc l; loc_dup l;
  ghost_impersonate other_loc
    (on other_loc (can_see_writes_from l))
    (on other_loc (can_see_writes_from l) ** pure (process_of other_loc == process_of l))
    fn _ {
      on_elim (can_see_writes_from l);
      can_see_writes_from_prop l;
      on_intro (can_see_writes_from l);
      unfold in_same_process l;
      loc_gather other_loc #_;
    };
  fold in_same_process other_loc;
  fold writes_visible_in other_loc;
}


[@@deprecated "UNSAFE"]
ghost fn unsafe_attest_can_see_writes_from (other_loc: loc_id)
    pre post (k: unit -> stt_ghost unit emp_inames (can_see_writes_from other_loc ** pre)
      (fun _ -> can_see_writes_from other_loc ** post))
  preserves in_same_process other_loc
  requires pre
  ensures post
{
  dup (in_same_process other_loc) ();
  fold can_see_writes_from other_loc;
  k ();
  drop_ (can_see_writes_from other_loc);
}

[@@deprecated "UNSAFE"]
ghost fn unsafe_attest_writes_visible_in (other_loc: loc_id)
    pre post (k: unit -> stt_ghost unit emp_inames (writes_visible_in other_loc ** pre)
      (fun _ -> writes_visible_in other_loc ** post))
  preserves in_same_process other_loc
  requires pre
  ensures post
{
  unfold in_same_process other_loc;
  with l. assert loc l;
  on_intro pre;
  ghost_impersonate other_loc (on l pre) (on l post) fn _ {
    loc_dup other_loc;
    fold in_same_process l;
    unsafe_attest_can_see_writes_from l (loc other_loc ** on l pre) (loc other_loc ** on l post) fn _ {
      on_intro (can_see_writes_from l);
      ghost_impersonate l
          (on other_loc (can_see_writes_from l) ** on l pre)
          (on other_loc (can_see_writes_from l) ** on l post)
          fn _ {
        loc_dup l;
        fold writes_visible_in other_loc;
        on_elim pre;
        k ();
        on_intro post;
        unfold writes_visible_in other_loc;
        loc_gather l #_;
      };
      on_elim (can_see_writes_from l);
    };
    drop_ (in_same_process l);
  };
  on_elim post;
  fold in_same_process other_loc;
}

ghost fn is_send_acq (p: slprop) {| inst: is_send p |} (other_loc: loc_id)
  preserves can_see_writes_from other_loc
  requires on other_loc p
  ensures p
{
  inst other_loc;
}

ghost fn is_send_rel (p: slprop) {| is_send p |} (other_loc: loc_id)
  preserves writes_visible_in other_loc
  requires p
  ensures on other_loc p
{
  unfold writes_visible_in;
  with l. assert loc l;
  on_intro p;
  ghost_impersonate other_loc
    (on other_loc (can_see_writes_from l) ** on l p)
    (on other_loc (can_see_writes_from l) ** on other_loc p)
    fn _ {
      on_elim (can_see_writes_from l);
      is_send_acq p l;
      on_intro p;
      on_intro (can_see_writes_from l);
    };
  fold writes_visible_in other_loc;
}

[@@deprecated "UNSAFE"]
ghost fn unsafe_attest_released (p: slprop) {| is_send p |} (#l:loc_id)
  preserves loc l
  requires p
  ensures on (process_of l) p
{
  loc_dup l;
  fold in_same_process (process_of l);
  unsafe_attest_writes_visible_in (process_of l) p (on (process_of l) p)
    fn _ { is_send_rel p (process_of l) };
  unfold in_same_process (process_of l);
  loc_gather l #_;
}

[@@deprecated "UNSAFE"]
ghost fn unsafe_attest_acquired (p: slprop) {| is_send p |} (#l:loc_id)
  preserves loc l
  requires on (process_of l) p
  ensures p
{
  loc_dup l;
  fold in_same_process (process_of l);
  unsafe_attest_can_see_writes_from (process_of l) (on (process_of l) p) p
    fn _ { is_send_acq p (process_of l) };
  unfold in_same_process (process_of l);
  loc_gather l #_;
}

ghost fn on_star_elim #l (p q: slprop)
  requires on l (p ** q)
  ensures on l p
  ensures on l q
{
  ghost_impersonate l (on l (p ** q)) (on l p ** on l q) fn _ {
    on_elim (p ** q);
    on_intro p;
    on_intro q;
  }
}

ghost fn on_star_intro #l (p q: slprop)
  requires on l p
  requires on l q
  ensures on l (p ** q)
{
  ghost_impersonate l (on l p ** on l q) (on l (p ** q)) fn _ {
    on_elim p;
    on_elim q;
    on_intro (p ** q);
  }
}

ghost fn on_exists_elim u#a #l (#a: Type u#a) (p: a -> slprop)
  requires on l (exists* x. p x)
  ensures exists* x. on l (p x)
{
  ghost_impersonate l (on l (exists* x. p x)) (exists* x. on l (p x)) fn _ {
    on_elim (exists* x. p x);
    on_intro (p _);
  }
}

ghost fn is_send_placeless p {| inst: placeless p |} : is_send p = l {
  loc_get (); with l0. assert loc l0;
  inst l l0;
  on_elim p;
  drop_ (loc l0);
}

ghost fn is_send_star p q {| is_send p, is_send q |} : is_send (p ** q) = l {
  on_star_elim p q;
  is_send_acq p l;
  is_send_acq q l;
}

ghost fn is_send_exists' u#a (#a: Type u#a) (p: a->slprop) {| ((x:a) -> is_send (p x)) |} :
    is_send (exists* x. p x) = l {
  on_exists_elim p;
  with x. assert on l (p x);
  is_send_acq (p x) l;
}
let is_send_exists p = is_send_exists' p

ghost fn is_sync_elim p {| inst: is_sync p |} #l l'
  requires on l p
  requires pure (process_of l == process_of l')
  ensures on l' p
{
  inst l l'
}

ghost fn is_sync_elim_on p {| is_sync p |} #l
  preserves in_same_process l
  requires on l p
  ensures p
{
  unfold in_same_process l;
  with l0. assert loc l0;
  is_sync_elim p l0;
  on_elim p;
  fold in_same_process l;
}

ghost fn is_sync_intro_on p {| is_sync p |} l
  preserves in_same_process l
  requires p
  ensures on l p
{
  unfold in_same_process l;
  with l0. assert loc l0;
  on_intro p;
  is_sync_elim p l;
  fold in_same_process l;
}

ghost fn is_sync_placeless p {| inst: placeless p |} : is_sync p = l l' {
  inst l l'
}

ghost fn is_sync_in_same_process p : is_sync (in_same_process p) = l l' {
  ghost_impersonate l
    (on l (in_same_process p))
    (on l' (in_same_process p))
    fn _ {
      on_elim (in_same_process p);
      unfold in_same_process p;
      loc_gather l #_;
      ghost_impersonate l' emp (on l' (in_same_process p)) fn _ {
        loc_dup l';
        fold in_same_process p;
        on_intro (in_same_process p);
      }
    }
}

ghost fn is_send_of_is_sync p {| is_sync p |} : is_send p = l {
  can_see_writes_from_prop l;
  unfold in_same_process l; with l0. assert loc l0;
  is_sync_elim p l0;
  on_elim p;
  drop_ (loc l0);
}

ghost fn is_sync_star p q {| is_sync p, is_sync q |} : is_sync (p ** q) = l l' {
  on_star_elim p q;
  is_sync_elim p l';
  is_sync_elim q l';
  on_star_intro p q;
}

ghost fn is_sync_exists' u#a (#a: Type u#a) (p: a->slprop) {| ((x:a) -> is_sync (p x)) |} :
    is_sync (exists* x. p x) = l l' {
  ghost_impersonate l (on l (exists* x. p x)) (on l' (exists* x. p x)) fn _ {
    on_elim (exists* x. p x);
    with x. assert p x;
    on_intro (p x);
    is_sync_elim (p x) l';
    ghost_impersonate l' (on l' (p x)) (on l' (exists* x. p x)) fn _ {
      on_elim (p x);
      on_intro (exists* x. p x)
    };
  }
}
let is_sync_exists = is_sync_exists'


inline_for_extraction noextract fn fork'
  (pre:slprop) {| is_send pre |}
  (f: (unit -> stt unit pre (fun _ -> emp)))
  requires pre
{
  loc_get (); with l. assert loc l;
  unsafe_attest_released pre #_ #l;
  fork (on (process_of l) pre) #_ #l fn l' {
    unsafe_attest_acquired pre #_ #l';
    drop_ (loc l');
    f ();
  };
}