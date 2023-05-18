module Pulse.Checker.Framing
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
module P = Pulse.Syntax.Printer

val vprop_as_list (vp:term)
  : list term

val list_as_vprop (vps:list term) : term

noeq
type framing_failure = {
  unmatched_preconditions : list term;
  remaining_context : list term;
}

val check_vprop_equiv
  (g:env)
  (vp1 vp2:term)
  (vp1_typing:tot_typing g vp1 Tm_VProp)
  : T.Tac (vprop_equiv g vp1 vp2)


val try_frame_pre (#g:env)
                  (#t:st_term)
                  (#pre:term)
                  (pre_typing: tot_typing g pre Tm_VProp)
                  (#c:comp_st)
                  (t_typing: st_typing g t c)
  : T.Tac (either (c':comp_st { comp_pre c' == pre } &
                   st_typing g t c')
                  framing_failure)

val frame_empty (#g:env)
                (#pre:term)
                (pre_typing: tot_typing g pre Tm_VProp)
                (#u:universe)
                (#ty:term) 
                (ut:universe_of g ty u)
                (t:st_term)
                (c0:comp_st{ comp_pre c0 == Tm_Emp })
                (d:st_typing g t c0)
  : T.Tac (c:comp_st { comp_pre c == pre} &
           st_typing g t c)

