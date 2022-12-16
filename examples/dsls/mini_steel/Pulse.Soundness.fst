module Pulse.Soundness
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common
module Bind = Pulse.Soundness.Bind
module Frame = Pulse.Soundness.Frame
module STEquiv = Pulse.Soundness.STEquiv
module Return = Pulse.Soundness.Return

assume
val equiv_beta (g:R.env) 
               (x:R.var)
               (ty:R.term { RT.lookup_bvar g x == Some ty })
               (t:R.term {RT.ln' t 0})
  : GTot (RT.equiv g t
                     (R.mk_app (mk_abs ty (RT.close_term t x))
                               [mk_name x, R.Q_Explicit]))

    
#push-options "--query_stats --fuel 2 --ifuel 2 --z3rlimit_factor 10"
let rec soundness (f:stt_env)
                  (g:env)
                  (t:term)
                  (c:pure_comp)
                  (d:src_typing f g t c)
  : GTot (RT.typing (extend_env_l f g) (elab_src_typing d) (elab_pure_comp c))
         (decreases d)
  = let mk_t_abs (#u:universe)
                 (#ty:pure_term)
                 (t_typing:tot_typing f g ty (Tm_Type u) { t_typing << d })
                 (#body:term)
                 (#x:var { None? (lookup g x) })
                 (#c:pure_comp)
                 (body_typing:src_typing f ((x, Inl ty)::g) (open_term body x) c { body_typing << d })
      : GTot (RT.typing (extend_env_l f g)
                        (mk_abs (elab_pure ty) (RT.close_term (elab_src_typing body_typing) x))
                        (elab_pure (Tm_Arrow ty (close_pure_comp c x))))
      = let E t_typing = t_typing in
        let r_t_typing = soundness _ _ _ _ t_typing in
        let r_body_typing = soundness _ _ _ _ body_typing in
        mk_t_abs f g r_t_typing r_body_typing
    in
    match d with
    | T_Tot _ _ _ d -> d

    | T_Abs _ x ty u body c hint t_typing body_typing ->
      mk_t_abs t_typing body_typing    

    | T_STApp _ head formal res arg head_typing arg_typing ->
      let E arg_typing = arg_typing in
      let r_head = elab_src_typing head_typing in
      let r_arg = elab_pure arg in
      elab_pure_equiv arg_typing;
      let r_head_typing
        : RT.typing _ r_head (elab_pure (Tm_Arrow formal res))
        = soundness _ _ _ _ head_typing
      in
      let r_arg_typing = soundness _ _ _ _ arg_typing in
      elab_comp_open_commute res arg;
      RT.T_App _ _ _ (binder_of_t_q (elab_pure formal) R.Q_Explicit)
                     (elab_pure_comp res)
                     r_head_typing
                     r_arg_typing

    | T_Bind _ e1 e2 c1 c2 x c e1_typing t_typing e2_typing bc ->
      let r1_typing
        : RT.typing _ _ (elab_pure_comp c1)
        = soundness _ _ _ _ e1_typing
      in
      let r2_typing
        : RT.typing _ _ (elab_pure (Tm_Arrow (comp_res c1) (close_pure_comp c2 x)))
        = mk_t_abs t_typing e2_typing
      in
      let Bind_comp _ _ _ _ t2_typing y post2_typing = bc in
      assume (~ (x `Set.mem` freevars_comp c1));
      assume (ln_c c1 /\ ln_c c2 /\ ln_c c);
      Bind.elab_bind_typing f g _ _ _ x _ r1_typing _ r2_typing bc 
                            (tot_typing_soundness t2_typing)
                            (mk_t_abs_tot _ _ t2_typing post2_typing)

    | T_Frame _ e c frame frame_typing e_typing ->
      let r_e_typing = soundness _ _ _ _ e_typing in
      assume (ln_c c);
      Frame.elab_frame_typing f g _ _ frame frame_typing r_e_typing

    | T_Equiv _ e c c' e_typing equiv ->
      assume (ln_c c /\ ln_c c');
      let r_e_typing = soundness _ _ _ _ e_typing in 
      STEquiv.st_equiv_soundness _ _ _ _ equiv _ r_e_typing

    | T_Return _ e t u e_typing t_typing ->
      Return.elab_return_typing t_typing e_typing

    | T_ReturnNoEq _ e t u e_typing t_typing ->
      let e_typing = soundness _ _ _ _ e_typing in
      Return.elab_return_noeq_typing t_typing e_typing
      
    | _ -> admit()

let soundness_lemma
  (f:stt_env)
  (g:env)
  (t:term)
  (c:pure_comp)
  (d:src_typing f g t c)
  : Lemma (ensures RT.typing (extend_env_l f g)
                             (elab_src_typing d)
                             (elab_pure_comp c))
  = FStar.Squash.bind_squash
      #(src_typing f g t c)
      ()
      (fun dd -> FStar.Squash.return_squash (soundness f g t c d))
