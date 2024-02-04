open Prims
type ('p, 'x, 't, 'u, 'post) post_hint_compatible = Obj.t
let (check_core :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun t ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Admit.fst"
                         (Prims.of_int (47)) (Prims.of_int (10))
                         (Prims.of_int (47)) (Prims.of_int (63)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Admit.fst"
                         (Prims.of_int (47)) (Prims.of_int (66))
                         (Prims.of_int (94)) (Prims.of_int (117)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Pulse_Typing_Env.push_context g "check_admit"
                        t.Pulse_Syntax_Base.range2))
                (fun uu___ ->
                   (fun g1 ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Admit.fst"
                                    (Prims.of_int (49)) (Prims.of_int (43))
                                    (Prims.of_int (49)) (Prims.of_int (49)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Admit.fst"
                                    (Prims.of_int (47)) (Prims.of_int (66))
                                    (Prims.of_int (94)) (Prims.of_int (117)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ -> t.Pulse_Syntax_Base.term1))
                           (fun uu___ ->
                              (fun uu___ ->
                                 match uu___ with
                                 | Pulse_Syntax_Base.Tm_Admit
                                     { Pulse_Syntax_Base.ctag = c;
                                       Pulse_Syntax_Base.u1 = uu___1;
                                       Pulse_Syntax_Base.typ = t1;
                                       Pulse_Syntax_Base.post3 = post;_}
                                     ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Admit.fst"
                                                   (Prims.of_int (51))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (51))
                                                   (Prims.of_int (17)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Admit.fst"
                                                   (Prims.of_int (51))
                                                   (Prims.of_int (20))
                                                   (Prims.of_int (94))
                                                   (Prims.of_int (117)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                Pulse_Typing_Env.fresh g1))
                                          (fun uu___2 ->
                                             (fun x ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Admit.fst"
                                                              (Prims.of_int (52))
                                                              (Prims.of_int (11))
                                                              (Prims.of_int (52))
                                                              (Prims.of_int (20)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Admit.fst"
                                                              (Prims.of_int (52))
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (94))
                                                              (Prims.of_int (117)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           Pulse_Syntax_Base.v_as_nv
                                                             x))
                                                     (fun uu___2 ->
                                                        (fun px ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (9)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (117)))))
                                                                (match 
                                                                   (post,
                                                                    post_hint)
                                                                 with
                                                                 | (FStar_Pervasives_Native.None,
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "could not find a post annotation on admit, please add one")
                                                                 | (FStar_Pervasives_Native.Some
                                                                    post1,
                                                                    FStar_Pervasives_Native.Some
                                                                    post2) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    post2.Pulse_Typing.post))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    post1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "found two post annotations on admit: "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " and "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    ", please remove one")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___2))
                                                                    uu___2))
                                                                 | (FStar_Pervasives_Native.Some
                                                                    post1,
                                                                    uu___2)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_universe
                                                                    g1 t1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (u,
                                                                    t_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    post1 px))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    post_opened
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Pure.check_tot_term
                                                                    (Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    (FStar_Pervasives_Native.fst
                                                                    px) t1)
                                                                    post_opened
                                                                    Pulse_Syntax_Base.tm_vprop))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post2,
                                                                    post_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (t1, u,
                                                                    (),
                                                                    post2,
                                                                    ())))))
                                                                    uu___4)))
                                                                    uu___3))
                                                                 | (uu___2,
                                                                    FStar_Pervasives_Native.Some
                                                                    post1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    post1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    post2 ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    x
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    post2.Pulse_Typing.post)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    "Impossible: unexpected freevar clash in Tm_Admit, please file a bug-report"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    ((post2.Pulse_Typing.ret_ty),
                                                                    (post2.Pulse_Typing.u),
                                                                    (),
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    post2.Pulse_Typing.post
                                                                    px), ())))))
                                                                    uu___3)))
                                                                (fun uu___2
                                                                   ->
                                                                   (fun res
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (117)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    res))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (t2, u,
                                                                    t_typing,
                                                                    post_opened,
                                                                    post_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (117)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Naming.close_term
                                                                    post_opened
                                                                    x))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    post1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (117)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = t2;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    = post1
                                                                    }))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun s ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (117)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.T_Admit
                                                                    (g1, s,
                                                                    c,
                                                                    (Pulse_Typing.STC
                                                                    (g1, s,
                                                                    x, (),
                                                                    (), ())))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (117)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Admit.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (99)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.match_comp_res_with_post_hint
                                                                    g1
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    c)
                                                                    (Pulse_Syntax_Base.Tm_Admit
                                                                    {
                                                                    Pulse_Syntax_Base.ctag
                                                                    = c;
                                                                    Pulse_Syntax_Base.u1
                                                                    =
                                                                    (s.Pulse_Syntax_Base.u);
                                                                    Pulse_Syntax_Base.typ
                                                                    =
                                                                    (s.Pulse_Syntax_Base.res);
                                                                    Pulse_Syntax_Base.post3
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }))
                                                                    (Pulse_Typing.comp_admit
                                                                    c s) d
                                                                    post_hint))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre
                                                                    g pre ()
                                                                    uu___3
                                                                    res_ppname))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.prove_post_hint
                                                                    g pre
                                                                    uu___3
                                                                    post_hint
                                                                    t2.Pulse_Syntax_Base.range1))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                          uu___2))) uu___2)))
                                uu___))) uu___)
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              ((unit, unit, unit) Pulse_Checker_Base.checker_result_t, 
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun t ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Admit.fst"
                         (Prims.of_int (105)) (Prims.of_int (21))
                         (Prims.of_int (105)) (Prims.of_int (27)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Admit.fst"
                         (Prims.of_int (105)) (Prims.of_int (3))
                         (Prims.of_int (110)) (Prims.of_int (56)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> t.Pulse_Syntax_Base.term1))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax_Base.Tm_Admit r ->
                          (match post_hint with
                           | FStar_Pervasives_Native.Some
                               { Pulse_Typing.g = uu___1;
                                 Pulse_Typing.ctag_hint =
                                   FStar_Pervasives_Native.Some ct;
                                 Pulse_Typing.ret_ty = uu___2;
                                 Pulse_Typing.u = uu___3;
                                 Pulse_Typing.ty_typing = uu___4;
                                 Pulse_Typing.post = uu___5;
                                 Pulse_Typing.x = uu___6;
                                 Pulse_Typing.post_typing_src = uu___7;
                                 Pulse_Typing.post_typing = uu___8;_}
                               ->
                               Obj.magic
                                 (check_core g pre () post_hint res_ppname
                                    {
                                      Pulse_Syntax_Base.term1 =
                                        (Pulse_Syntax_Base.Tm_Admit
                                           {
                                             Pulse_Syntax_Base.ctag = ct;
                                             Pulse_Syntax_Base.u1 =
                                               (r.Pulse_Syntax_Base.u1);
                                             Pulse_Syntax_Base.typ =
                                               (r.Pulse_Syntax_Base.typ);
                                             Pulse_Syntax_Base.post3 =
                                               (r.Pulse_Syntax_Base.post3)
                                           });
                                      Pulse_Syntax_Base.range2 =
                                        (t.Pulse_Syntax_Base.range2);
                                      Pulse_Syntax_Base.effect_tag =
                                        (t.Pulse_Syntax_Base.effect_tag)
                                    })
                           | uu___1 ->
                               Obj.magic
                                 (check_core g pre () post_hint res_ppname t)))
                     uu___)