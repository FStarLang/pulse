open Prims
let (while_cond_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.ppname ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            unit -> (unit, unit) Pulse_Typing.comp_typing_u)
  =
  fun g ->
    fun u ->
      fun x ->
        fun ty ->
          fun inv_body ->
            fun inv_typing ->
              Pulse_Typing_Metatheory_Base.admit_comp_typing g
                (Pulse_Typing.comp_while_cond x inv_body)
let (while_body_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.ppname ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            unit -> (unit, unit) Pulse_Typing.comp_typing_u)
  =
  fun g ->
    fun u ->
      fun x ->
        fun ty ->
          fun inv_body ->
            fun inv_typing ->
              Pulse_Typing_Metatheory_Base.admit_comp_typing g
                (Pulse_Typing.comp_while_body x inv_body)
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_opt ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.st_term ->
              Pulse_Checker_Base.check_t ->
                ((unit, unit, unit) Pulse_Checker_Base.checker_result_t,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun t ->
              fun check1 ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.While.fst"
                           (Prims.of_int (51)) (Prims.of_int (10))
                           (Prims.of_int (51)) (Prims.of_int (45)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.While.fst"
                           (Prims.of_int (51)) (Prims.of_int (48))
                           (Prims.of_int (130)) (Prims.of_int (70)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_Checker_Pure.push_context "while loop"
                          t.Pulse_Syntax_Base.range1 g))
                  (fun uu___ ->
                     (fun g1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.While.fst"
                                      (Prims.of_int (52)) (Prims.of_int (72))
                                      (Prims.of_int (52)) (Prims.of_int (78)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.While.fst"
                                      (Prims.of_int (51)) (Prims.of_int (48))
                                      (Prims.of_int (130))
                                      (Prims.of_int (70)))))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> t.Pulse_Syntax_Base.term1))
                             (fun uu___ ->
                                (fun uu___ ->
                                   match uu___ with
                                   | Pulse_Syntax_Base.Tm_While
                                       { Pulse_Syntax_Base.invariant = inv;
                                         Pulse_Syntax_Base.condition = cond;
                                         Pulse_Syntax_Base.condition_var =
                                           condition_var;
                                         Pulse_Syntax_Base.body3 = body;_}
                                       ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.While.fst"
                                                     (Prims.of_int (54))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (55))
                                                     (Prims.of_int (78)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.While.fst"
                                                     (Prims.of_int (52))
                                                     (Prims.of_int (81))
                                                     (Prims.of_int (130))
                                                     (Prims.of_int (70)))))
                                            (Obj.magic
                                               (Pulse_Checker_Pure.check_slprop
                                                  (Pulse_Checker_Pure.push_context
                                                     "invariant"
                                                     (Pulse_Syntax_Pure.term_range
                                                        inv) g1)
                                                  (Pulse_Syntax_Pure.tm_exists_sl
                                                     Pulse_Syntax_Pure.u0
                                                     (Pulse_Syntax_Base.mk_binder_ppname
                                                        Pulse_Typing.tm_bool
                                                        condition_var) inv)))
                                            (fun uu___1 ->
                                               (fun uu___1 ->
                                                  match uu___1 with
                                                  | Prims.Mkdtuple2
                                                      (ex_inv, inv_typing) ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (36)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (70)))))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 Pulse_Syntax_Pure.inspect_term
                                                                   ex_inv))
                                                           (fun uu___2 ->
                                                              (fun ex_inv_v
                                                                 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (70)))))
                                                                    (if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Pure.uu___is_Tm_ExistsSL
                                                                    ex_inv_v)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ex_inv))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "check_while: typechecked invariant "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    " is not an existential")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___2))
                                                                    uu___2)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ex_inv_v))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Pure.Tm_ExistsSL
                                                                    (u,
                                                                    {
                                                                    Pulse_Syntax_Base.binder_ty
                                                                    = ty;
                                                                    Pulse_Syntax_Base.binder_ppname
                                                                    = nm;
                                                                    Pulse_Syntax_Base.binder_attrs
                                                                    = uu___4;_},
                                                                    inv1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (70)))))
                                                                    (if
                                                                    (Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    ty
                                                                    Pulse_Typing.tm_bool))
                                                                    ||
                                                                    (Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_univ
                                                                    u
                                                                    Pulse_Syntax_Pure.u0))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    ty))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "While loop invariant exists but its witness type is "
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    ", expected bool")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (nm.Pulse_Syntax_Base.range))
                                                                    uu___5))
                                                                    uu___5)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    while_cond_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Pure.term_range
                                                                    inv) g1)
                                                                    u nm ty
                                                                    inv1 ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    while_cond_comp_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Pulse_Typing_Metatheory_Base.st_comp_typing_inversion
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Pure.term_range
                                                                    inv) g1)
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.comp_while_cond
                                                                    nm inv1))
                                                                    (FStar_Pervasives_Native.fst
                                                                    (Pulse_Typing_Metatheory_Base.comp_typing_inversion
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Pure.term_range
                                                                    inv) g1)
                                                                    (Pulse_Typing.comp_while_cond
                                                                    nm inv1)
                                                                    while_cond_comp_typing1))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (res_typing,
                                                                    cond_pre_typing,
                                                                    x,
                                                                    post_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Checker_Base.post_hint_from_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Pure.term_range
                                                                    inv) g1)
                                                                    (Pulse_Typing.comp_while_cond
                                                                    nm inv1)
                                                                    while_cond_comp_typing1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    while_cond_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_while_c"))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    ppname ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (check1
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "check_while_condition"
                                                                    cond.Pulse_Syntax_Base.range1
                                                                    g1)
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Typing.comp_while_cond
                                                                    nm inv1))
                                                                    ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    while_cond_hint)
                                                                    ppname
                                                                    cond))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "check_while_condition"
                                                                    cond.Pulse_Syntax_Base.range1
                                                                    g1)
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Typing.comp_while_cond
                                                                    nm inv1))
                                                                    while_cond_hint
                                                                    r ppname))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (cond1,
                                                                    cond_comp,
                                                                    cond_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.eq_comp
                                                                    cond_comp
                                                                    (Pulse_Typing.comp_while_cond
                                                                    nm inv1)
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    while_body_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Pure.term_range
                                                                    inv) g1)
                                                                    u nm ty
                                                                    inv1 ()))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    while_body_comp_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Typing_Metatheory_Base.st_comp_typing_inversion
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Pure.term_range
                                                                    inv) g1)
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.comp_while_body
                                                                    nm inv1))
                                                                    (FStar_Pervasives_Native.fst
                                                                    (Pulse_Typing_Metatheory_Base.comp_typing_inversion
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Pure.term_range
                                                                    inv) g1)
                                                                    (Pulse_Typing.comp_while_body
                                                                    nm inv1)
                                                                    while_body_comp_typing1))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (res_typing1,
                                                                    body_pre_typing,
                                                                    x1,
                                                                    post_typing1)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Checker_Base.post_hint_from_comp_typing
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "invariant"
                                                                    (Pulse_Syntax_Pure.term_range
                                                                    inv) g1)
                                                                    (Pulse_Typing.comp_while_body
                                                                    nm inv1)
                                                                    while_body_comp_typing1))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    while_post_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.debug
                                                                    g1
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    while_post_hint.Pulse_Typing.post))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.strcat
                                                                    "while_body post_hint: "
                                                                    (Prims.strcat
                                                                    uu___10
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_while_b"))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    ppname ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (12)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (check1
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "check_while_body"
                                                                    body.Pulse_Syntax_Base.range1
                                                                    g1)
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Typing.comp_while_body
                                                                    nm inv1))
                                                                    ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    while_post_hint)
                                                                    ppname
                                                                    body))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    (Pulse_Checker_Pure.push_context
                                                                    "check_while_body"
                                                                    body.Pulse_Syntax_Base.range1
                                                                    g1)
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    (Pulse_Typing.comp_while_body
                                                                    nm inv1))
                                                                    while_post_hint
                                                                    r ppname))
                                                                    uu___10)))
                                                                    uu___10)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body1,
                                                                    body_comp,
                                                                    body_typing)
                                                                    ->
                                                                    if
                                                                    Pulse_Syntax_Base.eq_comp
                                                                    body_comp
                                                                    (Pulse_Typing.comp_while_body
                                                                    nm inv1)
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (127)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Typing.T_While
                                                                    (g1,
                                                                    inv1,
                                                                    cond1,
                                                                    body1,
                                                                    (),
                                                                    cond_typing,
                                                                    body_typing)))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (109)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (127)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (109)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.match_comp_res_with_post_hint
                                                                    g1
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.STT)
                                                                    (Pulse_Syntax_Base.Tm_While
                                                                    {
                                                                    Pulse_Syntax_Base.invariant
                                                                    = inv1;
                                                                    Pulse_Syntax_Base.condition
                                                                    = cond1;
                                                                    Pulse_Syntax_Base.condition_var
                                                                    =
                                                                    Pulse_Syntax_Base.ppname_default;
                                                                    Pulse_Syntax_Base.body3
                                                                    = body1
                                                                    }))
                                                                    (Pulse_Typing.comp_while
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    inv1) d
                                                                    post_hint))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.try_frame_pre
                                                                    false g
                                                                    pre ()
                                                                    uu___11
                                                                    res_ppname))
                                                                    uu___11)))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Prover.prove_post_hint
                                                                    g pre
                                                                    uu___11
                                                                    post_hint
                                                                    t.Pulse_Syntax_Base.range1))
                                                                    uu___11)))
                                                                    uu___11))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    (Pulse_Typing.comp_while_body
                                                                    nm inv1)))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    body_comp))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Could not prove the inferred type of the while body matches the annotation\nInferred type = "
                                                                    (Prims.strcat
                                                                    uu___13
                                                                    "\nAnnotated type = "))
                                                                    (Prims.strcat
                                                                    x2 "\n")))))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    uu___13
                                                                    uu___12))))
                                                                    uu___12)))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___12))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___8))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    (Pulse_Typing.comp_while_cond
                                                                    nm inv1)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.While.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    cond_comp))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Could not prove that the inferred type of the while condition matches the annotation\nInferred type = "
                                                                    (Prims.strcat
                                                                    uu___10
                                                                    "\nAnnotated type = "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    uu___10
                                                                    uu___9))))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    FStar_Pervasives_Native.None
                                                                    uu___9))
                                                                    uu___9)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                uu___2)))
                                                 uu___1))) uu___))) uu___)