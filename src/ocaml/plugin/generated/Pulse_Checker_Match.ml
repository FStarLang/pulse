open Prims
let rec (readback_pat :
  FStar_Reflection_V2_Data.pattern ->
    Pulse_Syntax_Base.pattern FStar_Pervasives_Native.option)
  =
  fun p ->
    match p with
    | FStar_Reflection_V2_Data.Pat_Cons (fv, uu___, args) ->
        let fv1 = FStar_Reflection_V2_Builtins.inspect_fv fv in
        Pulse_Syntax_Pure.op_let_Question
          (Pulse_Common.map_opt_dec p readback_sub_pat args)
          (fun args1 ->
             FStar_Pervasives_Native.Some
               (Pulse_Syntax_Base.Pat_Cons
                  ({
                     Pulse_Syntax_Base.fv_name = fv1;
                     Pulse_Syntax_Base.fv_range = FStar_Range.range_0
                   }, args1)))
    | FStar_Reflection_V2_Data.Pat_Constant c ->
        FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Pat_Constant c)
    | FStar_Reflection_V2_Data.Pat_Var (st, nm) ->
        FStar_Pervasives_Native.Some
          (Pulse_Syntax_Base.Pat_Var
             (nm,
               (Pulse_RuntimeUtils.map_seal st
                  Pulse_RuntimeUtils.deep_compress)))
    | FStar_Reflection_V2_Data.Pat_Dot_Term (FStar_Pervasives_Native.None) ->
        FStar_Pervasives_Native.Some
          (Pulse_Syntax_Base.Pat_Dot_Term FStar_Pervasives_Native.None)
    | FStar_Reflection_V2_Data.Pat_Dot_Term (FStar_Pervasives_Native.Some t)
        ->
        if
          FStar_Reflection_V2_Data.uu___is_Tv_Unknown
            (FStar_Reflection_V2_Builtins.inspect_ln t)
        then FStar_Pervasives_Native.None
        else
          (let t1 = Pulse_RuntimeUtils.deep_compress t in
           let t2 = Pulse_Syntax_Pure.wr t1 FStar_Range.range_0 in
           FStar_Pervasives_Native.Some
             (Pulse_Syntax_Base.Pat_Dot_Term
                (FStar_Pervasives_Native.Some t2)))
    | uu___ -> FStar_Pervasives_Native.None
and (readback_sub_pat :
  (FStar_Reflection_V2_Data.pattern * Prims.bool) ->
    (Pulse_Syntax_Base.pattern * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun pb ->
    let uu___ = pb in
    match uu___ with
    | (p, b) ->
        Pulse_Syntax_Pure.op_let_Question (readback_pat p)
          (fun p1 -> FStar_Pervasives_Native.Some (p1, b))

type ('b1, 'b2) samepat = unit
type ('bs1, 'bs2) samepats = unit
let (open_st_term_bs :
  Pulse_Syntax_Base.st_term ->
    Pulse_Typing_Env.binding Prims.list -> Pulse_Syntax_Base.st_term)
  =
  fun t ->
    fun bs ->
      let rec aux bs1 i =
        match bs1 with
        | [] -> []
        | b::bs2 ->
            (FStar_Reflection_Typing.DT
               (i,
                 (Pulse_Syntax_Pure.term_of_nvar
                    (Pulse_Syntax_Base.ppname_default,
                      (FStar_Pervasives_Native.fst b)))))
            :: (aux bs2 (i + Prims.int_one)) in
      let ss = aux (FStar_List_Tot_Base.rev bs) Prims.int_zero in
      Pulse_Syntax_Naming.subst_st_term t ss
let rec (r_bindings_to_string :
  FStar_Reflection_V2_Data.binding Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun bs ->
       match bs with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
       | b::bs1 ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (206)) (Prims.of_int (4))
                            (Prims.of_int (206)) (Prims.of_int (90)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (206)) (Prims.of_int (4))
                            (Prims.of_int (206)) (Prims.of_int (116)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Match.fst"
                                  (Prims.of_int (206)) (Prims.of_int (5))
                                  (Prims.of_int (206)) (Prims.of_int (22)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Match.fst"
                                  (Prims.of_int (206)) (Prims.of_int (4))
                                  (Prims.of_int (206)) (Prims.of_int (90)))))
                         (Obj.magic
                            (FStar_Tactics_Unseal.unseal
                               b.FStar_Reflection_V2_Data.ppname3))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Match.fst"
                                             (Prims.of_int (206))
                                             (Prims.of_int (25))
                                             (Prims.of_int (206))
                                             (Prims.of_int (89)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Match.fst"
                                                   (Prims.of_int (206))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (206))
                                                   (Prims.of_int (89)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Match.fst"
                                                         (Prims.of_int (206))
                                                         (Prims.of_int (54))
                                                         (Prims.of_int (206))
                                                         (Prims.of_int (89)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Match.fst"
                                                               (Prims.of_int (206))
                                                               (Prims.of_int (60))
                                                               (Prims.of_int (206))
                                                               (Prims.of_int (89)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "prims.fst"
                                                               (Prims.of_int (590))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (590))
                                                               (Prims.of_int (31)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (83)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                            (Obj.magic
                                                               (FStar_Tactics_V2_Builtins.term_to_string
                                                                  b.FStar_Reflection_V2_Data.sort3))
                                                            (fun uu___1 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___2
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___1
                                                                    " "))))
                                                      (fun uu___1 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___2 ->
                                                              Prims.strcat
                                                                ":" uu___1))))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat
                                                          (Prims.string_of_int
                                                             b.FStar_Reflection_V2_Data.uniq1)
                                                          uu___1))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat "-" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Match.fst"
                                       (Prims.of_int (206))
                                       (Prims.of_int (93))
                                       (Prims.of_int (206))
                                       (Prims.of_int (116)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "prims.fst"
                                       (Prims.of_int (590))
                                       (Prims.of_int (19))
                                       (Prims.of_int (590))
                                       (Prims.of_int (31)))))
                              (Obj.magic (r_bindings_to_string bs1))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> Prims.strcat uu___ uu___1))))
                        uu___)))) uu___
let rec (bindings_to_string :
  Pulse_Typing_Env.binding Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun bs ->
       match bs with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
       | b::bs1 ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (212)) (Prims.of_int (4))
                            (Prims.of_int (212)) (Prims.of_int (85)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                            (Prims.of_int (212)) (Prims.of_int (4))
                            (Prims.of_int (212)) (Prims.of_int (109)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Match.fst"
                                  (Prims.of_int (212)) (Prims.of_int (29))
                                  (Prims.of_int (212)) (Prims.of_int (84)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "prims.fst"
                                  (Prims.of_int (590)) (Prims.of_int (19))
                                  (Prims.of_int (590)) (Prims.of_int (31)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Match.fst"
                                        (Prims.of_int (212))
                                        (Prims.of_int (35))
                                        (Prims.of_int (212))
                                        (Prims.of_int (84)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "prims.fst"
                                        (Prims.of_int (590))
                                        (Prims.of_int (19))
                                        (Prims.of_int (590))
                                        (Prims.of_int (31)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Match.fst"
                                              (Prims.of_int (212))
                                              (Prims.of_int (35))
                                              (Prims.of_int (212))
                                              (Prims.of_int (78)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range "prims.fst"
                                              (Prims.of_int (590))
                                              (Prims.of_int (19))
                                              (Prims.of_int (590))
                                              (Prims.of_int (31)))))
                                     (Obj.magic
                                        (Pulse_Syntax_Printer.term_to_string
                                           (FStar_Pervasives_Native.snd b)))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 ->
                                             Prims.strcat uu___ " "))))
                               (fun uu___ ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 -> Prims.strcat ":" uu___))))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 Prims.strcat
                                   (Prims.string_of_int
                                      (FStar_Pervasives_Native.fst b)) uu___))))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Match.fst"
                                       (Prims.of_int (212))
                                       (Prims.of_int (88))
                                       (Prims.of_int (212))
                                       (Prims.of_int (109)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "prims.fst"
                                       (Prims.of_int (590))
                                       (Prims.of_int (19))
                                       (Prims.of_int (590))
                                       (Prims.of_int (31)))))
                              (Obj.magic (bindings_to_string bs1))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> Prims.strcat uu___ uu___1))))
                        uu___)))) uu___
let (check_branch :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Checker_Base.check_t ->
            Pulse_Syntax_Base.universe ->
              Pulse_Syntax_Base.typ ->
                Pulse_Syntax_Base.term ->
                  FStar_Reflection_V2_Data.pattern ->
                    Pulse_Syntax_Base.st_term ->
                      FStar_Reflection_V2_Data.binding Prims.list ->
                        ((Pulse_Syntax_Base.pattern,
                           Pulse_Syntax_Base.st_term,
                           Pulse_Syntax_Base.comp_st,
                           (unit, unit, unit, unit, unit, unit, unit)
                             Pulse_Typing.br_typing)
                           FStar_Pervasives.dtuple4,
                          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun check ->
            fun sc_u ->
              fun sc_ty ->
                fun sc ->
                  fun p0 ->
                    fun e ->
                      fun bs ->
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Match.fst"
                                   (Prims.of_int (233)) (Prims.of_int (10))
                                   (Prims.of_int (234)) (Prims.of_int (48)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Match.fst"
                                   (Prims.of_int (236)) (Prims.of_int (27))
                                   (Prims.of_int (272)) (Prims.of_int (58)))))
                          (match readback_pat p0 with
                           | FStar_Pervasives_Native.Some p ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___ -> p)))
                           | FStar_Pervasives_Native.None ->
                               Obj.magic
                                 (Obj.repr
                                    (Pulse_Typing_Env.fail g
                                       (FStar_Pervasives_Native.Some
                                          (e.Pulse_Syntax_Base.range1))
                                       "readback_pat failed")))
                          (fun uu___ ->
                             (fun p ->
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Match.fst"
                                              (Prims.of_int (237))
                                              (Prims.of_int (17))
                                              (Prims.of_int (237))
                                              (Prims.of_int (42)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Match.fst"
                                              (Prims.of_int (239))
                                              (Prims.of_int (54))
                                              (Prims.of_int (272))
                                              (Prims.of_int (58)))))
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___ ->
                                           FStar_List_Tot_Base.map
                                             Pulse_Typing.readback_binding bs))
                                     (fun uu___ ->
                                        (fun pulse_bs ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Match.fst"
                                                         (Prims.of_int (240))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (240))
                                                         (Prims.of_int (35)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Match.fst"
                                                         (Prims.of_int (240))
                                                         (Prims.of_int (38))
                                                         (Prims.of_int (272))
                                                         (Prims.of_int (58)))))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___ ->
                                                      Pulse_Typing.push_bindings
                                                        g pulse_bs))
                                                (fun uu___ ->
                                                   (fun g' ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (24)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (58)))))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___ ->
                                                                 Pulse_Typing_Env.fresh
                                                                   g'))
                                                           (fun uu___ ->
                                                              (fun hyp_var ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Reflection_Typing.elaborate_pat
                                                                    p0 bs))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    elab_p ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (58)))))
                                                                    (if
                                                                    Prims.op_Negation
                                                                    (FStar_Pervasives_Native.uu___is_Some
                                                                    elab_p)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e.Pulse_Syntax_Base.range1))
                                                                    "Failed to elab pattern into term"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun
                                                                    uu___ ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (58)))))
                                                                    (if
                                                                    FStar_Reflection_V2_Data.uu___is_Tv_Unknown
                                                                    (FStar_Reflection_V2_Builtins.inspect_ln
                                                                    (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    elab_p)))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (e.Pulse_Syntax_Base.range1))
                                                                    "should not happen: pattern elaborated to Tv_Unknown"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    elab_p)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    elab_p_tm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing.mk_sq_eq2
                                                                    sc_u
                                                                    sc_ty sc
                                                                    (Pulse_Syntax_Pure.wr
                                                                    elab_p_tm
                                                                    FStar_Range.range_0)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    eq_typ ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (106)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g'
                                                                    hyp_var
                                                                    {
                                                                    Pulse_Syntax_Base.name
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "branch equality");
                                                                    Pulse_Syntax_Base.range
                                                                    =
                                                                    FStar_Range.range_0
                                                                    } eq_typ))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun g'1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    open_st_term_bs
                                                                    e
                                                                    pulse_bs))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun e1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    {
                                                                    Pulse_Syntax_Base.term1
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_ProofHintWithBinders
                                                                    {
                                                                    Pulse_Syntax_Base.hint_type
                                                                    =
                                                                    (Pulse_Syntax_Base.RENAME
                                                                    {
                                                                    Pulse_Syntax_Base.pairs
                                                                    =
                                                                    [
                                                                    (sc,
                                                                    elab_p_tm)];
                                                                    Pulse_Syntax_Base.goal
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.tac_opt
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    });
                                                                    Pulse_Syntax_Base.binders
                                                                    = [];
                                                                    Pulse_Syntax_Base.t
                                                                    = e1
                                                                    });
                                                                    Pulse_Syntax_Base.range1
                                                                    =
                                                                    (e1.Pulse_Syntax_Base.range1);
                                                                    Pulse_Syntax_Base.effect_tag
                                                                    =
                                                                    (e1.Pulse_Syntax_Base.effect_tag)
                                                                    }))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun e2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    pre_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    pre_typing2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "_br"))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    ppname ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (check
                                                                    g'1 pre
                                                                    ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint)
                                                                    ppname e2))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g'1 pre
                                                                    post_hint
                                                                    r ppname))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e3, c,
                                                                    e_d) ->
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (p,
                                                                    (Pulse_Syntax_Naming.close_st_term_n
                                                                    e3
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.fst
                                                                    pulse_bs)),
                                                                    c,
                                                                    (Pulse_Typing.TBR
                                                                    (g, sc_u,
                                                                    sc_ty,
                                                                    sc, c, p,
                                                                    e3, bs,
                                                                    (), (),
                                                                    (),
                                                                    hyp_var,
                                                                    e_d)))))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___1)))
                                                                    uu___)))
                                                                    uu___)))
                                                                uu___)))
                                                     uu___))) uu___))) uu___)
type ('g, 'pre, 'postuhint, 'scuu, 'scuty, 'sc) check_branches_aux_t =
  (Pulse_Syntax_Base.branch, Pulse_Syntax_Base.comp_st,
    (unit, unit, unit, unit, unit, unit, unit) Pulse_Typing.br_typing)
    FStar_Pervasives.dtuple3
let (check_branches_aux :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Checker_Base.check_t ->
            Pulse_Syntax_Base.universe ->
              Pulse_Syntax_Base.typ ->
                Pulse_Syntax_Base.term ->
                  Pulse_Syntax_Base.branch Prims.list ->
                    (FStar_Reflection_V2_Data.pattern *
                      FStar_Reflection_V2_Data.binding Prims.list) Prims.list
                      ->
                      ((unit, unit, unit, unit, unit, unit)
                         check_branches_aux_t Prims.list,
                        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun check ->
            fun sc_u ->
              fun sc_ty ->
                fun sc ->
                  fun brs0 ->
                    fun bnds ->
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                                 (Prims.of_int (301)) (Prims.of_int (2))
                                 (Prims.of_int (301)) (Prims.of_int (50)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                                 (Prims.of_int (301)) (Prims.of_int (51))
                                 (Prims.of_int (311)) (Prims.of_int (3)))))
                        (if FStar_List_Tot_Base.isEmpty brs0
                         then
                           Obj.magic
                             (Obj.repr
                                (Pulse_Typing_Env.fail g
                                   FStar_Pervasives_Native.None "empty match"))
                         else
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 -> ()))))
                        (fun uu___ ->
                           (fun uu___ ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Match.fst"
                                            (Prims.of_int (304))
                                            (Prims.of_int (5))
                                            (Prims.of_int (307))
                                            (Prims.of_int (23)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Match.fst"
                                            (Prims.of_int (308))
                                            (Prims.of_int (4))
                                            (Prims.of_int (311))
                                            (Prims.of_int (3)))))
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 ->
                                         fun b ->
                                           fun pbs ->
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Match.fst"
                                                        (Prims.of_int (304))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (304))
                                                        (Prims.of_int (20)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Match.fst"
                                                        (Prims.of_int (304))
                                                        (Prims.of_int (5))
                                                        (Prims.of_int (307))
                                                        (Prims.of_int (23)))))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 -> b))
                                               (fun uu___2 ->
                                                  (fun uu___2 ->
                                                     match uu___2 with
                                                     | (uu___3, e) ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (23)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23)))))
                                                              (FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___4
                                                                    -> pbs))
                                                              (fun uu___4 ->
                                                                 (fun uu___4
                                                                    ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (p, bs)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    (check_branch
                                                                    g pre ()
                                                                    post_hint
                                                                    check
                                                                    sc_u
                                                                    sc_ty sc
                                                                    p e bs))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (p1, e1,
                                                                    c, d) ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    ((p1, e1),
                                                                    c, d)))))
                                                                   uu___4)))
                                                    uu___2)))
                                   (fun uu___1 ->
                                      (fun tr1 ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Match.fst"
                                                       (Prims.of_int (309))
                                                       (Prims.of_int (10))
                                                       (Prims.of_int (309))
                                                       (Prims.of_int (31)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Match.fst"
                                                       (Prims.of_int (309))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (309))
                                                       (Prims.of_int (7)))))
                                              (Obj.magic
                                                 (Pulse_Common.zipWith tr1
                                                    brs0 bnds))
                                              (fun r ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___1 -> r))))
                                        uu___1))) uu___)
let (comp_observability :
  Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.observability) =
  fun c ->
    let uu___ = c in
    match uu___ with
    | Pulse_Syntax_Base.C_STAtomic (uu___1, obs, uu___2) -> obs
let (ctag_of_br :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit Pulse_Typing.post_hint_for_env ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.typ ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit, unit, unit) check_branches_aux_t ->
                Pulse_Syntax_Base.ctag)
  =
  fun g ->
    fun pre ->
      fun post_hint ->
        fun sc_u ->
          fun sc_ty ->
            fun sc ->
              fun l ->
                let uu___ = l in
                match uu___ with
                | FStar_Pervasives.Mkdtuple3 (uu___1, c, uu___2) ->
                    Pulse_Syntax_Base.ctag_of_comp_st c
let (weaken_branch_observability :
  Pulse_Syntax_Base.observability ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.slprop ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Syntax_Base.universe ->
            Pulse_Syntax_Base.typ ->
              Pulse_Syntax_Base.term ->
                Pulse_Syntax_Base.comp_st ->
                  (unit, unit, unit, unit, unit, unit) check_branches_aux_t
                    ->
                    ((Pulse_Syntax_Base.branch,
                       (unit, unit, unit, unit, unit, unit, unit)
                         Pulse_Typing.br_typing)
                       Prims.dtuple2,
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun obs ->
    fun g ->
      fun pre ->
        fun post_hint ->
          fun sc_u ->
            fun sc_ty ->
              fun sc ->
                fun c ->
                  fun checked_br ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                               (Prims.of_int (334)) (Prims.of_int (29))
                               (Prims.of_int (334)) (Prims.of_int (39)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                               (Prims.of_int (334)) Prims.int_one
                               (Prims.of_int (344)) (Prims.of_int (5)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ -> checked_br))
                      (fun uu___ ->
                         match uu___ with
                         | FStar_Pervasives.Mkdtuple3 (br, c0, typing) ->
                             (match c0 with
                              | Pulse_Syntax_Base.C_STAtomic (i, obs', st) ->
                                  if
                                    Prims.op_Negation
                                      (Pulse_Typing.sub_observability obs'
                                         obs)
                                  then
                                    FStar_Tactics_V2_Derived.fail
                                      "Cannot weaken observability"
                                  else
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         match typing with
                                         | Pulse_Typing.TBR
                                             (g1, sc_u1, sc_ty1, sc1, c1, p,
                                              e, bs, p1, p2, p3, hyp,
                                              st_typing)
                                             ->
                                             Prims.Mkdtuple2
                                               (br,
                                                 (Pulse_Typing.TBR
                                                    (g1, sc_u1, sc_ty1, sc1,
                                                      (Pulse_Syntax_Base.C_STAtomic
                                                         ((Pulse_Syntax_Base.comp_inames
                                                             c1), obs,
                                                           (Pulse_Syntax_Base.st_comp_of_comp
                                                              c1))), p, e,
                                                      bs, (), (), (), hyp,
                                                      (Pulse_Typing.T_Lift
                                                         ((Pulse_Typing_Env.push_binding
                                                             (Pulse_Typing.push_bindings
                                                                g1
                                                                (FStar_List_Tot_Base.map
                                                                   Pulse_Typing.readback_binding
                                                                   bs)) hyp
                                                             {
                                                               Pulse_Syntax_Base.name
                                                                 =
                                                                 (FStar_Sealed.seal
                                                                    "branch equality");
                                                               Pulse_Syntax_Base.range
                                                                 =
                                                                 FStar_Range.range_0
                                                             }
                                                             (Pulse_Typing.mk_sq_eq2
                                                                sc_u1 sc_ty1
                                                                sc1
                                                                (Pulse_Syntax_Pure.wr
                                                                   (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    (FStar_Reflection_Typing.elaborate_pat
                                                                    (Pulse_Elaborate_Pure.elab_pat
                                                                    p) bs)))
                                                                   FStar_Range.range_0))),
                                                           e, c1,
                                                           (Pulse_Syntax_Base.C_STAtomic
                                                              ((Pulse_Syntax_Base.comp_inames
                                                                  c1), obs,
                                                                (Pulse_Syntax_Base.st_comp_of_comp
                                                                   c1))),
                                                           st_typing,
                                                           (Pulse_Typing.Lift_Observability
                                                              ((Pulse_Typing_Env.push_binding
                                                                  (Pulse_Typing.push_bindings
                                                                    g1
                                                                    (FStar_List_Tot_Base.map
                                                                    Pulse_Typing.readback_binding
                                                                    bs)) hyp
                                                                  {
                                                                    Pulse_Syntax_Base.name
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "branch equality");
                                                                    Pulse_Syntax_Base.range
                                                                    =
                                                                    FStar_Range.range_0
                                                                  }
                                                                  (Pulse_Typing.mk_sq_eq2
                                                                    sc_u1
                                                                    sc_ty1
                                                                    sc1
                                                                    (Pulse_Syntax_Pure.wr
                                                                    (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    (FStar_Reflection_Typing.elaborate_pat
                                                                    (Pulse_Elaborate_Pure.elab_pat
                                                                    p) bs)))
                                                                    FStar_Range.range_0))),
                                                                c1, obs))))))))))
let rec (max_obs :
  Pulse_Syntax_Base.comp_st Prims.list ->
    Pulse_Syntax_Base.observability -> Pulse_Syntax_Base.observability)
  =
  fun checked_brs ->
    fun obs ->
      match checked_brs with
      | [] -> obs
      | c'::rest ->
          (match c' with
           | Pulse_Syntax_Base.C_ST uu___ -> max_obs rest obs
           | Pulse_Syntax_Base.C_STGhost (uu___, uu___1) -> max_obs rest obs
           | Pulse_Syntax_Base.C_STAtomic (uu___, obs', uu___1) ->
               max_obs rest (Pulse_Typing.join_obs obs obs'))
let (join_branches :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit Pulse_Typing.post_hint_for_env ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.typ ->
            Pulse_Syntax_Base.term ->
              Pulse_Syntax_Base.ctag ->
                (unit, unit, unit, unit, unit, unit) check_branches_aux_t
                  Prims.list ->
                  ((Pulse_Syntax_Base.comp_st,
                     (Pulse_Syntax_Base.branch,
                       (unit, unit, unit, unit, unit, unit, unit)
                         Pulse_Typing.br_typing)
                       Prims.dtuple2 Prims.list)
                     Prims.dtuple2,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___7 ->
    fun uu___6 ->
      fun uu___5 ->
        fun uu___4 ->
          fun uu___3 ->
            fun uu___2 ->
              fun uu___1 ->
                fun uu___ ->
                  (fun g ->
                     fun pre ->
                       fun post_hint ->
                         fun sc_u ->
                           fun sc_ty ->
                             fun sc ->
                               fun ct ->
                                 fun checked_brs ->
                                   match checked_brs with
                                   | [] ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_V2_Derived.fail
                                               "Impossible: empty match"))
                                   | checked_br::rest ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Match.fst"
                                                        (Prims.of_int (369))
                                                        (Prims.of_int (25))
                                                        (Prims.of_int (369))
                                                        (Prims.of_int (35)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Match.fst"
                                                        (Prims.of_int (368))
                                                        (Prims.of_int (23))
                                                        (Prims.of_int (385))
                                                        (Prims.of_int (26)))))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___ -> checked_br))
                                               (fun uu___ ->
                                                  (fun uu___ ->
                                                     match uu___ with
                                                     | FStar_Pervasives.Mkdtuple3
                                                         (br, c, d) ->
                                                         (match c with
                                                          | Pulse_Syntax_Base.C_ST
                                                              uu___1 ->
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Prims.Mkdtuple2
                                                                    (c,
                                                                    ((Prims.Mkdtuple2
                                                                    (br, d))
                                                                    ::
                                                                    (FStar_List_Tot_Base.map
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br1, c',
                                                                    d1) ->
                                                                    Prims.Mkdtuple2
                                                                    (br1, d1))
                                                                    rest))))))
                                                          | Pulse_Syntax_Base.C_STGhost
                                                              (uu___1,
                                                               uu___2)
                                                              ->
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.Mkdtuple2
                                                                    (c,
                                                                    ((Prims.Mkdtuple2
                                                                    (br, d))
                                                                    ::
                                                                    (FStar_List_Tot_Base.map
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (br1, c',
                                                                    d1) ->
                                                                    Prims.Mkdtuple2
                                                                    (br1, d1))
                                                                    rest))))))
                                                          | Pulse_Syntax_Base.C_STAtomic
                                                              (i, obs, stc)
                                                              ->
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    max_obs
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives.__proj__Mkdtuple3__item___2
                                                                    rest) obs))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    max_obs1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (i,
                                                                    max_obs1,
                                                                    stc)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun c1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (weaken_branch_observability
                                                                    max_obs1
                                                                    g pre
                                                                    post_hint
                                                                    sc_u
                                                                    sc_ty sc
                                                                    c1)
                                                                    checked_brs))
                                                                    (fun
                                                                    checked_brs1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Prims.Mkdtuple2
                                                                    (c1,
                                                                    checked_brs1)))))
                                                                    uu___1)))
                                                                    uu___1)))))
                                                    uu___)))) uu___7 uu___6
                    uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let rec (least_tag :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit Pulse_Typing.post_hint_for_env ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.typ ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit, unit, unit) check_branches_aux_t
                Prims.list -> Pulse_Syntax_Base.ctag)
  =
  fun g ->
    fun pre ->
      fun post_hint ->
        fun sc_u ->
          fun sc_ty ->
            fun sc ->
              fun checked_brs ->
                match checked_brs with
                | [] -> Pulse_Syntax_Base.STT_Ghost
                | checked_br::rest ->
                    let uu___ = checked_br in
                    (match uu___ with
                     | FStar_Pervasives.Mkdtuple3 (uu___1, c, uu___2) ->
                         (match c with
                          | Pulse_Syntax_Base.C_ST uu___3 ->
                              Pulse_Syntax_Base.STT
                          | Pulse_Syntax_Base.C_STGhost (uu___3, uu___4) ->
                              least_tag g pre post_hint sc_u sc_ty sc rest
                          | Pulse_Syntax_Base.C_STAtomic (i, uu___3, uu___4)
                              -> Pulse_Syntax_Base.STT_Atomic))
let (weaken_branch_tag_to :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit Pulse_Typing.post_hint_for_env ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.typ ->
            Pulse_Syntax_Base.term ->
              Pulse_Syntax_Base.ctag ->
                (unit, unit, unit, unit, unit, unit) check_branches_aux_t ->
                  ((unit, unit, unit, unit, unit, unit) check_branches_aux_t,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun post_hint ->
        fun sc_u ->
          fun sc_ty ->
            fun sc ->
              fun ct ->
                fun br ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                             (Prims.of_int (404)) (Prims.of_int (22))
                             (Prims.of_int (404)) (Prims.of_int (24)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                             (Prims.of_int (404)) Prims.int_one
                             (Prims.of_int (423)) (Prims.of_int (5)))))
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> br))
                    (fun uu___ ->
                       (fun uu___ ->
                          match uu___ with
                          | FStar_Pervasives.Mkdtuple3 (pe, c, d) ->
                              if (Pulse_Syntax_Base.ctag_of_comp_st c) = ct
                              then
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___1 -> br)))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Match.fst"
                                                 (Prims.of_int (407))
                                                 (Prims.of_int (12))
                                                 (Prims.of_int (407))
                                                 (Prims.of_int (26)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Match.fst"
                                                 (Prims.of_int (408))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (423))
                                                 (Prims.of_int (5)))))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              (FStar_Pervasives_Native.snd pe).Pulse_Syntax_Base.range1))
                                        (fun uu___2 ->
                                           (fun r ->
                                              match (ct, c) with
                                              | (Pulse_Syntax_Base.STT_Ghost,
                                                 Pulse_Syntax_Base.C_STAtomic
                                                 (uu___2, uu___3, uu___4)) ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_V2_Derived.fail
                                                          "Unexpected least effect"))
                                              | (Pulse_Syntax_Base.STT_Ghost,
                                                 Pulse_Syntax_Base.C_ST
                                                 uu___2) ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_V2_Derived.fail
                                                          "Unexpected least effect"))
                                              | (Pulse_Syntax_Base.STT_Atomic,
                                                 Pulse_Syntax_Base.C_ST
                                                 uu___2) ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (Pulse_Typing_Env.fail
                                                          g
                                                          (FStar_Pervasives_Native.Some
                                                             r)
                                                          "Cannot lift a computation from ST to atomic"))
                                              | (Pulse_Syntax_Base.STT,
                                                 uu___2) ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (Pulse_Typing_Env.fail
                                                          g
                                                          (FStar_Pervasives_Native.Some
                                                             r)
                                                          "Cannot lift a branch to ST"))
                                              | (Pulse_Syntax_Base.STT_Atomic,
                                                 Pulse_Syntax_Base.C_STGhost
                                                 (uu___2, uu___3)) ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Match.fst"
                                                                   (Prims.of_int (419))
                                                                   (Prims.of_int (57))
                                                                   (Prims.of_int (419))
                                                                   (Prims.of_int (58)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Match.fst"
                                                                   (Prims.of_int (418))
                                                                   (Prims.of_int (35))
                                                                   (Prims.of_int (423))
                                                                   (Prims.of_int (5)))))
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___4 -> d))
                                                          (fun uu___4 ->
                                                             (fun uu___4 ->
                                                                match uu___4
                                                                with
                                                                | Pulse_Typing.TBR
                                                                    (g1,
                                                                    sc_u1,
                                                                    sc_ty1,
                                                                    sc1, c1,
                                                                    p, e, bs,
                                                                    pf1, pf2,
                                                                    pf3, h,
                                                                    d1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Combinators.lift_ghost_atomic
                                                                    (Pulse_Typing_Env.push_binding
                                                                    (Pulse_Typing.push_bindings
                                                                    g1
                                                                    (FStar_List_Tot_Base.map
                                                                    Pulse_Typing.readback_binding
                                                                    bs)) h
                                                                    {
                                                                    Pulse_Syntax_Base.name
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "branch equality");
                                                                    Pulse_Syntax_Base.range
                                                                    =
                                                                    FStar_Range.range_0
                                                                    }
                                                                    (Pulse_Typing.mk_sq_eq2
                                                                    sc_u1
                                                                    sc_ty1
                                                                    sc1
                                                                    (Pulse_Syntax_Pure.wr
                                                                    (FStar_Pervasives_Native.fst
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    (FStar_Reflection_Typing.elaborate_pat
                                                                    (Pulse_Elaborate_Pure.elab_pat
                                                                    p) bs)))
                                                                    FStar_Range.range_0)))
                                                                    e c1 d1))
                                                                    (fun d2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (pe,
                                                                    (Pulse_Typing_Combinators.st_ghost_as_atomic
                                                                    c1),
                                                                    (Pulse_Typing.TBR
                                                                    (g1,
                                                                    sc_u1,
                                                                    sc_ty1,
                                                                    sc1,
                                                                    (Pulse_Typing_Combinators.st_ghost_as_atomic
                                                                    c1), p,
                                                                    e, bs,
                                                                    (), (),
                                                                    (), h,
                                                                    d2)))))))
                                                               uu___4))))
                                             uu___2)))) uu___)
let (weaken_branch_tags :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit Pulse_Typing.post_hint_for_env ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.typ ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit, unit, unit) check_branches_aux_t
                Prims.list ->
                ((Pulse_Syntax_Base.ctag,
                   (unit, unit, unit, unit, unit, unit) check_branches_aux_t
                     Prims.list)
                   Prims.dtuple2,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun post_hint ->
        fun sc_u ->
          fun sc_ty ->
            fun sc ->
              fun checked_brs ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                           (Prims.of_int (430)) (Prims.of_int (11))
                           (Prims.of_int (430)) (Prims.of_int (32)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                           (Prims.of_int (430)) (Prims.of_int (35))
                           (Prims.of_int (432)) (Prims.of_int (15)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        least_tag g pre post_hint sc_u sc_ty sc checked_brs))
                  (fun uu___ ->
                     (fun ct ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Match.fst"
                                      (Prims.of_int (431))
                                      (Prims.of_int (12))
                                      (Prims.of_int (431))
                                      (Prims.of_int (55)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Match.fst"
                                      (Prims.of_int (432)) (Prims.of_int (2))
                                      (Prims.of_int (432))
                                      (Prims.of_int (15)))))
                             (Obj.magic
                                (FStar_Tactics_Util.map
                                   (weaken_branch_tag_to g pre post_hint sc_u
                                      sc_ty sc ct) checked_brs))
                             (fun brs ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___ -> Prims.Mkdtuple2 (ct, brs)))))
                       uu___)
let (maybe_weaken_branch_tags :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit Pulse_Typing.post_hint_for_env ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.typ ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit, unit, unit) check_branches_aux_t
                Prims.list ->
                ((Pulse_Syntax_Base.ctag,
                   (unit, unit, unit, unit, unit, unit) check_branches_aux_t
                     Prims.list)
                   Prims.dtuple2,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun g ->
                   fun pre ->
                     fun post_hint ->
                       fun sc_u ->
                         fun sc_ty ->
                           fun sc ->
                             fun checked_brs ->
                               match post_hint.Pulse_Typing.effect_annot with
                               | Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
                                   uu___ ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Match.fst"
                                                    (Prims.of_int (440))
                                                    (Prims.of_int (13))
                                                    (Prims.of_int (440))
                                                    (Prims.of_int (34)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.Match.fst"
                                                    (Prims.of_int (440))
                                                    (Prims.of_int (37))
                                                    (Prims.of_int (442))
                                                    (Prims.of_int (17)))))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___1 ->
                                                 least_tag g pre post_hint
                                                   sc_u sc_ty sc checked_brs))
                                           (fun uu___1 ->
                                              (fun ct ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Match.fst"
                                                               (Prims.of_int (441))
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (441))
                                                               (Prims.of_int (57)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Match.fst"
                                                               (Prims.of_int (442))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (442))
                                                               (Prims.of_int (17)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_Util.map
                                                            (weaken_branch_tag_to
                                                               g pre
                                                               post_hint sc_u
                                                               sc_ty sc ct)
                                                            checked_brs))
                                                      (fun brs ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___1 ->
                                                              Prims.Mkdtuple2
                                                                (ct, brs)))))
                                                uu___1)))
                               | uu___ ->
                                   Obj.magic
                                     (Obj.repr
                                        (match checked_brs with
                                         | [] ->
                                             Obj.repr
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___1 ->
                                                     Prims.Mkdtuple2
                                                       (Pulse_Syntax_Base.STT_Ghost,
                                                         [])))
                                         | hd::tl ->
                                             Obj.repr
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Match.fst"
                                                           (Prims.of_int (447))
                                                           (Prims.of_int (15))
                                                           (Prims.of_int (447))
                                                           (Prims.of_int (28)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Match.fst"
                                                           (Prims.of_int (447))
                                                           (Prims.of_int (31))
                                                           (Prims.of_int (449))
                                                           (Prims.of_int (27)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___1 ->
                                                        ctag_of_br g pre
                                                          post_hint sc_u
                                                          sc_ty sc hd))
                                                  (fun uu___1 ->
                                                     (fun ct ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (139)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (27)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Util.map
                                                                   (fun
                                                                    uu___1 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    x)))
                                                                    uu___1)
                                                                   checked_brs))
                                                             (fun
                                                                checked_brs1
                                                                ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___1
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (ct,
                                                                    checked_brs1)))))
                                                       uu___1))))) uu___6
                  uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (check_branches :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Checker_Base.check_t ->
            Pulse_Syntax_Base.universe ->
              Pulse_Syntax_Base.typ ->
                Pulse_Syntax_Base.term ->
                  Pulse_Syntax_Base.branch Prims.list ->
                    (FStar_Reflection_V2_Data.pattern *
                      FStar_Reflection_V2_Data.binding Prims.list) Prims.list
                      ->
                      ((Pulse_Syntax_Base.branch Prims.list,
                         Pulse_Syntax_Base.comp_st,
                         (unit, unit, unit, unit, unit, unit)
                           Pulse_Typing.brs_typing)
                         FStar_Pervasives.dtuple3,
                        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun check ->
            fun sc_u ->
              fun sc_ty ->
                fun sc ->
                  fun brs0 ->
                    fun bnds ->
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                                 (Prims.of_int (465)) (Prims.of_int (20))
                                 (Prims.of_int (465)) (Prims.of_int (95)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                                 (Prims.of_int (465)) (Prims.of_int (98))
                                 (Prims.of_int (479)) (Prims.of_int (18)))))
                        (Obj.magic
                           (check_branches_aux g pre () post_hint check sc_u
                              sc_ty sc brs0 bnds))
                        (fun uu___ ->
                           (fun checked_brs ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Match.fst"
                                            (Prims.of_int (466))
                                            (Prims.of_int (30))
                                            (Prims.of_int (466))
                                            (Prims.of_int (66)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Match.fst"
                                            (Prims.of_int (465))
                                            (Prims.of_int (98))
                                            (Prims.of_int (479))
                                            (Prims.of_int (18)))))
                                   (Obj.magic
                                      (maybe_weaken_branch_tags g pre
                                         post_hint sc_u sc_ty sc checked_brs))
                                   (fun uu___ ->
                                      (fun uu___ ->
                                         match uu___ with
                                         | Prims.Mkdtuple2 (ct, checked_brs1)
                                             ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Match.fst"
                                                           (Prims.of_int (467))
                                                           (Prims.of_int (30))
                                                           (Prims.of_int (467))
                                                           (Prims.of_int (58)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Match.fst"
                                                           (Prims.of_int (466))
                                                           (Prims.of_int (69))
                                                           (Prims.of_int (479))
                                                           (Prims.of_int (18)))))
                                                  (Obj.magic
                                                     (join_branches g pre
                                                        post_hint sc_u sc_ty
                                                        sc ct checked_brs1))
                                                  (fun uu___1 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___2 ->
                                                          match uu___1 with
                                                          | Prims.Mkdtuple2
                                                              (c0,
                                                               checked_brs2)
                                                              ->
                                                              FStar_Pervasives.Mkdtuple3
                                                                ((FStar_List_Tot_Base.map
                                                                    FStar_Pervasives.dfst
                                                                    checked_brs2),
                                                                  c0,
                                                                  (let rec aux
                                                                    brs =
                                                                    match brs
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Pulse_Typing.TBRS_0
                                                                    c0
                                                                    | 
                                                                    (Prims.Mkdtuple2
                                                                    ((p, e),
                                                                    d))::rest
                                                                    ->
                                                                    Pulse_Typing.TBRS_1
                                                                    (c0, p,
                                                                    e, d,
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives.dfst
                                                                    rest),
                                                                    (aux rest)) in
                                                                   aux
                                                                    checked_brs2))))))
                                        uu___))) uu___)
let (check :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        unit Pulse_Typing.post_hint_for_env ->
          Pulse_Syntax_Base.ppname ->
            Pulse_Syntax_Base.term ->
              Pulse_Syntax_Base.branch Prims.list ->
                Pulse_Checker_Base.check_t ->
                  ((unit, unit, unit) Pulse_Checker_Base.checker_result_t,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun pre ->
      fun pre_typing ->
        fun post_hint ->
          fun res_ppname ->
            fun sc ->
              fun brs ->
                fun check1 ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                             (Prims.of_int (493)) (Prims.of_int (10))
                             (Prims.of_int (493)) (Prims.of_int (64)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.Match.fst"
                             (Prims.of_int (493)) (Prims.of_int (67))
                             (Prims.of_int (542)) (Prims.of_int (55)))))
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          Pulse_Typing_Env.push_context_no_range g
                            "check_match"))
                    (fun uu___ ->
                       (fun g1 ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Match.fst"
                                        (Prims.of_int (495))
                                        (Prims.of_int (17))
                                        (Prims.of_int (495))
                                        (Prims.of_int (52)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Match.fst"
                                        (Prims.of_int (495))
                                        (Prims.of_int (55))
                                        (Prims.of_int (542))
                                        (Prims.of_int (55)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___ ->
                                     Pulse_RuntimeUtils.range_of_term sc))
                               (fun uu___ ->
                                  (fun sc_range ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Match.fst"
                                                   (Prims.of_int (496))
                                                   (Prims.of_int (17))
                                                   (Prims.of_int (496))
                                                   (Prims.of_int (20)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Match.fst"
                                                   (Prims.of_int (496))
                                                   (Prims.of_int (23))
                                                   (Prims.of_int (542))
                                                   (Prims.of_int (55)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___ -> brs))
                                          (fun uu___ ->
                                             (fun orig_brs ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Match.fst"
                                                              (Prims.of_int (497))
                                                              (Prims.of_int (12))
                                                              (Prims.of_int (497))
                                                              (Prims.of_int (24)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Match.fst"
                                                              (Prims.of_int (497))
                                                              (Prims.of_int (27))
                                                              (Prims.of_int (542))
                                                              (Prims.of_int (55)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___ ->
                                                           FStar_List_Tot_Base.length
                                                             brs))
                                                     (fun uu___ ->
                                                        (fun nbr ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (87)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (55)))))
                                                                (Obj.magic
                                                                   (Pulse_Checker_Pure.compute_tot_term_type_and_u
                                                                    g1 sc))
                                                                (fun uu___ ->
                                                                   (fun uu___
                                                                    ->
                                                                    match uu___
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (sc1,
                                                                    sc_u,
                                                                    sc_ty,
                                                                    sc_ty_typing,
                                                                    sc_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_List_Tot_Base.map
                                                                    Pulse_Elaborate_Pure.elab_pat
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.fst
                                                                    brs)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    elab_pats
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.check_match_complete
                                                                    (Pulse_Typing.elab_env
                                                                    g1) sc1
                                                                    sc_ty
                                                                    elab_pats))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    sc_range)
                                                                    "Could not check that match is correct/complete"))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (elab_pats',
                                                                    bnds) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (elab_pats',
                                                                    bnds,
                                                                    (Pulse_Typing.PC_Elab
                                                                    (g1, sc1,
                                                                    sc_ty,
                                                                    elab_pats',
                                                                    bnds,
                                                                    (FStar_Reflection_Typing.MC_Tok
                                                                    ((Pulse_Typing.elab_env
                                                                    g1), sc1,
                                                                    sc_ty,
                                                                    elab_pats',
                                                                    bnds, ())))))))))
                                                                    uu___1)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (elab_pats',
                                                                    bnds',
                                                                    complete_d)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    uu___1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (518))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Common.map_opt
                                                                    readback_pat
                                                                    elab_pats'))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    new_pats
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (518))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (55)))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    new_pats
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (FStar_Pervasives_Native.Some
                                                                    sc_range)
                                                                    "failed to readback new patterns"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (Pulse_Common.zipWith
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun
                                                                    uu___4 ->
                                                                    (fun p ->
                                                                    fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (uu___6,
                                                                    e) ->
                                                                    (p, e))))
                                                                    uu___5
                                                                    uu___4)
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    new_pats)
                                                                    brs))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun brs1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (check_branches
                                                                    g1 pre ()
                                                                    post_hint
                                                                    check1
                                                                    sc_u
                                                                    sc_ty sc1
                                                                    brs1
                                                                    (Pulse_Common.zip
                                                                    elab_pats'
                                                                    bnds')))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (brs2, c,
                                                                    brs_d) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Base.comp_typing_from_post_hint
                                                                    g c ()
                                                                    post_hint))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    c_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (541))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (541))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Match.fst"
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing.T_Match
                                                                    (g1,
                                                                    sc_u,
                                                                    sc_ty,
                                                                    sc1, (),
                                                                    (), c,
                                                                    (), brs2,
                                                                    brs_d,
                                                                    complete_d)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun d ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint)
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    ((Pulse_Typing.wrst
                                                                    c
                                                                    (Pulse_Syntax_Base.Tm_Match
                                                                    {
                                                                    Pulse_Syntax_Base.sc
                                                                    = sc1;
                                                                    Pulse_Syntax_Base.returns_
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.brs
                                                                    = brs2
                                                                    })), c,
                                                                    d))
                                                                    res_ppname))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___)))
                                                          uu___))) uu___)))
                                    uu___))) uu___)