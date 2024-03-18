open Prims
let (debug_main :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun s ->
           if
             Pulse_RuntimeUtils.debug_at_level (Pulse_Typing_Env.fstar_env g)
               "pulse.main"
           then
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (36)) (Prims.of_int (15))
                              (Prims.of_int (36)) (Prims.of_int (21)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (36)) (Prims.of_int (7))
                              (Prims.of_int (36)) (Prims.of_int (21)))))
                     (Obj.magic (s ()))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic (FStar_Tactics_V2_Builtins.print uu___))
                          uu___)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
let rec (mk_abs :
  Pulse_Typing_Env.env ->
    (Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option *
      Pulse_Syntax_Base.binder * Pulse_Syntax_Base.bv) Prims.list ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp ->
          (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun qbs ->
      fun body ->
        fun comp ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (44))
                     (Prims.of_int (6)) (Prims.of_int (44))
                     (Prims.of_int (59)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (46))
                     (Prims.of_int (2)) (Prims.of_int (55))
                     (Prims.of_int (81)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ ->
                  fun s ->
                    fun r ->
                      {
                        Pulse_Syntax_Base.term1 = s;
                        Pulse_Syntax_Base.range2 = r;
                        Pulse_Syntax_Base.effect_tag =
                          Pulse_Syntax_Base.default_effect_hint
                      }))
            (fun uu___ ->
               (fun with_range ->
                  match qbs with
                  | (q, last, last_bv)::[] ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ ->
                                 with_range
                                   (Pulse_Syntax_Builder.tm_abs last q
                                      {
                                        Pulse_Syntax_Base.annotated =
                                          (FStar_Pervasives_Native.Some
                                             (Pulse_Syntax_Naming.close_comp
                                                comp
                                                last_bv.Pulse_Syntax_Base.bv_index));
                                        Pulse_Syntax_Base.elaborated =
                                          FStar_Pervasives_Native.None
                                      }
                                      (Pulse_Syntax_Naming.close_st_term body
                                         last_bv.Pulse_Syntax_Base.bv_index))
                                   (Pulse_Syntax_Naming.close_st_term body
                                      last_bv.Pulse_Syntax_Base.bv_index).Pulse_Syntax_Base.range2)))
                  | (q, b, bv)::qbs1 ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Pulse.Main.fst"
                                       (Prims.of_int (53))
                                       (Prims.of_int (15))
                                       (Prims.of_int (53))
                                       (Prims.of_int (37)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Pulse.Main.fst"
                                       (Prims.of_int (55)) (Prims.of_int (4))
                                       (Prims.of_int (55))
                                       (Prims.of_int (81)))))
                              (Obj.magic (mk_abs g qbs1 body comp))
                              (fun body1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      with_range
                                        (Pulse_Syntax_Builder.tm_abs b q
                                           Pulse_Syntax_Base.empty_ascription
                                           (Pulse_Syntax_Naming.close_st_term
                                              body1
                                              bv.Pulse_Syntax_Base.bv_index))
                                        (Pulse_Syntax_Naming.close_st_term
                                           body1
                                           bv.Pulse_Syntax_Base.bv_index).Pulse_Syntax_Base.range2)))))
                 uu___)
let rec (is_incremental_st_term :
  Pulse_Syntax_Base.st_term ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.st_term FStar_Pervasives_Native.option)
  =
  fun st0 ->
    fun st1 ->
      match ((st0.Pulse_Syntax_Base.term1), (st1.Pulse_Syntax_Base.term1))
      with
      | (Pulse_Syntax_Base.Tm_Bind
         { Pulse_Syntax_Base.binder = binder0;
           Pulse_Syntax_Base.head1 = head0;
           Pulse_Syntax_Base.body1 = body0;_},
         Pulse_Syntax_Base.Tm_Bind
         { Pulse_Syntax_Base.binder = binder1;
           Pulse_Syntax_Base.head1 = head1;
           Pulse_Syntax_Base.body1 = body1;_})
          ->
          if
            (Pulse_Syntax_Base.eq_binder binder0 binder1) &&
              (Pulse_Syntax_Base.eq_st_term head0 head1)
          then is_incremental_st_term body0 body1
          else FStar_Pervasives_Native.None
      | (Pulse_Syntax_Base.Tm_TotBind
         { Pulse_Syntax_Base.binder1 = binder0;
           Pulse_Syntax_Base.head2 = head0;
           Pulse_Syntax_Base.body2 = body0;_},
         Pulse_Syntax_Base.Tm_TotBind
         { Pulse_Syntax_Base.binder1 = binder1;
           Pulse_Syntax_Base.head2 = head1;
           Pulse_Syntax_Base.body2 = body1;_})
          ->
          if
            (Pulse_Syntax_Base.eq_binder binder0 binder1) &&
              (Pulse_Syntax_Base.eq_tm head0 head1)
          then is_incremental_st_term body0 body1
          else FStar_Pervasives_Native.None
      | (Pulse_Syntax_Base.Tm_Admit uu___, uu___1) ->
          FStar_Pervasives_Native.Some st1
      | (uu___, uu___1) -> FStar_Pervasives_Native.None
type cache_elt =
  {
  cache_decl: Pulse_Syntax_Base.decl' ;
  cache_typing:
    (Pulse_Typing_Env.env, Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
      (unit, unit, unit) Pulse_Typing.st_typing) FStar_Pervasives.dtuple4
    }
let (__proj__Mkcache_elt__item__cache_decl :
  cache_elt -> Pulse_Syntax_Base.decl') =
  fun projectee ->
    match projectee with | { cache_decl; cache_typing;_} -> cache_decl
let (__proj__Mkcache_elt__item__cache_typing :
  cache_elt ->
    (Pulse_Typing_Env.env, Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
      (unit, unit, unit) Pulse_Typing.st_typing) FStar_Pervasives.dtuple4)
  =
  fun projectee ->
    match projectee with | { cache_decl; cache_typing;_} -> cache_typing
let (is_internal_name : Prims.string -> Prims.bool) =
  fun s ->
    ((((((s = "_fret") || (s = "_bind_c")) || (s = "_while_c")) ||
         (s = "_tbind_c"))
        || (s = "_if_br"))
       || (s = "_br"))
      || ((FStar_String.index s Prims.int_zero) = 95)
let (is_internal_binder :
  Pulse_Syntax_Base.binder ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (99))
               (Prims.of_int (10)) (Prims.of_int (99)) (Prims.of_int (39)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (100))
               (Prims.of_int (2)) (Prims.of_int (100)) (Prims.of_int (20)))))
      (Obj.magic
         (FStar_Tactics_Unseal.unseal
            (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name))
      (fun s ->
         FStar_Tactics_Effect.lift_div_tac (fun uu___ -> is_internal_name s))
let op_let_Question :
  'a 'b .
    'a FStar_Pervasives_Native.option ->
      ('a ->
         ('b FStar_Pervasives_Native.option, unit)
           FStar_Tactics_Effect.tac_repr)
        ->
        ('b FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun x ->
         fun y ->
           match x with
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives_Native.None)))
           | FStar_Pervasives_Native.Some x1 -> Obj.magic (Obj.repr (y x1)))
        uu___1 uu___
let return : 'a . 'a -> 'a FStar_Pervasives_Native.option =
  fun x -> FStar_Pervasives_Native.Some x
type ('c1, 'c2) c_match = unit
let (obs_match :
  Pulse_Syntax_Base.comp_st -> Pulse_Syntax_Base.comp_st -> Prims.bool) =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (Pulse_Syntax_Base.C_ST uu___, Pulse_Syntax_Base.C_ST uu___1) -> true
      | (Pulse_Syntax_Base.C_STAtomic (uu___, obs1, uu___1),
         Pulse_Syntax_Base.C_STAtomic (uu___2, obs2, uu___3)) -> obs1 = obs2
      | (Pulse_Syntax_Base.C_STGhost uu___, Pulse_Syntax_Base.C_STGhost
         uu___1) -> true
type ('t0, 't1) both_binds = unit
let rec (incremental_tc_bind0 :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.st_term ->
            Pulse_Syntax_Base.st_term ->
              ((Pulse_Syntax_Base.st_term,
                 (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun t ->
                   fun c ->
                     fun d ->
                       fun t0 ->
                         fun t1 ->
                           match d with
                           | Pulse_Typing.T_Bind
                               (g1, e1, e2, c1, c2, b, x, c3, e1_typing,
                                c1_res_typing, e2_typing, d_bind_comp)
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (161))
                                                (Prims.of_int (4))
                                                (Prims.of_int (161))
                                                (Prims.of_int (93)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (162))
                                                (Prims.of_int (4))
                                                (Prims.of_int (171))
                                                (Prims.of_int (94)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Main.fst"
                                                      (Prims.of_int (161))
                                                      (Prims.of_int (12))
                                                      (Prims.of_int (161))
                                                      (Prims.of_int (93)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Main.fst"
                                                      (Prims.of_int (161))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (161))
                                                      (Prims.of_int (93)))))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Main.fst"
                                                            (Prims.of_int (161))
                                                            (Prims.of_int (70))
                                                            (Prims.of_int (161))
                                                            (Prims.of_int (92)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "prims.fst"
                                                            (Prims.of_int (590))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (590))
                                                            (Prims.of_int (31)))))
                                                   (Obj.magic
                                                      (Pulse_Syntax_Printer.binder_to_string
                                                         b))
                                                   (fun uu___ ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           Prims.strcat
                                                             "Incremental tc bind0 with b: "
                                                             (Prims.strcat
                                                                uu___ "\n")))))
                                             (fun uu___ ->
                                                (fun uu___ ->
                                                   Obj.magic
                                                     (FStar_Tactics_V2_Builtins.print
                                                        uu___)) uu___)))
                                       (fun uu___ ->
                                          (fun uu___ ->
                                             if
                                               Pulse_Syntax_Base.uu___is_Tm_Bind
                                                 e1.Pulse_Syntax_Base.term1
                                             then
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Main.fst"
                                                                (Prims.of_int (163))
                                                                (Prims.of_int (17))
                                                                (Prims.of_int (163))
                                                                (Prims.of_int (119)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Main.fst"
                                                                (Prims.of_int (163))
                                                                (Prims.of_int (122))
                                                                (Prims.of_int (168))
                                                                (Prims.of_int (23)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (119)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (119)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (118)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                   (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    e1))
                                                                   (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Prims.strcat
                                                                    "Incremental tc bind0 e1.term is a bind: "
                                                                    (Prims.strcat
                                                                    uu___1
                                                                    "\n")))))
                                                             (fun uu___1 ->
                                                                (fun uu___1
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___1))
                                                                  uu___1)))
                                                       (fun uu___1 ->
                                                          (fun uu___1 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (67)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (23)))))
                                                                  (Obj.magic
                                                                    (incremental_tc_bind1
                                                                    g1 e1 c1
                                                                    e1_typing
                                                                    t0 t1))
                                                                  (fun ropt
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match ropt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (e11,
                                                                    e1_typing1))
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    ((Pulse_Typing.wr
                                                                    c3
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e11;
                                                                    Pulse_Syntax_Base.body1
                                                                    = e2
                                                                    })),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g1, e11,
                                                                    e2, c1,
                                                                    c2, b, x,
                                                                    c3,
                                                                    e1_typing1,
                                                                    (),
                                                                    e2_typing,
                                                                    d_bind_comp))))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                            uu___1)))
                                             else
                                               Obj.magic
                                                 (Obj.repr
                                                    (if
                                                       ((Pulse_Typing.uu___is_T_Frame
                                                           g t c d)
                                                          ||
                                                          (Pulse_Typing.uu___is_T_Sub
                                                             g t c d))
                                                         ||
                                                         (Pulse_Typing.uu___is_T_Equiv
                                                            g t c d)
                                                     then
                                                       Obj.repr
                                                         (incremental_tc_trivial
                                                            g t c d
                                                            (fun g2 ->
                                                               fun t2 ->
                                                                 fun c4 ->
                                                                   fun
                                                                    e_typing
                                                                    ->
                                                                    incremental_tc_bind0
                                                                    g2 t2 c4
                                                                    e_typing
                                                                    t0 t1))
                                                     else
                                                       Obj.repr
                                                         (FStar_Tactics_V2_Derived.fail
                                                            (Prims.strcat
                                                               "Unexpected derivation(2) with "
                                                               (Prims.strcat
                                                                  (Pulse_Typing.tag_of_st_typing
                                                                    g t c d)
                                                                  ""))))))
                                            uu___)))
                           | uu___ ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       ((Pulse_Typing.uu___is_T_Frame g t c d)
                                          ||
                                          (Pulse_Typing.uu___is_T_Sub g t c d))
                                         ||
                                         (Pulse_Typing.uu___is_T_Equiv g t c
                                            d)
                                     then
                                       Obj.repr
                                         (incremental_tc_trivial g t c d
                                            (fun g1 ->
                                               fun t2 ->
                                                 fun c1 ->
                                                   fun e_typing ->
                                                     incremental_tc_bind0 g1
                                                       t2 c1 e_typing t0 t1))
                                     else
                                       Obj.repr
                                         (FStar_Tactics_V2_Derived.fail
                                            (Prims.strcat
                                               "Unexpected derivation(1) with "
                                               (Prims.strcat
                                                  (Pulse_Typing.tag_of_st_typing
                                                     g t c d) "")))))) uu___5
                uu___4 uu___3 uu___2 uu___1 uu___
and (incremental_tc_bind1 :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.st_term ->
            Pulse_Syntax_Base.st_term ->
              ((Pulse_Syntax_Base.st_term,
                 (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun t ->
                   fun c ->
                     fun d ->
                       fun t0 ->
                         fun t1 ->
                           match d with
                           | Pulse_Typing.T_Bind
                               (g1, e1, e2, c1, c2, b, x, c3, e1_typing,
                                c1_res_typing, e2_typing, d_bind_comp)
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (186))
                                                (Prims.of_int (4))
                                                (Prims.of_int (186))
                                                (Prims.of_int (90)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (187))
                                                (Prims.of_int (4))
                                                (Prims.of_int (198))
                                                (Prims.of_int (37)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Main.fst"
                                                      (Prims.of_int (186))
                                                      (Prims.of_int (12))
                                                      (Prims.of_int (186))
                                                      (Prims.of_int (90)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Main.fst"
                                                      (Prims.of_int (186))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (186))
                                                      (Prims.of_int (90)))))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Main.fst"
                                                            (Prims.of_int (186))
                                                            (Prims.of_int (67))
                                                            (Prims.of_int (186))
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
                                                      (Pulse_Syntax_Printer.binder_to_string
                                                         b))
                                                   (fun uu___ ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           Prims.strcat
                                                             "incremental tc bind1, b : "
                                                             (Prims.strcat
                                                                uu___ "\n")))))
                                             (fun uu___ ->
                                                (fun uu___ ->
                                                   Obj.magic
                                                     (FStar_Tactics_V2_Builtins.print
                                                        uu___)) uu___)))
                                       (fun uu___ ->
                                          (fun uu___ ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (187))
                                                           (Prims.of_int (7))
                                                           (Prims.of_int (187))
                                                           (Prims.of_int (27)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (187))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (198))
                                                           (Prims.of_int (37)))))
                                                  (Obj.magic
                                                     (is_internal_binder b))
                                                  (fun uu___1 ->
                                                     (fun uu___1 ->
                                                        if uu___1
                                                        then
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (89)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (23)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_V2_Builtins.print
                                                                    "incremental tc bind1, internal binder\n"))
                                                               (fun uu___2 ->
                                                                  (fun uu___2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    b.Pulse_Syntax_Base.binder_ppname
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun g2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2
                                                                    ((b.Pulse_Syntax_Base.binder_ppname),
                                                                    x)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun e21
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    (incremental_tc_bind1
                                                                    g2 e21 c2
                                                                    e2_typing
                                                                    t0 t1))
                                                                    (fun ropt
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match ropt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (e22,
                                                                    e2_typing1))
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    ((Pulse_Typing.wr
                                                                    c3
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    e22 x)
                                                                    })),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g1, e1,
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    e22 x),
                                                                    c1, c2,
                                                                    b, x, c3,
                                                                    e1_typing,
                                                                    (),
                                                                    e2_typing1,
                                                                    d_bind_comp))))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2))
                                                        else
                                                          Obj.magic
                                                            (incremental_tc_bind2
                                                               g t c d t0 t1))
                                                       uu___1))) uu___)))
                           | uu___ ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       ((Pulse_Typing.uu___is_T_Frame g t c d)
                                          ||
                                          (Pulse_Typing.uu___is_T_Sub g t c d))
                                         ||
                                         (Pulse_Typing.uu___is_T_Equiv g t c
                                            d)
                                     then
                                       Obj.repr
                                         (incremental_tc_trivial g t c d
                                            (fun g1 ->
                                               fun t2 ->
                                                 fun c1 ->
                                                   fun e_typing ->
                                                     incremental_tc_bind1 g1
                                                       t2 c1 e_typing t0 t1))
                                     else
                                       Obj.repr
                                         (FStar_Tactics_V2_Derived.fail
                                            (Prims.strcat
                                               "Unexpected derivation(2) with "
                                               (Prims.strcat
                                                  (Pulse_Typing.tag_of_st_typing
                                                     g t c d) "")))))) uu___5
                uu___4 uu___3 uu___2 uu___1 uu___
and (incremental_tc_bind2 :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.st_term ->
            Pulse_Syntax_Base.st_term ->
              ((Pulse_Syntax_Base.st_term,
                 (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun t ->
                   fun c ->
                     fun d ->
                       fun t0 ->
                         fun t1 ->
                           match d with
                           | Pulse_Typing.T_Bind
                               (g1, e1, e2, c1, c2, b, x, c3, e1_typing,
                                c1_res_typing, e2_typing, d_bind_comp)
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (214))
                                                (Prims.of_int (6))
                                                (Prims.of_int (228))
                                                (Prims.of_int (17)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (230))
                                                (Prims.of_int (6))
                                                (Prims.of_int (243))
                                                (Prims.of_int (22)))))
                                       (match ((t0.Pulse_Syntax_Base.term1),
                                                (t1.Pulse_Syntax_Base.term1))
                                        with
                                        | (Pulse_Syntax_Base.Tm_Bind
                                           {
                                             Pulse_Syntax_Base.binder =
                                               binder0;
                                             Pulse_Syntax_Base.head1 = uu___;
                                             Pulse_Syntax_Base.body1 = body0;_},
                                           Pulse_Syntax_Base.Tm_Bind
                                           {
                                             Pulse_Syntax_Base.binder =
                                               binder1;
                                             Pulse_Syntax_Base.head1 = uu___1;
                                             Pulse_Syntax_Base.body1 = body1;_})
                                            ->
                                            Obj.magic
                                              (Obj.repr
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Main.fst"
                                                             (Prims.of_int (217))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (220))
                                                             (Prims.of_int (39)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Main.fst"
                                                             (Prims.of_int (221))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (223))
                                                             (Prims.of_int (17)))))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Main.fst"
                                                                   (Prims.of_int (217))
                                                                   (Prims.of_int (16))
                                                                   (Prims.of_int (220))
                                                                   (Prims.of_int (39)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Main.fst"
                                                                   (Prims.of_int (217))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (220))
                                                                   (Prims.of_int (39)))))
                                                          (Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (38)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (39)))))
                                                                (Obj.magic
                                                                   (Pulse_Syntax_Printer.binder_to_string
                                                                    binder1))
                                                                (fun uu___2
                                                                   ->
                                                                   (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.binder_to_string
                                                                    binder0))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.binder_to_string
                                                                    b))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "incremental tc bind2 b: "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    ", b0: "))
                                                                    (Prims.strcat
                                                                    x1
                                                                    ", b1: "))
                                                                    (Prims.strcat
                                                                    x2 "\n")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                                    uu___2)))
                                                          (fun uu___2 ->
                                                             (fun uu___2 ->
                                                                Obj.magic
                                                                  (FStar_Tactics_V2_Builtins.print
                                                                    uu___2))
                                                               uu___2)))
                                                    (fun uu___2 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            if
                                                              Pulse_Syntax_Base.eq_binder
                                                                binder0
                                                                binder1
                                                            then
                                                              FStar_Pervasives_Native.Some
                                                                (body0,
                                                                  body1)
                                                            else
                                                              FStar_Pervasives_Native.None))))
                                        | (Pulse_Syntax_Base.Tm_TotBind
                                           {
                                             Pulse_Syntax_Base.binder1 =
                                               binder0;
                                             Pulse_Syntax_Base.head2 = uu___;
                                             Pulse_Syntax_Base.body2 = body0;_},
                                           Pulse_Syntax_Base.Tm_TotBind
                                           {
                                             Pulse_Syntax_Base.binder1 =
                                               binder1;
                                             Pulse_Syntax_Base.head2 = uu___1;
                                             Pulse_Syntax_Base.body2 = body1;_})
                                            ->
                                            Obj.magic
                                              (Obj.repr
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 ->
                                                       if
                                                         Pulse_Syntax_Base.eq_binder
                                                           binder0 binder1
                                                       then
                                                         FStar_Pervasives_Native.Some
                                                           (body0, body1)
                                                       else
                                                         FStar_Pervasives_Native.None))))
                                       (fun uu___ ->
                                          (fun ropt ->
                                             match ropt with
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___ ->
                                                            FStar_Pervasives_Native.None)))
                                             | FStar_Pervasives_Native.Some
                                                 (body0, body1) ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Main.fst"
                                                                  (Prims.of_int (233))
                                                                  (Prims.of_int (17))
                                                                  (Prims.of_int (233))
                                                                  (Prims.of_int (59)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Main.fst"
                                                                  (Prims.of_int (233))
                                                                  (Prims.of_int (62))
                                                                  (Prims.of_int (243))
                                                                  (Prims.of_int (22)))))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___ ->
                                                               Pulse_Syntax_Naming.open_st_term_nv
                                                                 body0
                                                                 ((b.Pulse_Syntax_Base.binder_ppname),
                                                                   x)))
                                                         (fun uu___ ->
                                                            (fun t01 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (59)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (22)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body1
                                                                    ((b.Pulse_Syntax_Base.binder_ppname),
                                                                    x)))
                                                                    (
                                                                    fun uu___
                                                                    ->
                                                                    (fun t11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    b.Pulse_Syntax_Base.binder_ppname
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1)))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun g2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2
                                                                    ((b.Pulse_Syntax_Base.binder_ppname),
                                                                    x)))
                                                                    (fun
                                                                    uu___ ->
                                                                    (fun e21
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    (incremental_tc
                                                                    g2 e21 c2
                                                                    e2_typing
                                                                    t01 t11))
                                                                    (fun
                                                                    ropt1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    match ropt1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (e22,
                                                                    e2_typing1))
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    ((Pulse_Typing.wr
                                                                    c3
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = e1;
                                                                    Pulse_Syntax_Base.body1
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    e22 x)
                                                                    })),
                                                                    (Pulse_Typing.T_Bind
                                                                    (g1, e1,
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    e22 x),
                                                                    c1, c2,
                                                                    b, x, c3,
                                                                    e1_typing,
                                                                    (),
                                                                    e2_typing1,
                                                                    d_bind_comp))))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    uu___)))
                                                                    uu___)))
                                                                    uu___)))
                                                              uu___)))) uu___)))
                           | uu___ ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       ((Pulse_Typing.uu___is_T_Frame g t c d)
                                          ||
                                          (Pulse_Typing.uu___is_T_Sub g t c d))
                                         ||
                                         (Pulse_Typing.uu___is_T_Equiv g t c
                                            d)
                                     then
                                       Obj.repr
                                         (incremental_tc_trivial g t c d
                                            (fun g1 ->
                                               fun t2 ->
                                                 fun c1 ->
                                                   fun e_typing ->
                                                     incremental_tc_bind2 g1
                                                       t2 c1 e_typing t0 t1))
                                     else
                                       Obj.repr
                                         (FStar_Tactics_V2_Derived.fail
                                            (Prims.strcat
                                               "Unexpected derivation(3) with "
                                               (Prims.strcat
                                                  (Pulse_Typing.tag_of_st_typing
                                                     g t c d) "")))))) uu___5
                uu___4 uu___3 uu___2 uu___1 uu___
and (incremental_tc_admit :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.st_term ->
            Pulse_Syntax_Base.st_term ->
              ((Pulse_Syntax_Base.st_term,
                 (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun c ->
        fun d ->
          fun t0 ->
            fun t1 ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Main.fst"
                         (Prims.of_int (257)) (Prims.of_int (2))
                         (Prims.of_int (257)) (Prims.of_int (89)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Main.fst"
                         (Prims.of_int (257)) (Prims.of_int (90))
                         (Prims.of_int (272)) (Prims.of_int (36)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Main.fst"
                               (Prims.of_int (257)) (Prims.of_int (10))
                               (Prims.of_int (257)) (Prims.of_int (89)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Main.fst"
                               (Prims.of_int (257)) (Prims.of_int (2))
                               (Prims.of_int (257)) (Prims.of_int (89)))))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (257)) (Prims.of_int (64))
                                     (Prims.of_int (257)) (Prims.of_int (88)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "prims.fst"
                                     (Prims.of_int (590)) (Prims.of_int (19))
                                     (Prims.of_int (590)) (Prims.of_int (31)))))
                            (Obj.magic
                               (Pulse_Syntax_Printer.st_term_to_string t1))
                            (fun uu___ ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    Prims.strcat "Reached a point with e2: "
                                      (Prims.strcat uu___ "\n")))))
                      (fun uu___ ->
                         (fun uu___ ->
                            Obj.magic (FStar_Tactics_V2_Builtins.print uu___))
                           uu___)))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Main.fst"
                                    (Prims.of_int (258)) (Prims.of_int (11))
                                    (Prims.of_int (258)) (Prims.of_int (63)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Main.fst"
                                    (Prims.of_int (258)) (Prims.of_int (66))
                                    (Prims.of_int (272)) (Prims.of_int (36)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 Pulse_Typing_Metatheory_Base.st_typing_correctness
                                   g t c d))
                           (fun uu___1 ->
                              (fun ct ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (259))
                                               (Prims.of_int (40))
                                               (Prims.of_int (259))
                                               (Prims.of_int (69)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (259))
                                               (Prims.of_int (72))
                                               (Prims.of_int (272))
                                               (Prims.of_int (36)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            Pulse_Checker_Base.post_hint_from_comp_typing
                                              g c ct))
                                      (fun uu___1 ->
                                         (fun post_hint ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (261))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (261))
                                                          (Prims.of_int (70)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (261))
                                                          (Prims.of_int (73))
                                                          (Prims.of_int (272))
                                                          (Prims.of_int (36)))))
                                                 (Obj.magic
                                                    (Pulse_Checker.check g
                                                       (Pulse_Syntax_Base.comp_pre
                                                          c) ()
                                                       (FStar_Pervasives_Native.Some
                                                          post_hint)
                                                       Pulse_Syntax_Base.ppname_default
                                                       t1))
                                                 (fun uu___1 ->
                                                    (fun res ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (45)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (36)))))
                                                            (Obj.magic
                                                               (Pulse_Checker_Base.apply_checker_result_k
                                                                  g
                                                                  (Pulse_Syntax_Base.comp_pre
                                                                    c)
                                                                  post_hint
                                                                  res
                                                                  Pulse_Syntax_Base.ppname_default))
                                                            (fun uu___1 ->
                                                               (fun uu___1 ->
                                                                  match uu___1
                                                                  with
                                                                  | FStar_Pervasives.Mkdtuple3
                                                                    (t', c',
                                                                    t'_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (84)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (264))
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
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    t'))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "Typechecked with e: "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    "\n")))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___2))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    if
                                                                    obs_match
                                                                    c c'
                                                                    then
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (t',
                                                                    t'_typing)))
                                                                    else
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    "Obs did not match!\n")))
                                                                 uu___1)))
                                                      uu___1))) uu___1)))
                                uu___1))) uu___)
and (incremental_tc :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.st_term ->
            Pulse_Syntax_Base.st_term ->
              ((Pulse_Syntax_Base.st_term,
                 (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun c ->
        fun d ->
          fun t0 ->
            fun t1 ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Main.fst"
                         (Prims.of_int (281)) (Prims.of_int (2))
                         (Prims.of_int (284)) (Prims.of_int (29)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Main.fst"
                         (Prims.of_int (285)) (Prims.of_int (2))
                         (Prims.of_int (315)) (Prims.of_int (22)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Main.fst"
                               (Prims.of_int (281)) (Prims.of_int (10))
                               (Prims.of_int (284)) (Prims.of_int (29)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Main.fst"
                               (Prims.of_int (281)) (Prims.of_int (2))
                               (Prims.of_int (284)) (Prims.of_int (29)))))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (284)) (Prims.of_int (4))
                                     (Prims.of_int (284)) (Prims.of_int (28)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (281)) (Prims.of_int (10))
                                     (Prims.of_int (284)) (Prims.of_int (29)))))
                            (Obj.magic
                               (Pulse_Syntax_Printer.st_term_to_string t1))
                            (fun uu___ ->
                               (fun uu___ ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (281))
                                                (Prims.of_int (10))
                                                (Prims.of_int (284))
                                                (Prims.of_int (29)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (281))
                                                (Prims.of_int (10))
                                                (Prims.of_int (284))
                                                (Prims.of_int (29)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Main.fst"
                                                      (Prims.of_int (283))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (283))
                                                      (Prims.of_int (28)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Main.fst"
                                                      (Prims.of_int (281))
                                                      (Prims.of_int (10))
                                                      (Prims.of_int (284))
                                                      (Prims.of_int (29)))))
                                             (Obj.magic
                                                (Pulse_Syntax_Printer.st_term_to_string
                                                   t0))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Main.fst"
                                                                 (Prims.of_int (281))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (284))
                                                                 (Prims.of_int (29)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Main.fst"
                                                                 (Prims.of_int (281))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (284))
                                                                 (Prims.of_int (29)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (27)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                              (Obj.magic
                                                                 (Pulse_Syntax_Printer.st_term_to_string
                                                                    t))
                                                              (fun uu___2 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "incremental tc, t: "
                                                                    (Prims.strcat
                                                                    uu___2
                                                                    "\n, t0: "))
                                                                    (Prims.strcat
                                                                    x
                                                                    "\n, t1:"))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                        (fun uu___2 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                uu___2 uu___1))))
                                                  uu___1)))
                                       (fun uu___1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 -> uu___1 uu___))))
                                 uu___)))
                      (fun uu___ ->
                         (fun uu___ ->
                            Obj.magic (FStar_Tactics_V2_Builtins.print uu___))
                           uu___)))
                (fun uu___ ->
                   (fun uu___ ->
                      match ((t0.Pulse_Syntax_Base.term1),
                              (t1.Pulse_Syntax_Base.term1))
                      with
                      | (Pulse_Syntax_Base.Tm_Bind uu___1,
                         Pulse_Syntax_Base.Tm_Bind uu___2) ->
                          Obj.magic
                            (Obj.repr (incremental_tc_bind0 g t c d t0 t1))
                      | (Pulse_Syntax_Base.Tm_TotBind uu___1,
                         Pulse_Syntax_Base.Tm_TotBind uu___2) ->
                          Obj.magic
                            (Obj.repr (incremental_tc_bind0 g t c d t0 t1))
                      | (Pulse_Syntax_Base.Tm_Admit uu___1, uu___2) ->
                          Obj.magic
                            (Obj.repr (incremental_tc_admit g t c d t0 t1))
                      | (Pulse_Syntax_Base.Tm_Abs
                         { Pulse_Syntax_Base.b = uu___1;
                           Pulse_Syntax_Base.q = uu___2;
                           Pulse_Syntax_Base.ascription = uu___3;
                           Pulse_Syntax_Base.body = body0;_},
                         Pulse_Syntax_Base.Tm_Abs
                         { Pulse_Syntax_Base.b = uu___4;
                           Pulse_Syntax_Base.q = uu___5;
                           Pulse_Syntax_Base.ascription = uu___6;
                           Pulse_Syntax_Base.body = body1;_})
                          ->
                          Obj.magic
                            (Obj.repr
                               (match d with
                                | Pulse_Typing.T_Abs
                                    (uu___7, x, q, b, u, body, c1, d_bt,
                                     d_body)
                                    ->
                                    Obj.repr
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Main.fst"
                                                  (Prims.of_int (298))
                                                  (Prims.of_int (16))
                                                  (Prims.of_int (298))
                                                  (Prims.of_int (60)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Main.fst"
                                                  (Prims.of_int (298))
                                                  (Prims.of_int (63))
                                                  (Prims.of_int (307))
                                                  (Prims.of_int (71)))))
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___8 ->
                                               Pulse_Typing_Env.push_binding
                                                 g x
                                                 b.Pulse_Syntax_Base.binder_ppname
                                                 b.Pulse_Syntax_Base.binder_ty))
                                         (fun uu___8 ->
                                            (fun g' ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Main.fst"
                                                             (Prims.of_int (299))
                                                             (Prims.of_int (19))
                                                             (Prims.of_int (299))
                                                             (Prims.of_int (61)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Main.fst"
                                                             (Prims.of_int (299))
                                                             (Prims.of_int (64))
                                                             (Prims.of_int (307))
                                                             (Prims.of_int (71)))))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___8 ->
                                                          Pulse_Syntax_Naming.open_st_term_nv
                                                            body0
                                                            ((b.Pulse_Syntax_Base.binder_ppname),
                                                              x)))
                                                    (fun uu___8 ->
                                                       (fun body01 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (61)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (71)))))
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___8
                                                                    ->
                                                                    Pulse_Syntax_Naming.open_st_term_nv
                                                                    body1
                                                                    ((b.Pulse_Syntax_Base.binder_ppname),
                                                                    x)))
                                                               (fun uu___8 ->
                                                                  (fun body11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (incremental_tc
                                                                    (Pulse_Typing_Env.push_binding
                                                                    uu___7 x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    b.Pulse_Syntax_Base.binder_ty)
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    body
                                                                    ((b.Pulse_Syntax_Base.binder_ppname),
                                                                    x)) c1
                                                                    d_body
                                                                    body01
                                                                    body11))
                                                                    (fun ropt
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match ropt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (body2,
                                                                    body_typing))
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    ((Pulse_Typing.wtag
                                                                    FStar_Pervasives_Native.None
                                                                    (Pulse_Syntax_Base.Tm_Abs
                                                                    {
                                                                    Pulse_Syntax_Base.b
                                                                    = b;
                                                                    Pulse_Syntax_Base.q
                                                                    = q;
                                                                    Pulse_Syntax_Base.ascription
                                                                    =
                                                                    Pulse_Syntax_Base.empty_ascription;
                                                                    Pulse_Syntax_Base.body
                                                                    =
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body2 x)
                                                                    })),
                                                                    (Pulse_Typing.T_Abs
                                                                    (uu___7,
                                                                    x, q, b,
                                                                    u,
                                                                    (Pulse_Syntax_Naming.close_st_term
                                                                    body2 x),
                                                                    c1, (),
                                                                    body_typing))))))))
                                                                    uu___8)))
                                                         uu___8))) uu___8))
                                | uu___7 ->
                                    Obj.repr
                                      (FStar_Tactics_V2_Derived.fail
                                         "Expected T_Abs")))
                      | (uu___1, uu___2) ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (312))
                                           (Prims.of_int (4))
                                           (Prims.of_int (314))
                                           (Prims.of_int (37)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (315))
                                           (Prims.of_int (4))
                                           (Prims.of_int (315))
                                           (Prims.of_int (22)))))
                                  (Obj.magic
                                     (FStar_Tactics_V2_Builtins.print
                                        (Prims.strcat
                                           (Prims.strcat
                                              "Unhandled case with t0 and t1: "
                                              (Prims.strcat
                                                 (Pulse_Syntax_Printer.tag_of_st_term
                                                    t0) " and "))
                                           (Prims.strcat
                                              (Pulse_Syntax_Printer.tag_of_st_term
                                                 t1) "\n"))))
                                  (fun uu___3 ->
                                     FStar_Tactics_V2_Derived.fail
                                       "main fail")))) uu___)
and (incremental_tc_trivial :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (Pulse_Typing_Env.env ->
             Pulse_Syntax_Base.st_term ->
               Pulse_Syntax_Base.comp_st ->
                 (unit, unit, unit) Pulse_Typing.st_typing ->
                   ((Pulse_Syntax_Base.st_term,
                      (unit, unit, unit) Pulse_Typing.st_typing)
                      Prims.dtuple2 FStar_Pervasives_Native.option,
                     unit) FStar_Tactics_Effect.tac_repr)
            ->
            ((Pulse_Syntax_Base.st_term,
               (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2
               FStar_Pervasives_Native.option,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun c ->
        fun d ->
          fun f ->
            match d with
            | Pulse_Typing.T_Sub (g1, e, c1, c', e_typing, st_sub_typing) ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (327)) (Prims.of_int (17))
                           (Prims.of_int (327)) (Prims.of_int (27)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (328)) (Prims.of_int (6))
                           (Prims.of_int (331)) (Prims.of_int (22)))))
                  (Obj.magic (f g1 e c1 e_typing))
                  (fun ropt ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          match ropt with
                          | FStar_Pervasives_Native.Some (Prims.Mkdtuple2
                              (e1, e_typing1)) ->
                              FStar_Pervasives_Native.Some
                                (Prims.Mkdtuple2
                                   (e1,
                                     (Pulse_Typing.T_Sub
                                        (g1, e1, c1, c', e_typing1,
                                          st_sub_typing))))
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None))
            | Pulse_Typing.T_Equiv (g1, e, c1, c', e_typing, d_equiv) ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (336)) (Prims.of_int (17))
                           (Prims.of_int (336)) (Prims.of_int (27)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (337)) (Prims.of_int (6))
                           (Prims.of_int (340)) (Prims.of_int (20)))))
                  (Obj.magic (f g1 e c1 e_typing))
                  (fun ropt ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          match ropt with
                          | FStar_Pervasives_Native.Some (Prims.Mkdtuple2
                              (e1, e_typing1)) ->
                              FStar_Pervasives_Native.Some
                                (Prims.Mkdtuple2
                                   (e1,
                                     (Pulse_Typing.T_Equiv
                                        (g1, e1, c1, c', e_typing1, d_equiv))))
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None))
            | Pulse_Typing.T_Frame (g1, e, c1, frame, frame_typing, e_typing)
                ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (345)) (Prims.of_int (17))
                           (Prims.of_int (345)) (Prims.of_int (27)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (346)) (Prims.of_int (6))
                           (Prims.of_int (349)) (Prims.of_int (20)))))
                  (Obj.magic (f g1 e c1 e_typing))
                  (fun ropt ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          match ropt with
                          | FStar_Pervasives_Native.Some (Prims.Mkdtuple2
                              (e1, e_typing1)) ->
                              FStar_Pervasives_Native.Some
                                (Prims.Mkdtuple2
                                   (e1,
                                     (Pulse_Typing.T_Frame
                                        (g1, e1, c1, frame, (), e_typing1))))
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None))
let (try_incremental_checking :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.decl ->
      ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
         (unit, unit, unit) Pulse_Typing.st_typing) FStar_Pervasives.dtuple3
         FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun d ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (357))
                 (Prims.of_int (13)) (Prims.of_int (357)) (Prims.of_int (65)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (358))
                 (Prims.of_int (2)) (Prims.of_int (380)) (Prims.of_int (45)))))
        (Obj.magic
           (Pulse_RuntimeUtils.get_extension_state
              (Pulse_Typing_Env.fstar_env g)))
        (fun uu___ ->
           (fun copt ->
              match copt with
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Main.fst"
                                (Prims.of_int (360)) (Prims.of_int (4))
                                (Prims.of_int (360)) (Prims.of_int (71)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Main.fst"
                                (Prims.of_int (361)) (Prims.of_int (4))
                                (Prims.of_int (361)) (Prims.of_int (8)))))
                       (Obj.magic
                          (FStar_Tactics_V2_Builtins.print
                             "Could not find anything in the cache, not incremental\n"))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> FStar_Pervasives_Native.None)))
              | FStar_Pervasives_Native.Some { cache_decl; cache_typing;_} ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Main.fst"
                                (Prims.of_int (363)) (Prims.of_int (4))
                                (Prims.of_int (363)) (Prims.of_int (66)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Main.fst"
                                (Prims.of_int (363)) (Prims.of_int (67))
                                (Prims.of_int (380)) (Prims.of_int (45)))))
                       (Obj.magic
                          (FStar_Tactics_V2_Builtins.print
                             "Found something in the cache, trying incremental\n"))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (364))
                                           (Prims.of_int (86))
                                           (Prims.of_int (364))
                                           (Prims.of_int (96)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (363))
                                           (Prims.of_int (67))
                                           (Prims.of_int (380))
                                           (Prims.of_int (45)))))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> cache_decl))
                                  (fun uu___1 ->
                                     (fun uu___1 ->
                                        match uu___1 with
                                        | Pulse_Syntax_Base.FnDecl
                                            { Pulse_Syntax_Base.id = id0;
                                              Pulse_Syntax_Base.isrec =
                                                isrec0;
                                              Pulse_Syntax_Base.bs = bs0;
                                              Pulse_Syntax_Base.comp = comp0;
                                              Pulse_Syntax_Base.meas = meas0;
                                              Pulse_Syntax_Base.body7 = body0;_}
                                            ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (365))
                                                          (Prims.of_int (86))
                                                          (Prims.of_int (365))
                                                          (Prims.of_int (89)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (364))
                                                          (Prims.of_int (99))
                                                          (Prims.of_int (380))
                                                          (Prims.of_int (45)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 ->
                                                       d.Pulse_Syntax_Base.d))
                                                 (fun uu___2 ->
                                                    (fun uu___2 ->
                                                       match uu___2 with
                                                       | Pulse_Syntax_Base.FnDecl
                                                           {
                                                             Pulse_Syntax_Base.id
                                                               = id1;
                                                             Pulse_Syntax_Base.isrec
                                                               = isrec1;
                                                             Pulse_Syntax_Base.bs
                                                               = bs1;
                                                             Pulse_Syntax_Base.comp
                                                               = comp1;
                                                             Pulse_Syntax_Base.meas
                                                               = meas1;
                                                             Pulse_Syntax_Base.body7
                                                               = body1;_}
                                                           ->
                                                           (match is_incremental_st_term
                                                                    body0
                                                                    body1
                                                            with
                                                            | FStar_Pervasives_Native.None
                                                                ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives_Native.None)))
                                                            | FStar_Pervasives_Native.Some
                                                                e ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (89)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    e))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "Incremental with e as "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    "\n")))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___3))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    cache_typing))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g_c,
                                                                    t_c, c_c,
                                                                    d1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (102)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (378))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (102)))))
                                                                    (Obj.magic
                                                                    (mk_abs g
                                                                    bs0 body0
                                                                    comp0))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (102)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (102)))))
                                                                    (Obj.magic
                                                                    (mk_abs g
                                                                    bs1 body1
                                                                    comp1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (incremental_tc
                                                                    g_c t_c
                                                                    c_c d1
                                                                    uu___5
                                                                    uu___6))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    (fun ropt
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match ropt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (Prims.Mkdtuple2
                                                                    (uu___6,
                                                                    d2)) ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (uu___6,
                                                                    c_c, d2))))))
                                                                    uu___4)))
                                                                    uu___3)))))
                                                      uu___2))) uu___1)))
                            uu___))) uu___)
let (check_fndecl :
  Pulse_Syntax_Base.decl ->
    Pulse_Soundness_Common.stt_env ->
      Pulse_Syntax_Base.term ->
        unit ->
          (unit FStar_Reflection_Typing.dsl_tac_result_t, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun d ->
    fun g ->
      fun pre ->
        fun pre_typing ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (391))
                     (Prims.of_int (20)) (Prims.of_int (391))
                     (Prims.of_int (23)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (388))
                     Prims.int_one (Prims.of_int (463)) (Prims.of_int (30)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> d.Pulse_Syntax_Base.d))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | Pulse_Syntax_Base.FnDecl fn_d ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Main.fst"
                                    (Prims.of_int (392)) (Prims.of_int (16))
                                    (Prims.of_int (392)) (Prims.of_int (43)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Main.fst"
                                    (Prims.of_int (392)) (Prims.of_int (46))
                                    (Prims.of_int (463)) (Prims.of_int (30)))))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 FStar_Pervasives_Native.fst
                                   (FStar_Reflection_V2_Builtins.inspect_ident
                                      fn_d.Pulse_Syntax_Base.id)))
                           (fun uu___1 ->
                              (fun nm_orig ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (394))
                                               (Prims.of_int (4))
                                               (Prims.of_int (396))
                                               (Prims.of_int (10)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (397))
                                               (Prims.of_int (4))
                                               (Prims.of_int (463))
                                               (Prims.of_int (30)))))
                                      (if fn_d.Pulse_Syntax_Base.isrec
                                       then
                                         Obj.magic
                                           (Obj.repr
                                              (Pulse_Recursion.add_knot g
                                                 d.Pulse_Syntax_Base.range3 d))
                                       else
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 -> d))))
                                      (fun uu___1 ->
                                         (fun d1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (399))
                                                          (Prims.of_int (51))
                                                          (Prims.of_int (399))
                                                          (Prims.of_int (54)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (397))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (463))
                                                          (Prims.of_int (30)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       d1.Pulse_Syntax_Base.d))
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       match uu___1 with
                                                       | Pulse_Syntax_Base.FnDecl
                                                           {
                                                             Pulse_Syntax_Base.id
                                                               = id;
                                                             Pulse_Syntax_Base.isrec
                                                               = isrec;
                                                             Pulse_Syntax_Base.bs
                                                               = bs;
                                                             Pulse_Syntax_Base.comp
                                                               = comp;
                                                             Pulse_Syntax_Base.meas
                                                               = meas;
                                                             Pulse_Syntax_Base.body7
                                                               = body;_}
                                                           ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (37)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (30)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives_Native.fst
                                                                    (FStar_Reflection_V2_Builtins.inspect_ident
                                                                    id)))
                                                                (fun uu___2
                                                                   ->
                                                                   (fun
                                                                    nm_aux ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (30)))))
                                                                    (if
                                                                    Prims.uu___is_Nil
                                                                    bs
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (d1.Pulse_Syntax_Base.range3))
                                                                    "main: FnDecl does not have binders"))
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
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    body.Pulse_Syntax_Base.range2))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun rng
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (try_incremental_checking
                                                                    g d1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (r, true))))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (mk_abs g
                                                                    bs body
                                                                    comp))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    tm_abs ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (102)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (debug_main
                                                                    g
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    tm_abs))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "\nbody after mk_abs:\n"
                                                                    (Prims.strcat
                                                                    uu___5
                                                                    "\n"))))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Abs.check_abs
                                                                    g tm_abs
                                                                    Pulse_Checker.check))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (uu___5,
                                                                    false)))))
                                                                    uu___4)))
                                                                    uu___4))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (tm_abs,
                                                                    c,
                                                                    t_typing),
                                                                    incr) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (Pulse_RuntimeUtils.set_extension_state
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g)
                                                                    {
                                                                    cache_decl
                                                                    =
                                                                    (d1.Pulse_Syntax_Base.d);
                                                                    cache_typing
                                                                    =
                                                                    (FStar_Pervasives.Mkdtuple4
                                                                    (g,
                                                                    tm_abs,
                                                                    c,
                                                                    t_typing))
                                                                    }))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (Pulse_Checker_Prover_Util.debug_prover
                                                                    g
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.comp_to_string
                                                                    c))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    tm_abs))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "\ncheck call returned in main with:\n"
                                                                    (Prims.strcat
                                                                    uu___7
                                                                    "\nat type "))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    uu___7
                                                                    uu___6))))
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (debug_main
                                                                    g
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Printer.print_st_typing
                                                                    g tm_abs
                                                                    c
                                                                    t_typing))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    tm_abs))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun x ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "\nchecker call returned in main with:\n"
                                                                    (Prims.strcat
                                                                    uu___8
                                                                    "\nderivation="))
                                                                    (Prims.strcat
                                                                    x "\n")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___8
                                                                    uu___7))))
                                                                    uu___7))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.st_term_to_string
                                                                    tm_abs))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "Elaborated ("
                                                                    (Prims.strcat
                                                                    (if incr
                                                                    then
                                                                    "incremental"
                                                                    else
                                                                    "not-incremental")
                                                                    "): "))
                                                                    (Prims.strcat
                                                                    uu___7
                                                                    "\n")))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    uu___7))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_Elaborate_Pure.elab_comp
                                                                    c))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    refl_t ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Pulse_RuntimeUtils.embed_st_term_for_extraction
                                                                    tm_abs
                                                                    (FStar_Pervasives_Native.Some
                                                                    rng)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    refl_e ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ("pulse",
                                                                    refl_e)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun blob
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (435))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pervasives_Native.fst
                                                                    (FStar_Reflection_V2_Builtins.inspect_ident
                                                                    id)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun nm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (94)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.ext_getv
                                                                    "pulse:elab_derivation"))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___8 <>
                                                                    ""))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    if uu___8
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Reflection_Typing.mk_checked_let
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g) nm
                                                                    (Pulse_Elaborate_Core.elab_st_typing
                                                                    g tm_abs
                                                                    c
                                                                    t_typing)
                                                                    refl_t)
                                                                    else
                                                                    Obj.magic
                                                                    (Pulse_Reflection_Util.mk_opaque_let
                                                                    (Pulse_Typing_Env.fstar_env
                                                                    g) nm ()
                                                                    refl_t))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    main_decl
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match main_decl
                                                                    with
                                                                    | 
                                                                    (chk, se,
                                                                    uu___9)
                                                                    ->
                                                                    (chk,
                                                                    (if
                                                                    fn_d.Pulse_Syntax_Base.isrec
                                                                    then
                                                                    Pulse_RuntimeUtils.add_attribute
                                                                    (Pulse_RuntimeUtils.add_noextract_qual
                                                                    (Pulse_RuntimeUtils.add_attribute
                                                                    se
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "noextract_to"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    (FStar_Reflection_V2_Data.C_String
                                                                    "krml"))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))))
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    (FStar_Reflection_V2_Data.C_String
                                                                    "pulse.recursive"))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    (FStar_Reflection_V2_Data.C_String
                                                                    nm_orig))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))
                                                                    else se),
                                                                    (FStar_Pervasives_Native.Some
                                                                    blob))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    main_decl1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (461))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (30)))))
                                                                    (if
                                                                    fn_d.Pulse_Syntax_Base.isrec
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Recursion.tie_knot
                                                                    g rng
                                                                    nm_orig
                                                                    nm_aux d1
                                                                    refl_t
                                                                    blob))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    []))))
                                                                    (fun
                                                                    recursive_decls
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    main_decl1
                                                                    ::
                                                                    recursive_decls))))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                      uu___1))) uu___1)))
                                uu___1))) uu___)
let (main' :
  Prims.string ->
    Pulse_Syntax_Base.decl ->
      Pulse_Syntax_Base.term ->
        FStar_Reflection_Typing.fstar_top_env ->
          (unit FStar_Reflection_Typing.dsl_tac_result_t, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun nm ->
             fun d ->
               fun pre ->
                 fun g ->
                   match Pulse_Soundness_Common.check_top_level_environment g
                   with
                   | FStar_Pervasives_Native.None ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_V2_Derived.fail
                               "pulse main: top-level environment does not include stt at the expected types"))
                   | FStar_Pervasives_Native.Some g1 ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.Main.fst"
                                        (Prims.of_int (470))
                                        (Prims.of_int (6))
                                        (Prims.of_int (471))
                                        (Prims.of_int (88)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Pulse.Main.fst"
                                        (Prims.of_int (471))
                                        (Prims.of_int (89))
                                        (Prims.of_int (478))
                                        (Prims.of_int (39)))))
                               (if
                                  Pulse_RuntimeUtils.debug_at_level
                                    (Pulse_Typing_Env.fstar_env g1) "Pulse"
                                then
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (471))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (471))
                                                   (Prims.of_int (88)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (471))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (471))
                                                   (Prims.of_int (88)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Main.fst"
                                                         (Prims.of_int (471))
                                                         (Prims.of_int (67))
                                                         (Prims.of_int (471))
                                                         (Prims.of_int (87)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic
                                                   (Pulse_Syntax_Printer.decl_to_string
                                                      d))
                                                (fun uu___ ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___1 ->
                                                        Prims.strcat
                                                          "About to check pulse decl:\n"
                                                          (Prims.strcat uu___
                                                             "\n")))))
                                          (fun uu___ ->
                                             (fun uu___ ->
                                                Obj.magic
                                                  (FStar_Tactics_V2_Builtins.print
                                                     uu___)) uu___)))
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
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (472))
                                                   (Prims.of_int (38))
                                                   (Prims.of_int (472))
                                                   (Prims.of_int (84)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (471))
                                                   (Prims.of_int (89))
                                                   (Prims.of_int (478))
                                                   (Prims.of_int (39)))))
                                          (Obj.magic
                                             (Pulse_Checker_Pure.compute_tot_term_type
                                                g1 pre))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | FStar_Pervasives.Mkdtuple3
                                                    (pre1, ty, pre_typing) ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Main.fst"
                                                                  (Prims.of_int (473))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (474))
                                                                  (Prims.of_int (80)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Main.fst"
                                                                  (Prims.of_int (474))
                                                                  (Prims.of_int (81))
                                                                  (Prims.of_int (478))
                                                                  (Prims.of_int (39)))))
                                                         (if
                                                            Prims.op_Negation
                                                              (Pulse_Syntax_Base.eq_tm
                                                                 ty
                                                                 Pulse_Syntax_Base.tm_vprop)
                                                          then
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (Pulse_Typing_Env.fail
                                                                    g1
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    (pre1.Pulse_Syntax_Base.range1))
                                                                    "pulse main: cannot typecheck pre at type vprop"))
                                                          else
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    ()))))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (61)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (39)))))
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    pre_typing1
                                                                    ->
                                                                    match 
                                                                    d.Pulse_Syntax_Base.d
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.FnDecl
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (check_fndecl
                                                                    d g1 pre1
                                                                    ()))
                                                                    uu___3)))
                                                              uu___2)))
                                               uu___1))) uu___)))) uu___3
            uu___2 uu___1 uu___
let (join_smt_goals : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (484))
               (Prims.of_int (2)) (Prims.of_int (485)) (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (485))
               (Prims.of_int (36)) (Prims.of_int (506)) (Prims.of_int (4)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (484))
                     (Prims.of_int (5)) (Prims.of_int (484))
                     (Prims.of_int (48)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (484))
                     (Prims.of_int (2)) (Prims.of_int (485))
                     (Prims.of_int (35)))))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (484)) (Prims.of_int (23))
                           (Prims.of_int (484)) (Prims.of_int (35)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (484)) (Prims.of_int (5))
                           (Prims.of_int (484)) (Prims.of_int (48)))))
                  (Obj.magic (FStar_Tactics_V2_Builtins.top_env ()))
                  (fun uu___1 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___2 ->
                          Pulse_RuntimeUtils.debug_at_level uu___1
                            "pulse.join"))))
            (fun uu___1 ->
               (fun uu___1 ->
                  if uu___1
                  then
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_V2_Builtins.dump
                            "PULSE: Goals before join"))
                  else
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> ())))) uu___1)))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (488)) (Prims.of_int (18))
                          (Prims.of_int (488)) (Prims.of_int (30)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (489)) (Prims.of_int (2))
                          (Prims.of_int (506)) (Prims.of_int (4)))))
                 (Obj.magic (FStar_Tactics_V2_Derived.smt_goals ()))
                 (fun uu___2 ->
                    (fun smt_goals ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (489)) (Prims.of_int (2))
                                     (Prims.of_int (489)) (Prims.of_int (34)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (490)) (Prims.of_int (2))
                                     (Prims.of_int (506)) (Prims.of_int (4)))))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (489))
                                           (Prims.of_int (12))
                                           (Prims.of_int (489))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (489))
                                           (Prims.of_int (2))
                                           (Prims.of_int (489))
                                           (Prims.of_int (34)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (489))
                                                 (Prims.of_int (13))
                                                 (Prims.of_int (489))
                                                 (Prims.of_int (21)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (489))
                                                 (Prims.of_int (12))
                                                 (Prims.of_int (489))
                                                 (Prims.of_int (34)))))
                                        (Obj.magic
                                           (FStar_Tactics_V2_Derived.goals ()))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                FStar_List_Tot_Base.op_At
                                                  uu___2 smt_goals))))
                                  (fun uu___2 ->
                                     (fun uu___2 ->
                                        Obj.magic
                                          (FStar_Tactics_V2_Builtins.set_goals
                                             uu___2)) uu___2)))
                            (fun uu___2 ->
                               (fun uu___2 ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (490))
                                                (Prims.of_int (2))
                                                (Prims.of_int (490))
                                                (Prims.of_int (18)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (490))
                                                (Prims.of_int (19))
                                                (Prims.of_int (506))
                                                (Prims.of_int (4)))))
                                       (Obj.magic
                                          (FStar_Tactics_V2_Builtins.set_smt_goals
                                             []))
                                       (fun uu___3 ->
                                          (fun uu___3 ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (491))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (491))
                                                           (Prims.of_int (36)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (492))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (506))
                                                           (Prims.of_int (4)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Main.fst"
                                                                 (Prims.of_int (491))
                                                                 (Prims.of_int (26))
                                                                 (Prims.of_int (491))
                                                                 (Prims.of_int (36)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Main.fst"
                                                                 (Prims.of_int (491))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (491))
                                                                 (Prims.of_int (36)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_V2_Derived.goals
                                                              ()))
                                                        (fun uu___4 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___5 ->
                                                                FStar_List_Tot_Base.length
                                                                  uu___4))))
                                                  (fun uu___4 ->
                                                     (fun n ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (22)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (4)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (22)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (22)))))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.repeat
                                                                    FStar_Tactics_V2_Builtins.join))
                                                                   (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ()))))
                                                             (fun uu___4 ->
                                                                (fun uu___4
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (4)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.goals
                                                                    ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.uu___is_Nil
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.op_Negation
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    if uu___5
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_SMT.get_rlimit
                                                                    ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___6 +
                                                                    ((n -
                                                                    Prims.int_one)
                                                                    *
                                                                    (Prims.of_int (2)))))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    rlimit ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_SMT.set_rlimit
                                                                    rlimit))
                                                                    uu___6)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ()))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (4)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (503))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.top_env
                                                                    ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_RuntimeUtils.debug_at_level
                                                                    uu___6
                                                                    "pulse.join"))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    if uu___6
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Builtins.dump
                                                                    "PULSE: Goals after join"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ()))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ()))))
                                                                    uu___5)))
                                                                  uu___4)))
                                                       uu___4))) uu___3)))
                                 uu___2))) uu___2))) uu___1)
let (main :
  Prims.string ->
    Pulse_Syntax_Base.decl ->
      Pulse_Syntax_Base.term -> FStar_Reflection_Typing.dsl_tac_t)
  =
  fun nm ->
    fun t ->
      fun pre ->
        fun g ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (513))
                     (Prims.of_int (2)) (Prims.of_int (516))
                     (Prims.of_int (24)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (516))
                     (Prims.of_int (25)) (Prims.of_int (525))
                     (Prims.of_int (5)))))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (513)) (Prims.of_int (5))
                           (Prims.of_int (513)) (Prims.of_int (46)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (513)) (Prims.of_int (2))
                           (Prims.of_int (516)) (Prims.of_int (24)))))
                  (Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Main.fst"
                                 (Prims.of_int (513)) (Prims.of_int (5))
                                 (Prims.of_int (513)) (Prims.of_int (34)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Main.fst"
                                 (Prims.of_int (513)) (Prims.of_int (5))
                                 (Prims.of_int (513)) (Prims.of_int (46)))))
                        (Obj.magic
                           (FStar_Tactics_V2_Builtins.ext_getv
                              "pulse:guard_policy"))
                        (fun uu___ ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 -> uu___ = "SMTSync"))))
                  (fun uu___ ->
                     (fun uu___ ->
                        if uu___
                        then
                          Obj.magic
                            (FStar_Tactics_V2_Builtins.set_guard_policy
                               FStar_Tactics_Types.SMTSync)
                        else
                          Obj.magic
                            (FStar_Tactics_V2_Builtins.set_guard_policy
                               FStar_Tactics_Types.SMT)) uu___)))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Main.fst"
                                (Prims.of_int (518)) (Prims.of_int (12))
                                (Prims.of_int (518)) (Prims.of_int (28)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Main.fst"
                                (Prims.of_int (520)) (Prims.of_int (2))
                                (Prims.of_int (525)) (Prims.of_int (5)))))
                       (Obj.magic (main' nm t pre g))
                       (fun uu___1 ->
                          (fun res ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (520))
                                           (Prims.of_int (2))
                                           (Prims.of_int (524))
                                           (Prims.of_int (20)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Main.fst"
                                           (Prims.of_int (518))
                                           (Prims.of_int (6))
                                           (Prims.of_int (518))
                                           (Prims.of_int (9)))))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (520))
                                                 (Prims.of_int (5))
                                                 (Prims.of_int (520))
                                                 (Prims.of_int (32)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Main.fst"
                                                 (Prims.of_int (520))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (524))
                                                 (Prims.of_int (20)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Main.fst"
                                                       (Prims.of_int (520))
                                                       (Prims.of_int (5))
                                                       (Prims.of_int (520))
                                                       (Prims.of_int (26)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Main.fst"
                                                       (Prims.of_int (520))
                                                       (Prims.of_int (5))
                                                       (Prims.of_int (520))
                                                       (Prims.of_int (32)))))
                                              (Obj.magic
                                                 (FStar_Tactics_V2_Builtins.ext_getv
                                                    "pulse:join"))
                                              (fun uu___1 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      uu___1 = "1"))))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              if uu___1
                                              then
                                                Obj.magic
                                                  (Obj.repr
                                                     (join_smt_goals ()))
                                              else
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 -> ()))))
                                             uu___1)))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> res)))) uu___1))) uu___)
let (check_pulse :
  Prims.string Prims.list ->
    (Prims.string * Prims.string) Prims.list ->
      Prims.string ->
        Prims.string ->
          Prims.int ->
            Prims.int -> Prims.string -> FStar_Reflection_Typing.dsl_tac_t)
  =
  fun namespaces ->
    fun module_abbrevs ->
      fun content ->
        fun file_name ->
          fun line ->
            fun col ->
              fun nm ->
                fun env ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Main.fst"
                             (Prims.of_int (536)) (Prims.of_int (12))
                             (Prims.of_int (536)) (Prims.of_int (112)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Main.fst"
                             (Prims.of_int (536)) (Prims.of_int (6))
                             (Prims.of_int (552)) (Prims.of_int (36)))))
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          PulseSyntaxExtension_ASTBuilder.parse_pulse env
                            namespaces module_abbrevs content file_name line
                            col))
                    (fun uu___ ->
                       (fun uu___ ->
                          match uu___ with
                          | FStar_Pervasives.Inl decl ->
                              Obj.magic
                                (Obj.repr
                                   (main nm decl Pulse_Syntax_Base.tm_emp env))
                          | FStar_Pervasives.Inr
                              (FStar_Pervasives_Native.None) ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_V2_Derived.fail
                                      "Pulse parser failed"))
                          | FStar_Pervasives.Inr
                              (FStar_Pervasives_Native.Some (msg, range)) ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (545))
                                               (Prims.of_int (10))
                                               (Prims.of_int (549))
                                               (Prims.of_int (21)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (551))
                                               (Prims.of_int (8))
                                               (Prims.of_int (552))
                                               (Prims.of_int (36)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Main.fst"
                                                     (Prims.of_int (546))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (546))
                                                     (Prims.of_int (74)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Issue.fsti"
                                                     (Prims.of_int (49))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (49))
                                                     (Prims.of_int (65)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (546))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (546))
                                                           (Prims.of_int (74)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (546))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (546))
                                                           (Prims.of_int (74)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Main.fst"
                                                                 (Prims.of_int (546))
                                                                 (Prims.of_int (44))
                                                                 (Prims.of_int (546))
                                                                 (Prims.of_int (69)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Printf.fst"
                                                                 (Prims.of_int (122))
                                                                 (Prims.of_int (8))
                                                                 (Prims.of_int (124))
                                                                 (Prims.of_int (44)))))
                                                        (Obj.magic
                                                           (FStar_Tactics_V2_Builtins.range_to_string
                                                              range))
                                                        (fun uu___1 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___2 ->
                                                                fun x ->
                                                                  Prims.strcat
                                                                    (
                                                                    Prims.strcat
                                                                    ""
                                                                    (Prims.strcat
                                                                    uu___1
                                                                    ": "))
                                                                    (
                                                                    Prims.strcat
                                                                    x "")))))
                                                  (fun uu___1 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___2 ->
                                                          uu___1 msg))))
                                            (fun uu___1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    FStar_Issue.mk_issue_doc
                                                      "Error"
                                                      [FStar_Pprint.arbitrary_string
                                                         uu___1]
                                                      (FStar_Pervasives_Native.Some
                                                         range)
                                                      FStar_Pervasives_Native.None
                                                      []))))
                                      (fun uu___1 ->
                                         (fun i ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (551))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (551))
                                                          (Prims.of_int (24)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Main.fst"
                                                          (Prims.of_int (552))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (552))
                                                          (Prims.of_int (36)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_V2_Builtins.log_issues
                                                       [i]))
                                                 (fun uu___1 ->
                                                    FStar_Tactics_V2_Derived.fail
                                                      "Pulse parser failed")))
                                           uu___1)))) uu___)
let _ =
  FStar_Tactics_Native.register_tactic "Pulse.Main.check_pulse"
    (Prims.of_int (9))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_8
               "Pulse.Main.check_pulse (plugin)"
               (FStar_Tactics_Native.from_tactic_8 check_pulse)
               (FStar_Syntax_Embeddings.e_list
                  FStar_Syntax_Embeddings.e_string)
               (FStar_Syntax_Embeddings.e_list
                  (FStar_Syntax_Embeddings.e_tuple2
                     FStar_Syntax_Embeddings.e_string
                     FStar_Syntax_Embeddings.e_string))
               FStar_Syntax_Embeddings.e_string
               FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_int
               FStar_Syntax_Embeddings.e_int FStar_Syntax_Embeddings.e_string
               FStar_Reflection_V2_Embeddings.e_env
               (FStar_Syntax_Embeddings.e_list
                  (FStar_Syntax_Embeddings.e_tuple3
                     FStar_Syntax_Embeddings.e_bool
                     FStar_Reflection_V2_Embeddings.e_sigelt
                     (FStar_Syntax_Embeddings.e_option
                        (FStar_Syntax_Embeddings.e_tuple2
                           FStar_Syntax_Embeddings.e_string
                           FStar_Reflection_V2_Embeddings.e_term)))) psc ncb
               us args)