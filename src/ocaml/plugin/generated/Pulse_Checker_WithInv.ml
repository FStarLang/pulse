open Prims
let (rt_recheck :
  Pulse_Typing_Env.env ->
    FStar_Reflection_Types.env ->
      FStar_Tactics_NamedView.term ->
        FStar_Reflection_Types.typ ->
          unit ->
            ((unit, unit, unit) FStar_Reflection_Typing.tot_typing, unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun gg ->
    fun g ->
      fun e ->
        fun ty ->
          fun uu___ ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (35)) (Prims.of_int (8))
                       (Prims.of_int (35)) (Prims.of_int (42)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (35)) (Prims.of_int (2))
                       (Prims.of_int (37)) (Prims.of_int (58)))))
              (Obj.magic
                 (FStar_Tactics_V2_Builtins.core_check_term g e ty
                    FStar_TypeChecker_Core.E_Total))
              (fun uu___1 ->
                 match uu___1 with
                 | (FStar_Pervasives_Native.Some tok, uu___2) ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___3 ->
                          FStar_Reflection_Typing.T_Token
                            (g, e, (FStar_TypeChecker_Core.E_Total, ty), ()))
                 | (FStar_Pervasives_Native.None, uu___2) ->
                     FStar_Tactics_V2_Derived.fail
                       "Checker.WithInv: rt_recheck failed")
let (recheck :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.typ ->
        unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      fun ty -> fun uu___ -> Pulse_Checker_Pure.core_check_tot_term g e ty
let (remove_iname :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun inames ->
    fun i ->
      Pulse_Syntax_Pure.wr (Pulse_Reflection_Util.remove_inv_tm inames i)
        (Pulse_RuntimeUtils.range_of_term inames)
let (add_iname :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun inames ->
    fun i ->
      Pulse_Syntax_Pure.wr (Pulse_Syntax_Pure.tm_add_inv inames i)
        (Pulse_RuntimeUtils.range_of_term inames)
let (all_inames : Pulse_Syntax_Base.term) =
  Pulse_Syntax_Pure.wr Pulse_Syntax_Pure.tm_all_inames FStar_Range.range_0




let (disjointness_remove_i_i :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun inames ->
             fun i ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ())))
          uu___2 uu___1 uu___
let (add_remove_inverse :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        unit -> unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun inames ->
      fun i ->
        fun inames_typing ->
          fun i_typing ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (102)) (Prims.of_int (3))
                       (Prims.of_int (106)) (Prims.of_int (19)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                       (Prims.of_int (108)) (Prims.of_int (2))
                       (Prims.of_int (119)) (Prims.of_int (19)))))
              (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))
              (fun uu___ ->
                 (fun typing ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.WithInv.fst"
                                  (Prims.of_int (108)) (Prims.of_int (8))
                                  (Prims.of_int (108)) (Prims.of_int (61)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Checker.WithInv.fst"
                                  (Prims.of_int (108)) (Prims.of_int (2))
                                  (Prims.of_int (119)) (Prims.of_int (19)))))
                         (Obj.magic
                            (Pulse_Checker_Pure.try_check_prop_validity g
                               (Pulse_Typing.tm_inames_subset
                                  (add_iname (remove_iname inames i) i)
                                  inames) ()))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | FStar_Pervasives_Native.None ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.WithInv.fst"
                                                    (Prims.of_int (110))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (117))
                                                    (Prims.of_int (5)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Checker.WithInv.fst"
                                                    (Prims.of_int (110))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (117))
                                                    (Prims.of_int (5)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (110))
                                                          (Prims.of_int (20))
                                                          (Prims.of_int (117))
                                                          (Prims.of_int (5)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (110))
                                                          (Prims.of_int (20))
                                                          (Prims.of_int (117))
                                                          (Prims.of_int (5)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.WithInv.fst"
                                                                (Prims.of_int (112))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (116))
                                                                (Prims.of_int (65)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.WithInv.fst"
                                                                (Prims.of_int (110))
                                                                (Prims.of_int (20))
                                                                (Prims.of_int (117))
                                                                (Prims.of_int (5)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (15)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (65)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (15)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (15)))))
                                                                   (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    (add_iname
                                                                    (remove_iname
                                                                    inames i)
                                                                    i)))
                                                                   (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Inferred the following invariants were opened: ")
                                                                    uu___1))))
                                                             (fun uu___1 ->
                                                                (fun uu___1
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    inames))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "But expected to only open: ")
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___1
                                                                    uu___2))))
                                                                  uu___1)))
                                                       (fun uu___1 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               [uu___1]))))
                                                 (fun uu___1 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         (Pulse_PP.text
                                                            "Failed to prove that only the following invariants are opened")
                                                         :: uu___1))))
                                           (fun uu___1 ->
                                              (fun uu___1 ->
                                                 Obj.magic
                                                   (Pulse_Typing_Env.fail_doc
                                                      g
                                                      FStar_Pervasives_Native.None
                                                      uu___1)) uu___1)))
                               | FStar_Pervasives_Native.Some tok ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 -> ())))) uu___)))
                   uu___)
let rec (find_inv :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.term ->
          ((Pulse_Syntax_Base.term, Pulse_Syntax_Base.term, unit, unit, 
             unit) FStar_Pervasives.dtuple5 FStar_Pervasives_Native.option,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun pre ->
               fun pre_typing ->
                 fun i ->
                   match Pulse_Syntax_Pure.inspect_term pre with
                   | Pulse_Syntax_Pure.Tm_Inv (i', p) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ ->
                                  if Pulse_Syntax_Base.eq_tm i i'
                                  then
                                    FStar_Pervasives_Native.Some
                                      (FStar_Pervasives.Mkdtuple5
                                         (p, Pulse_Syntax_Pure.tm_emp, (),
                                           (), ()))
                                  else FStar_Pervasives_Native.None)))
                   | Pulse_Syntax_Pure.Tm_Star (l, r) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.WithInv.fst"
                                        (Prims.of_int (142))
                                        (Prims.of_int (10))
                                        (Prims.of_int (142))
                                        (Prims.of_int (37)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.WithInv.fst"
                                        (Prims.of_int (142))
                                        (Prims.of_int (4))
                                        (Prims.of_int (151))
                                        (Prims.of_int (17)))))
                               (Obj.magic (find_inv g l () i))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     match uu___ with
                                     | FStar_Pervasives_Native.Some res ->
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    match res with
                                                    | FStar_Pervasives.Mkdtuple5
                                                        (p, frame, uu___2,
                                                         uu___3, uu___4)
                                                        ->
                                                        FStar_Pervasives_Native.Some
                                                          (FStar_Pervasives.Mkdtuple5
                                                             (p,
                                                               (Pulse_Syntax_Pure.tm_star
                                                                  frame r),
                                                               (), (), ())))))
                                     | FStar_Pervasives_Native.None ->
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (147))
                                                          (Prims.of_int (12))
                                                          (Prims.of_int (147))
                                                          (Prims.of_int (39)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (147))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (151))
                                                          (Prims.of_int (17)))))
                                                 (Obj.magic
                                                    (find_inv g r () i))
                                                 (fun uu___1 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         match uu___1 with
                                                         | FStar_Pervasives_Native.Some
                                                             res ->
                                                             (match res with
                                                              | FStar_Pervasives.Mkdtuple5
                                                                  (p, frame,
                                                                   uu___3,
                                                                   uu___4,
                                                                   uu___5)
                                                                  ->
                                                                  FStar_Pervasives_Native.Some
                                                                    (
                                                                    FStar_Pervasives.Mkdtuple5
                                                                    (p,
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    l frame),
                                                                    (), (),
                                                                    ())))
                                                         | uu___3 ->
                                                             FStar_Pervasives_Native.None)))))
                                    uu___)))
                   | uu___ ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> FStar_Pervasives_Native.None))))
            uu___3 uu___2 uu___1 uu___
let (find_inv_post :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.universe ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            unit ->
              unit ->
                Pulse_Syntax_Base.term ->
                  ((Pulse_Syntax_Base.term, Pulse_Syntax_Base.term, unit,
                     unit, unit) FStar_Pervasives.dtuple5
                     FStar_Pervasives_Native.option,
                    unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun x ->
      fun u ->
        fun ret_ty ->
          fun post ->
            fun ret_ty_typing ->
              fun post_typing ->
                fun i ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                             (Prims.of_int (172)) (Prims.of_int (20))
                             (Prims.of_int (172)) (Prims.of_int (57)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                             (Prims.of_int (172)) (Prims.of_int (60))
                             (Prims.of_int (180)) (Prims.of_int (71)))))
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          Pulse_Syntax_Naming.open_term_nv post
                            (Pulse_Syntax_Base.ppname_default, x)))
                    (fun uu___ ->
                       (fun post_opened ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.WithInv.fst"
                                        (Prims.of_int (173))
                                        (Prims.of_int (12))
                                        (Prims.of_int (173))
                                        (Prims.of_int (50)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.WithInv.fst"
                                        (Prims.of_int (174))
                                        (Prims.of_int (2))
                                        (Prims.of_int (180))
                                        (Prims.of_int (71)))))
                               (Obj.magic
                                  (find_inv
                                     (Pulse_Typing_Env.push_binding g x
                                        Pulse_Syntax_Base.ppname_default
                                        ret_ty) post_opened () i))
                               (fun uu___ ->
                                  (fun res ->
                                     match res with
                                     | FStar_Pervasives_Native.None ->
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___ ->
                                                    FStar_Pervasives_Native.None)))
                                     | FStar_Pervasives_Native.Some
                                         (FStar_Pervasives.Mkdtuple5
                                         (p, frame, inv_typing, frame_typing,
                                          d_eq))
                                         ->
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (177))
                                                          (Prims.of_int (53))
                                                          (Prims.of_int (177))
                                                          (Prims.of_int (65)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.WithInv.fst"
                                                          (Prims.of_int (178))
                                                          (Prims.of_int (55))
                                                          (Prims.of_int (180))
                                                          (Prims.of_int (71)))))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___ -> ()))
                                                 (fun uu___ ->
                                                    (fun frame_typing1 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (71)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (71)))))
                                                            (Obj.magic
                                                               (recheck g
                                                                  (Pulse_Syntax_Pure.tm_inv
                                                                    i p)
                                                                  Pulse_Syntax_Pure.tm_vprop
                                                                  ()))
                                                            (fun
                                                               tm_inv_typing
                                                               ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p,
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    frame x),
                                                                    (), (),
                                                                    ()))))))
                                                      uu___)))) uu___)))
                         uu___)
let (atomic_or_ghost_with_inames_and_pre_post :
  Pulse_Syntax_Base.comp ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp)
  =
  fun c ->
    fun inames ->
      fun pre ->
        fun post ->
          match c with
          | Pulse_Syntax_Base.C_STAtomic (uu___, obs, s) ->
              Pulse_Syntax_Base.C_STAtomic
                (inames, obs,
                  {
                    Pulse_Syntax_Base.u = (s.Pulse_Syntax_Base.u);
                    Pulse_Syntax_Base.res = (s.Pulse_Syntax_Base.res);
                    Pulse_Syntax_Base.pre = pre;
                    Pulse_Syntax_Base.post = post
                  })
          | Pulse_Syntax_Base.C_STGhost (uu___, s) ->
              Pulse_Syntax_Base.C_STGhost
                (inames,
                  {
                    Pulse_Syntax_Base.u = (s.Pulse_Syntax_Base.u);
                    Pulse_Syntax_Base.res = (s.Pulse_Syntax_Base.res);
                    Pulse_Syntax_Base.pre = pre;
                    Pulse_Syntax_Base.post = post
                  })
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
                        (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                           (Prims.of_int (202)) (Prims.of_int (47))
                           (Prims.of_int (202)) (Prims.of_int (53)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Checker.WithInv.fst"
                           (Prims.of_int (202)) Prims.int_one
                           (Prims.of_int (396)) (Prims.of_int (57)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ -> t.Pulse_Syntax_Base.term1))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | Pulse_Syntax_Base.Tm_WithInv
                            { Pulse_Syntax_Base.name1 = i;
                              Pulse_Syntax_Base.body6 = body;
                              Pulse_Syntax_Base.returns_inv = returns_inv;_}
                            ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithInv.fst"
                                          (Prims.of_int (203))
                                          (Prims.of_int (19))
                                          (Prims.of_int (203))
                                          (Prims.of_int (50)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.WithInv.fst"
                                          (Prims.of_int (202))
                                          (Prims.of_int (56))
                                          (Prims.of_int (396))
                                          (Prims.of_int (57)))))
                                 (Obj.magic
                                    (Pulse_Checker_Pure.check_tot_term g i
                                       Pulse_Syntax_Pure.tm_iname_ref))
                                 (fun uu___1 ->
                                    (fun uu___1 ->
                                       match uu___1 with
                                       | Prims.Mkdtuple2 (i1, uu___2) ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.WithInv.fst"
                                                         (Prims.of_int (204))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (204))
                                                         (Prims.of_int (50)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.WithInv.fst"
                                                         (Prims.of_int (204))
                                                         (Prims.of_int (53))
                                                         (Prims.of_int (396))
                                                         (Prims.of_int (57)))))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___3 ->
                                                      Pulse_RuntimeUtils.range_of_term
                                                        i1))
                                                (fun uu___3 ->
                                                   (fun i_range ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (33)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                           (Obj.magic
                                                              (find_inv g pre
                                                                 () i1))
                                                           (fun uu___3 ->
                                                              (fun res ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    res
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    i1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Cannot find invariant resource for iref ")
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    pre))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    " in the precondition ")
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___3
                                                                    uu___4))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    [uu___3]))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    i_range)
                                                                    uu___3))
                                                                    uu___3)))
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
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    res))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p,
                                                                    pre_frame,
                                                                    inv_typing,
                                                                    pre_frame_typing,
                                                                    d_pre_frame_eq))
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (match 
                                                                    (returns_inv,
                                                                    post_hint)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    FStar_Pervasives_Native.Some
                                                                    post) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    post)))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    (b, post,
                                                                    opens),
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Checker_Base.intro_post_hint
                                                                    g
                                                                    (Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
                                                                    {
                                                                    Pulse_Syntax_Base.opens2
                                                                    = opens
                                                                    })
                                                                    (FStar_Pervasives_Native.Some
                                                                    (b.Pulse_Syntax_Base.binder_ty))
                                                                    post))
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    (uu___5,
                                                                    post,
                                                                    uu___6),
                                                                    FStar_Pervasives_Native.Some
                                                                    q) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    post))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "First postcondition:")
                                                                    uu___7))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_post_hint_t
                                                                    q))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (4))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Second postcondition:")
                                                                    uu___8))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    [uu___8]))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___7 ::
                                                                    uu___8))))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    (FStar_Pprint.doc_of_string
                                                                    "Fatal: multiple annotated postconditions on with_invariant")
                                                                    :: uu___7))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    uu___7))
                                                                    uu___7)))
                                                                    | 
                                                                    (uu___5,
                                                                    uu___6)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (t.Pulse_Syntax_Base.range1))
                                                                    "Fatal: no post hint on with_invariant")))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    post_hint1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    body.Pulse_Syntax_Base.range1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    body_range
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Pure.tm_star
                                                                    p
                                                                    pre_frame))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    pre_body
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    pre_body_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g x
                                                                    Pulse_Syntax_Base.ppname_default
                                                                    post_hint1.Pulse_Typing.ret_ty))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun g'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (recheck
                                                                    g
                                                                    post_hint1.Pulse_Typing.ret_ty
                                                                    (Pulse_Syntax_Pure.tm_type
                                                                    post_hint1.Pulse_Typing.u)
                                                                    ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    post_hint_ret_ty_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (recheck
                                                                    g'
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    post_hint1.Pulse_Typing.post
                                                                    (Pulse_Syntax_Base.ppname_default,
                                                                    x))
                                                                    Pulse_Syntax_Pure.tm_vprop
                                                                    ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    post_hint_post_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (find_inv_post
                                                                    g x
                                                                    post_hint1.Pulse_Typing.u
                                                                    post_hint1.Pulse_Typing.ret_ty
                                                                    post_hint1.Pulse_Typing.post
                                                                    () () i1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun res1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    res1
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    i1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    "Cannot find invariant resource for iref ")
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    post_hint1.Pulse_Typing.post))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (Pulse_PP.text
                                                                    " in the postcondition ")
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___5
                                                                    uu___6))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    [uu___5]))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    i_range)
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
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    res1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple5
                                                                    (p',
                                                                    post_frame,
                                                                    uu___7,
                                                                    post_frame_typing,
                                                                    d_post_frame_equiv))
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.eq_tm
                                                                    p p')
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    p'))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    p))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (Pulse_Show.show
                                                                    Pulse_Show.tac_showable_r_term
                                                                    i1))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "Inconsistent vprops for iref "
                                                                    (Prims.strcat
                                                                    uu___10
                                                                    " in pre ("))
                                                                    (Prims.strcat
                                                                    x1
                                                                    ") and post ("))
                                                                    (Prims.strcat
                                                                    x2 ")")))))
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
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    uu___9
                                                                    uu___8))))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    i_range)
                                                                    uu___8))
                                                                    uu___8)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Pulse_Syntax_Pure.tm_star
                                                                    p
                                                                    post_frame))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    post_body
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    match 
                                                                    post_hint1.Pulse_Typing.effect_annot
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotSTT
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (all_inames,
                                                                    ())
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotGhost
                                                                    {
                                                                    Pulse_Syntax_Base.opens
                                                                    = opens;_}
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (opens,
                                                                    ())
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    {
                                                                    Pulse_Syntax_Base.opens1
                                                                    = opens;_}
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (opens,
                                                                    ())
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
                                                                    {
                                                                    Pulse_Syntax_Base.opens2
                                                                    = opens;_}
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    (opens,
                                                                    ())))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (opens,
                                                                    opens_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> uu___9))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    remove_iname
                                                                    opens i1))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    opens_remove_i
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match 
                                                                    post_hint1.Pulse_Typing.effect_annot
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotSTT
                                                                    ->
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    {
                                                                    Pulse_Syntax_Base.opens1
                                                                    =
                                                                    opens_remove_i
                                                                    }
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    {
                                                                    Pulse_Syntax_Base.opens1
                                                                    =
                                                                    opens_remove_i
                                                                    }
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotGhost
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Syntax_Base.EffectAnnotGhost
                                                                    {
                                                                    Pulse_Syntax_Base.opens
                                                                    =
                                                                    opens_remove_i
                                                                    }
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
                                                                    {
                                                                    Pulse_Syntax_Base.opens2
                                                                    =
                                                                    opens_remove_i
                                                                    }))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    effect_annot
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    ())
                                                                    uu___11))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    effect_annot_typing
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    {
                                                                    Pulse_Typing.g
                                                                    = g;
                                                                    Pulse_Typing.effect_annot
                                                                    =
                                                                    effect_annot;
                                                                    Pulse_Typing.effect_annot_typing
                                                                    =
                                                                    effect_annot_typing;
                                                                    Pulse_Typing.ret_ty
                                                                    =
                                                                    (post_hint1.Pulse_Typing.ret_ty);
                                                                    Pulse_Typing.u
                                                                    =
                                                                    (post_hint1.Pulse_Typing.u);
                                                                    Pulse_Typing.ty_typing
                                                                    = ();
                                                                    Pulse_Typing.post
                                                                    =
                                                                    post_body;
                                                                    Pulse_Typing.x
                                                                    = x;
                                                                    Pulse_Typing.post_typing_src
                                                                    = ();
                                                                    Pulse_Typing.post_typing
                                                                    = ()
                                                                    }))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    post_hint_body
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Pulse_Syntax_Base.mk_ppname_no_range
                                                                    "with_inv_body"))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    ppname ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (check1 g
                                                                    pre_body
                                                                    ()
                                                                    (FStar_Pervasives_Native.Some
                                                                    post_hint_body)
                                                                    ppname
                                                                    body))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.apply_checker_result_k
                                                                    g
                                                                    pre_body
                                                                    post_hint_body
                                                                    r ppname))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (body1,
                                                                    c_body,
                                                                    body_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    atomic_or_ghost_with_inames_and_pre_post
                                                                    c_body
                                                                    (Pulse_Syntax_Pure.tm_add_inv
                                                                    (Pulse_Syntax_Base.comp_inames
                                                                    c_body)
                                                                    i1) pre
                                                                    post_hint1.Pulse_Typing.post))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    c_out ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (disjointness_remove_i_i
                                                                    g opens
                                                                    i1))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun tok
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (90)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    c_out))
                                                                    (Pulse_Syntax_Base.Tm_WithInv
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = i1;
                                                                    Pulse_Syntax_Base.body6
                                                                    = body1;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun tm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Typing.T_Equiv
                                                                    (g,
                                                                    (Pulse_Typing.wtag
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    (atomic_or_ghost_with_inames_and_pre_post
                                                                    c_body
                                                                    (Pulse_Syntax_Base.comp_inames
                                                                    c_body)
                                                                    pre_frame
                                                                    post_frame)))
                                                                    (Pulse_Syntax_Base.Tm_WithInv
                                                                    {
                                                                    Pulse_Syntax_Base.name1
                                                                    = i1;
                                                                    Pulse_Syntax_Base.body6
                                                                    = body1;
                                                                    Pulse_Syntax_Base.returns_inv
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })),
                                                                    (atomic_or_ghost_with_inames_and_pre_post
                                                                    c_body
                                                                    (Pulse_Syntax_Pure.tm_add_inv
                                                                    (Pulse_Syntax_Base.comp_inames
                                                                    c_body)
                                                                    i1)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i1 p)
                                                                    pre_frame)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i1 p)
                                                                    post_frame)),
                                                                    c_out,
                                                                    (Pulse_Typing.T_WithInv
                                                                    (g, i1,
                                                                    p, body1,
                                                                    (atomic_or_ghost_with_inames_and_pre_post
                                                                    c_body
                                                                    (Pulse_Syntax_Base.comp_inames
                                                                    c_body)
                                                                    pre_frame
                                                                    post_frame),
                                                                    (), (),
                                                                    body_typing,
                                                                    ())),
                                                                    (Pulse_Typing.ST_VPropEquiv
                                                                    (g,
                                                                    (atomic_or_ghost_with_inames_and_pre_post
                                                                    c_body
                                                                    (Pulse_Syntax_Pure.tm_add_inv
                                                                    (Pulse_Syntax_Base.comp_inames
                                                                    c_body)
                                                                    i1)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i1 p)
                                                                    pre_frame)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i1 p)
                                                                    post_frame)),
                                                                    c_out, x,
                                                                    (), (),
                                                                    (),
                                                                    (FStar_Reflection_Typing.Rel_refl
                                                                    ((Pulse_Typing.elab_env
                                                                    g),
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    (atomic_or_ghost_with_inames_and_pre_post
                                                                    c_body
                                                                    (Pulse_Syntax_Pure.tm_add_inv
                                                                    (Pulse_Syntax_Base.comp_inames
                                                                    c_body)
                                                                    i1)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i1 p)
                                                                    pre_frame)
                                                                    (Pulse_Syntax_Pure.tm_star
                                                                    (Pulse_Syntax_Pure.tm_inv
                                                                    i1 p)
                                                                    post_frame))),
                                                                    FStar_Reflection_Typing.R_Eq)),
                                                                    (), ())))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun d ->
                                                                    match 
                                                                    post_hint1.Pulse_Typing.effect_annot
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotGhost
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (add_remove_inverse
                                                                    g opens
                                                                    i1 () ()))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun tok1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match c_out
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (add_inv,
                                                                    obs, st)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_STAtomic
                                                                    (opens,
                                                                    obs, st)),
                                                                    (Pulse_Typing.STS_AtomicInvs
                                                                    (g, st,
                                                                    add_inv,
                                                                    opens,
                                                                    obs, obs,
                                                                    ())))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (add_inv,
                                                                    st) ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_STGhost
                                                                    (opens,
                                                                    st)),
                                                                    (Pulse_Typing.STS_GhostInvs
                                                                    (g, st,
                                                                    add_inv,
                                                                    opens,
                                                                    ())))))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_out_opens,
                                                                    d_sub_c)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    uu___13))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g, tm,
                                                                    c_out,
                                                                    c_out_opens,
                                                                    d,
                                                                    d_sub_c)))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (tm,
                                                                    c_out_opens,
                                                                    d1))
                                                                    res_ppname))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___13))
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomic
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (add_remove_inverse
                                                                    g opens
                                                                    i1 () ()))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun tok1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match c_out
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (add_inv,
                                                                    obs, st)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_STAtomic
                                                                    (opens,
                                                                    obs, st)),
                                                                    (Pulse_Typing.STS_AtomicInvs
                                                                    (g, st,
                                                                    add_inv,
                                                                    opens,
                                                                    obs, obs,
                                                                    ())))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (add_inv,
                                                                    st) ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_STGhost
                                                                    (opens,
                                                                    st)),
                                                                    (Pulse_Typing.STS_GhostInvs
                                                                    (g, st,
                                                                    add_inv,
                                                                    opens,
                                                                    ())))))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_out_opens,
                                                                    d_sub_c)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    uu___13))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g, tm,
                                                                    c_out,
                                                                    c_out_opens,
                                                                    d,
                                                                    d_sub_c)))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (tm,
                                                                    c_out_opens,
                                                                    d1))
                                                                    res_ppname))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___13))
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    (add_remove_inverse
                                                                    g opens
                                                                    i1 () ()))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun tok1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match c_out
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (add_inv,
                                                                    obs, st)
                                                                    ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_STAtomic
                                                                    (opens,
                                                                    obs, st)),
                                                                    (Pulse_Typing.STS_AtomicInvs
                                                                    (g, st,
                                                                    add_inv,
                                                                    opens,
                                                                    obs, obs,
                                                                    ())))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (add_inv,
                                                                    st) ->
                                                                    Prims.Mkdtuple2
                                                                    ((Pulse_Syntax_Base.C_STGhost
                                                                    (opens,
                                                                    st)),
                                                                    (Pulse_Typing.STS_GhostInvs
                                                                    (g, st,
                                                                    add_inv,
                                                                    opens,
                                                                    ())))))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c_out_opens,
                                                                    d_sub_c)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    uu___13))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Pulse_Typing.T_Sub
                                                                    (g, tm,
                                                                    c_out,
                                                                    c_out_opens,
                                                                    d,
                                                                    d_sub_c)))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (tm,
                                                                    c_out_opens,
                                                                    d1))
                                                                    res_ppname))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___13))
                                                                    | 
                                                                    Pulse_Syntax_Base.EffectAnnotSTT
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.WithInv.fst"
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Pulse_Typing.T_Lift
                                                                    (g, tm,
                                                                    c_out,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_out)),
                                                                    d,
                                                                    (Pulse_Typing.Lift_STAtomic_ST
                                                                    (g,
                                                                    c_out)))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun d1
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Checker_Base.checker_result_for_st_typing
                                                                    g pre
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (tm,
                                                                    (Pulse_Syntax_Base.C_ST
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c_out)),
                                                                    d1))
                                                                    res_ppname))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                uu___3)))
                                                     uu___3))) uu___1)))
                       uu___)