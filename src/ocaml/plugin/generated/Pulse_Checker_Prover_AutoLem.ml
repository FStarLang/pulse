open Prims
let (debug :
  Pulse_Typing_Env.env ->
    (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun g -> fun f -> f ()
type 't tacmonad =
  {
  return: unit -> Obj.t -> ('t, unit) FStar_Tactics_Effect.tac_repr ;
  op_let_Bang:
    unit ->
      unit ->
        't ->
          (Obj.t -> ('t, unit) FStar_Tactics_Effect.tac_repr) ->
            ('t, unit) FStar_Tactics_Effect.tac_repr
    }
let __proj__Mktacmonad__item__return :
  't .
    't tacmonad -> unit -> Obj.t -> ('t, unit) FStar_Tactics_Effect.tac_repr
  =
  fun projectee -> match projectee with | { return; op_let_Bang;_} -> return
let __proj__Mktacmonad__item__op_let_Bang :
  't .
    't tacmonad ->
      unit ->
        unit ->
          't ->
            (Obj.t -> ('t, unit) FStar_Tactics_Effect.tac_repr) ->
              ('t, unit) FStar_Tactics_Effect.tac_repr
  =
  fun projectee ->
    match projectee with | { return; op_let_Bang;_} -> op_let_Bang
let return :
  't .
    't tacmonad -> unit -> Obj.t -> ('t, unit) FStar_Tactics_Effect.tac_repr
  =
  fun projectee ->
    match projectee with | { return = return1; op_let_Bang;_} -> return1
let op_let_Bang :
  't .
    't tacmonad ->
      unit ->
        unit ->
          't ->
            (Obj.t -> ('t, unit) FStar_Tactics_Effect.tac_repr) ->
              ('t, unit) FStar_Tactics_Effect.tac_repr
  =
  fun projectee ->
    match projectee with
    | { return = return1; op_let_Bang = op_let_Bang1;_} -> op_let_Bang1
let (uu___26 : unit FStar_Pervasives_Native.option tacmonad) =
  {
    return =
      (fun uu___1 ->
         fun uu___ ->
           (fun a ->
              fun x ->
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ -> FStar_Pervasives_Native.Some x))) uu___1
             uu___);
    op_let_Bang =
      (fun uu___3 ->
         fun uu___2 ->
           fun uu___1 ->
             fun uu___ ->
               (fun a ->
                  fun b ->
                    fun x ->
                      let x = Obj.magic x in
                      fun f ->
                        let f = Obj.magic f in
                        match x with
                        | FStar_Pervasives_Native.None ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ ->
                                       FStar_Pervasives_Native.None)))
                        | FStar_Pervasives_Native.Some x1 ->
                            Obj.magic (Obj.repr (f x1))) uu___3 uu___2 uu___1
                 uu___)
  }
type 't tac_alternative =
  {
  empty: 't ;
  op_Less_Bar_Greater:
    't ->
      (unit -> ('t, unit) FStar_Tactics_Effect.tac_repr) ->
        ('t, unit) FStar_Tactics_Effect.tac_repr
    }
let __proj__Mktac_alternative__item__empty : 't . 't tac_alternative -> 't =
  fun projectee ->
    match projectee with | { empty; op_Less_Bar_Greater;_} -> empty
let __proj__Mktac_alternative__item__op_Less_Bar_Greater :
  't .
    't tac_alternative ->
      't ->
        (unit -> ('t, unit) FStar_Tactics_Effect.tac_repr) ->
          ('t, unit) FStar_Tactics_Effect.tac_repr
  =
  fun projectee ->
    match projectee with
    | { empty; op_Less_Bar_Greater;_} -> op_Less_Bar_Greater
let empty : 't . 't tac_alternative -> 't =
  fun projectee ->
    match projectee with | { empty = empty1; op_Less_Bar_Greater;_} -> empty1
let op_Less_Bar_Greater :
  't .
    't tac_alternative ->
      't ->
        (unit -> ('t, unit) FStar_Tactics_Effect.tac_repr) ->
          ('t, unit) FStar_Tactics_Effect.tac_repr
  =
  fun projectee ->
    match projectee with
    | { empty = empty1; op_Less_Bar_Greater = op_Less_Bar_Greater1;_} ->
        op_Less_Bar_Greater1
let alternative_option :
  'a . unit -> 'a FStar_Pervasives_Native.option tac_alternative =
  fun uu___ ->
    {
      empty = FStar_Pervasives_Native.None;
      op_Less_Bar_Greater =
        (fun uu___2 ->
           fun uu___1 ->
             (fun x ->
                fun y ->
                  match x with
                  | FStar_Pervasives_Native.None ->
                      Obj.magic (Obj.repr (y ()))
                  | FStar_Pervasives_Native.Some uu___1 ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 -> x)))) uu___2 uu___1)
    }
let (hua :
  FStar_Reflection_Types.term ->
    ((FStar_Reflection_Types.fv * Pulse_Syntax_Base.universe Prims.list *
       FStar_Reflection_V2_Data.argv Prims.list)
       FStar_Pervasives_Native.option,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
               (Prims.of_int (64)) (Prims.of_int (17)) (Prims.of_int (64))
               (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
               (Prims.of_int (63)) (Prims.of_int (70)) (Prims.of_int (68))
               (Prims.of_int (13)))))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Reflection_V2_Derived.collect_app_ln t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | (hd, args) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.AutoLem.fst"
                              (Prims.of_int (65)) (Prims.of_int (8))
                              (Prims.of_int (65)) (Prims.of_int (18)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.AutoLem.fst"
                              (Prims.of_int (65)) (Prims.of_int (2))
                              (Prims.of_int (68)) (Prims.of_int (13)))))
                     (Obj.magic (FStar_Tactics_NamedView.inspect hd))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             match uu___1 with
                             | FStar_Tactics_NamedView.Tv_FVar fv ->
                                 FStar_Pervasives_Native.Some (fv, [], args)
                             | FStar_Tactics_NamedView.Tv_UInst (fv, us) ->
                                 FStar_Pervasives_Native.Some (fv, us, args)
                             | uu___3 -> FStar_Pervasives_Native.None))))
           uu___)
let (eager_autolem1 :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit Pulse_Checker_Prover_Base.prover_state
         FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun preamble ->
         fun pst ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ -> FStar_Pervasives_Native.None))) uu___1 uu___
let rec (eager_autolem : Pulse_Checker_Prover_Base.eager_prover_step) =
  fun preamble ->
    fun pst ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                 (Prims.of_int (121)) (Prims.of_int (8)) (Prims.of_int (121))
                 (Prims.of_int (26)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                 (Prims.of_int (121)) (Prims.of_int (2)) (Prims.of_int (123))
                 (Prims.of_int (15)))))
        (Obj.magic (eager_autolem1 preamble pst))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives_Native.Some pst' ->
                  Obj.magic (Obj.repr (eager_autolem preamble pst'))
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> pst))))
             uu___)
let (guided_autolem_attr : FStar_Reflection_Types.term) =
  FStar_Reflection_V2_Builtins.pack_ln
    (FStar_Reflection_V2_Data.Tv_FVar
       (FStar_Reflection_V2_Builtins.pack_fv
          ["Pulse"; "Lib"; "Core"; "guided_autolem"]))
let (pp_fv : FStar_Reflection_Types.fv Pulse_PP.printable) =
  {
    Pulse_PP.pp =
      (fun fv ->
         Pulse_PP.pp Pulse_PP.printable_term
           (FStar_Tactics_NamedView.pack (FStar_Tactics_NamedView.Tv_FVar fv)))
  }
let (pp_aqualv : FStar_Reflection_V2_Data.aqualv Pulse_PP.printable) =
  {
    Pulse_PP.pp =
      (fun uu___ ->
         (fun x ->
            match x with
            | FStar_Reflection_V2_Data.Q_Explicit ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> Pulse_PP.text "Q_Explicit")))
            | FStar_Reflection_V2_Data.Q_Implicit ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> Pulse_PP.text "Q_Implicit")))
            | FStar_Reflection_V2_Data.Q_Meta t ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.AutoLem.fst"
                                 (Prims.of_int (131)) (Prims.of_int (130))
                                 (Prims.of_int (131)) (Prims.of_int (134)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.AutoLem.fst"
                                 (Prims.of_int (131)) (Prims.of_int (112))
                                 (Prims.of_int (131)) (Prims.of_int (134)))))
                        (Obj.magic (Pulse_PP.pp Pulse_PP.printable_term t))
                        (fun uu___ ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 ->
                                FStar_Pprint.op_Hat_Slash_Hat
                                  (Pulse_PP.text "Q_Meta") uu___))))) uu___)
  }
let (pp_binder : FStar_Tactics_NamedView.binder Pulse_PP.printable) =
  {
    Pulse_PP.pp =
      (fun b ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                    (Prims.of_int (135)) (Prims.of_int (47))
                    (Prims.of_int (135)) (Prims.of_int (80)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                    (Prims.of_int (135)) (Prims.of_int (44))
                    (Prims.of_int (135)) (Prims.of_int (80)))))
           (Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "Pulse.Checker.Prover.AutoLem.fst"
                          (Prims.of_int (135)) (Prims.of_int (48))
                          (Prims.of_int (135)) (Prims.of_int (63)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "Pulse.Checker.Prover.AutoLem.fst"
                          (Prims.of_int (135)) (Prims.of_int (47))
                          (Prims.of_int (135)) (Prims.of_int (80)))))
                 (Obj.magic
                    (FStar_Tactics_Unseal.unseal
                       b.FStar_Tactics_NamedView.ppname))
                 (fun uu___ ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 ->
                         (uu___, (b.FStar_Tactics_NamedView.sort),
                           (b.FStar_Tactics_NamedView.qual))))))
           (fun uu___ ->
              (fun uu___ ->
                 Obj.magic
                   (Pulse_PP.pp
                      (Pulse_PP.printable_tuple3 Pulse_PP.printable_string
                         Pulse_PP.printable_term pp_aqualv) uu___)) uu___))
  }
let (pp_tot_or_ghost :
  FStar_TypeChecker_Core.tot_or_ghost Pulse_PP.printable) =
  {
    Pulse_PP.pp =
      (fun uu___ ->
         (fun x ->
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    match x with
                    | FStar_TypeChecker_Core.E_Total ->
                        Pulse_PP.text "E_Total"
                    | FStar_TypeChecker_Core.E_Ghost ->
                        Pulse_PP.text "E_Ghost"))) uu___)
  }
exception Retry 
let (uu___is_Retry : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Retry -> true | uu___ -> false
let rec apply_first :
  'a 'b .
    ('a ->
       ('b FStar_Pervasives_Native.option, unit)
         FStar_Tactics_Effect.tac_repr)
      ->
      'a Prims.list ->
        ('b FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun cands ->
           match cands with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives_Native.None)))
           | x::xs ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.AutoLem.fst"
                                (Prims.of_int (148)) (Prims.of_int (10))
                                (Prims.of_int (148)) (Prims.of_int (53)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Pulse.Checker.Prover.AutoLem.fst"
                                (Prims.of_int (148)) (Prims.of_int (4))
                                (Prims.of_int (150)) (Prims.of_int (30)))))
                       (Obj.magic
                          (FStar_Tactics_V2_Derived.try_with
                             (fun uu___ -> match () with | () -> f x)
                             (fun uu___ ->
                                (fun uu___ ->
                                   match uu___ with
                                   | Retry ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___1 ->
                                               FStar_Pervasives_Native.None))
                                   | e ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.raise e))
                                  uu___)))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | FStar_Pervasives_Native.Some y ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            FStar_Pervasives_Native.Some y)))
                             | FStar_Pervasives_Native.None ->
                                 Obj.magic (Obj.repr (apply_first f xs)))
                            uu___)))) uu___1 uu___
let (n_args :
  FStar_Reflection_Types.term ->
    (Prims.nat, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun typ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
               (Prims.of_int (153)) (Prims.of_int (14)) (Prims.of_int (153))
               (Prims.of_int (29)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
               (Prims.of_int (152)) (Prims.of_int (35)) (Prims.of_int (154))
               (Prims.of_int (16)))))
      (Obj.magic (FStar_Tactics_V2_SyntaxHelpers.collect_arr typ))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with | (bs, c) -> FStar_List_Tot_Base.length bs))
let (pp_comp_view : FStar_Reflection_V2_Data.comp_view Pulse_PP.printable) =
  {
    Pulse_PP.pp =
      (fun x ->
         match x with
         | FStar_Reflection_V2_Data.C_Total ret ->
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                        (Prims.of_int (159)) (Prims.of_int (41))
                        (Prims.of_int (159)) (Prims.of_int (47)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                        (Prims.of_int (159)) (Prims.of_int (22))
                        (Prims.of_int (159)) (Prims.of_int (47)))))
               (Obj.magic (Pulse_PP.pp Pulse_PP.printable_term ret))
               (fun uu___ ->
                  FStar_Tactics_Effect.lift_div_tac
                    (fun uu___1 ->
                       FStar_Pprint.op_Hat_Slash_Hat
                         (Pulse_PP.text "C_Total") uu___))
         | FStar_Reflection_V2_Data.C_GTotal ret ->
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                        (Prims.of_int (160)) (Prims.of_int (43))
                        (Prims.of_int (160)) (Prims.of_int (49)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                        (Prims.of_int (160)) (Prims.of_int (23))
                        (Prims.of_int (160)) (Prims.of_int (49)))))
               (Obj.magic (Pulse_PP.pp Pulse_PP.printable_term ret))
               (fun uu___ ->
                  FStar_Tactics_Effect.lift_div_tac
                    (fun uu___1 ->
                       FStar_Pprint.op_Hat_Slash_Hat
                         (Pulse_PP.text "C_GTotal") uu___))
         | FStar_Reflection_V2_Data.C_Lemma (pre, post, pats) ->
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                        (Prims.of_int (161)) (Prims.of_int (51))
                        (Prims.of_int (161)) (Prims.of_int (81)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                        (Prims.of_int (161)) (Prims.of_int (32))
                        (Prims.of_int (161)) (Prims.of_int (81)))))
               (Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.AutoLem.fst"
                              (Prims.of_int (161)) (Prims.of_int (51))
                              (Prims.of_int (161)) (Prims.of_int (57)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.AutoLem.fst"
                              (Prims.of_int (161)) (Prims.of_int (51))
                              (Prims.of_int (161)) (Prims.of_int (81)))))
                     (Obj.magic (Pulse_PP.pp Pulse_PP.printable_term pre))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Prover.AutoLem.fst"
                                         (Prims.of_int (161))
                                         (Prims.of_int (62))
                                         (Prims.of_int (161))
                                         (Prims.of_int (81)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Prover.AutoLem.fst"
                                         (Prims.of_int (161))
                                         (Prims.of_int (51))
                                         (Prims.of_int (161))
                                         (Prims.of_int (81)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.AutoLem.fst"
                                               (Prims.of_int (161))
                                               (Prims.of_int (62))
                                               (Prims.of_int (161))
                                               (Prims.of_int (69)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.AutoLem.fst"
                                               (Prims.of_int (161))
                                               (Prims.of_int (62))
                                               (Prims.of_int (161))
                                               (Prims.of_int (81)))))
                                      (Obj.magic
                                         (Pulse_PP.pp Pulse_PP.printable_term
                                            post))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.AutoLem.fst"
                                                          (Prims.of_int (161))
                                                          (Prims.of_int (74))
                                                          (Prims.of_int (161))
                                                          (Prims.of_int (81)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.AutoLem.fst"
                                                          (Prims.of_int (161))
                                                          (Prims.of_int (62))
                                                          (Prims.of_int (161))
                                                          (Prims.of_int (81)))))
                                                 (Obj.magic
                                                    (Pulse_PP.pp
                                                       Pulse_PP.printable_term
                                                       pats))
                                                 (fun uu___2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         FStar_Pprint.op_Hat_Slash_Hat
                                                           uu___1 uu___2))))
                                           uu___1)))
                                (fun uu___1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 ->
                                        FStar_Pprint.op_Hat_Slash_Hat uu___
                                          uu___1)))) uu___)))
               (fun uu___ ->
                  FStar_Tactics_Effect.lift_div_tac
                    (fun uu___1 ->
                       FStar_Pprint.op_Hat_Slash_Hat
                         (Pulse_PP.text "C_Lemma") uu___))
         | FStar_Reflection_V2_Data.C_Eff
             (us, eff_name, result, eff_args, decrs) ->
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                        (Prims.of_int (162)) (Prims.of_int (67))
                        (Prims.of_int (162)) (Prims.of_int (131)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                        (Prims.of_int (162)) (Prims.of_int (50))
                        (Prims.of_int (162)) (Prims.of_int (131)))))
               (Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.AutoLem.fst"
                              (Prims.of_int (162)) (Prims.of_int (67))
                              (Prims.of_int (162)) (Prims.of_int (72)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.AutoLem.fst"
                              (Prims.of_int (162)) (Prims.of_int (67))
                              (Prims.of_int (162)) (Prims.of_int (131)))))
                     (Obj.magic
                        (Pulse_PP.pp
                           (Pulse_PP.printable_list
                              Pulse_PP.printable_universe) us))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Prover.AutoLem.fst"
                                         (Prims.of_int (162))
                                         (Prims.of_int (77))
                                         (Prims.of_int (162))
                                         (Prims.of_int (131)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Prover.AutoLem.fst"
                                         (Prims.of_int (162))
                                         (Prims.of_int (67))
                                         (Prims.of_int (162))
                                         (Prims.of_int (131)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.AutoLem.fst"
                                               (Prims.of_int (162))
                                               (Prims.of_int (77))
                                               (Prims.of_int (162))
                                               (Prims.of_int (88)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.AutoLem.fst"
                                               (Prims.of_int (162))
                                               (Prims.of_int (77))
                                               (Prims.of_int (162))
                                               (Prims.of_int (131)))))
                                      (Obj.magic
                                         (Pulse_PP.pp
                                            (Pulse_PP.printable_list
                                               Pulse_PP.printable_string)
                                            eff_name))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.AutoLem.fst"
                                                          (Prims.of_int (162))
                                                          (Prims.of_int (93))
                                                          (Prims.of_int (162))
                                                          (Prims.of_int (131)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.AutoLem.fst"
                                                          (Prims.of_int (162))
                                                          (Prims.of_int (77))
                                                          (Prims.of_int (162))
                                                          (Prims.of_int (131)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.AutoLem.fst"
                                                                (Prims.of_int (162))
                                                                (Prims.of_int (93))
                                                                (Prims.of_int (162))
                                                                (Prims.of_int (102)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.AutoLem.fst"
                                                                (Prims.of_int (162))
                                                                (Prims.of_int (93))
                                                                (Prims.of_int (162))
                                                                (Prims.of_int (131)))))
                                                       (Obj.magic
                                                          (Pulse_PP.pp
                                                             Pulse_PP.printable_term
                                                             result))
                                                       (fun uu___2 ->
                                                          (fun uu___2 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (131)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (131)))))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (118)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (131)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    (Pulse_PP.printable_tuple2
                                                                    Pulse_PP.printable_term
                                                                    pp_aqualv))
                                                                    eff_args))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (131)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (131)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    decrs))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___3
                                                                    uu___4))))
                                                                    uu___3)))
                                                                  (fun uu___3
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___2
                                                                    uu___3))))
                                                            uu___2)))
                                                 (fun uu___2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         FStar_Pprint.op_Hat_Slash_Hat
                                                           uu___1 uu___2))))
                                           uu___1)))
                                (fun uu___1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 ->
                                        FStar_Pprint.op_Hat_Slash_Hat uu___
                                          uu___1)))) uu___)))
               (fun uu___ ->
                  FStar_Tactics_Effect.lift_div_tac
                    (fun uu___1 ->
                       FStar_Pprint.op_Hat_Slash_Hat (Pulse_PP.text "C_Eff")
                         uu___)))
  }
let (binder_to_r_namedv :
  FStar_Tactics_NamedView.binder -> FStar_Reflection_Types.namedv) =
  fun b ->
    FStar_Reflection_V2_Builtins.pack_namedv
      {
        FStar_Reflection_V2_Data.uniq = (b.FStar_Tactics_NamedView.uniq);
        FStar_Reflection_V2_Data.sort =
          (FStar_Sealed.seal b.FStar_Tactics_NamedView.sort);
        FStar_Reflection_V2_Data.ppname = (b.FStar_Tactics_NamedView.ppname)
      }
let (apply_wild :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      FStar_Tactics_NamedView.binders ->
        ((FStar_Reflection_Types.term * FStar_Syntax_Syntax.subst_t *
           FStar_Reflection_Types.term Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      fun bs ->
        let rec go uu___3 uu___2 uu___1 uu___ =
          (fun t1 ->
             fun bs1 ->
               fun subst ->
                 fun uvs ->
                   match bs1 with
                   | [] ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> (t1, subst, uvs))))
                   | b::bs2 ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Prover.AutoLem.fst"
                                        (Prims.of_int (179))
                                        (Prims.of_int (15))
                                        (Prims.of_int (179))
                                        (Prims.of_int (60)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Prover.AutoLem.fst"
                                        (Prims.of_int (179))
                                        (Prims.of_int (63))
                                        (Prims.of_int (181))
                                        (Prims.of_int (52)))))
                               (Obj.magic
                                  (FStar_Tactics_V2_Builtins.uvar_env e
                                     (FStar_Pervasives_Native.Some
                                        (FStar_Reflection_V2_Builtins.subst_term
                                           subst
                                           b.FStar_Tactics_NamedView.sort))))
                               (fun uu___ ->
                                  (fun ut ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.AutoLem.fst"
                                                   (Prims.of_int (180))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (180))
                                                   (Prims.of_int (58)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.AutoLem.fst"
                                                   (Prims.of_int (181))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (181))
                                                   (Prims.of_int (52)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___ ->
                                                (FStar_Syntax_Syntax.NT
                                                   ((binder_to_r_namedv b),
                                                     ut))
                                                :: subst))
                                          (fun uu___ ->
                                             (fun subst' ->
                                                Obj.magic
                                                  (go
                                                     (FStar_Tactics_NamedView.pack
                                                        (FStar_Tactics_NamedView.Tv_App
                                                           (t1,
                                                             (ut,
                                                               (b.FStar_Tactics_NamedView.qual)))))
                                                     bs2 subst' (ut :: uvs)))
                                               uu___))) uu___)))) uu___3
            uu___2 uu___1 uu___ in
        go t bs [] []
let (push_binding :
  FStar_Reflection_Types.env ->
    FStar_Reflection_V2_Data.binding ->
      (FStar_Reflection_Types.env, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun e ->
         fun b ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ -> FStar_Reflection_V2_Derived.push_binding e b)))
        uu___1 uu___
let (uu___142 : FStar_Reflection_Types.comp Pulse_Show.tac_showable) =
  { Pulse_Show.show = (fun c -> FStar_Tactics_V1_Builtins.comp_to_string c) }
let (uu___144 : FStar_Tactics_NamedView.comp Pulse_Show.tac_showable) =
  {
    Pulse_Show.show =
      (fun c ->
         Pulse_Show.show uu___142 (FStar_Reflection_V2_Builtins.pack_comp c))
  }
let (uu___146 : FStar_Reflection_V2_Data.binding Pulse_PP.printable) =
  {
    Pulse_PP.pp =
      (fun b ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                    (Prims.of_int (200)) (Prims.of_int (29))
                    (Prims.of_int (200)) (Prims.of_int (49)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                    (Prims.of_int (200)) (Prims.of_int (29))
                    (Prims.of_int (200)) (Prims.of_int (93)))))
           (Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "Pulse.Checker.Prover.AutoLem.fst"
                          (Prims.of_int (200)) (Prims.of_int (32))
                          (Prims.of_int (200)) (Prims.of_int (49)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "Pulse.Checker.Prover.AutoLem.fst"
                          (Prims.of_int (200)) (Prims.of_int (29))
                          (Prims.of_int (200)) (Prims.of_int (49)))))
                 (Obj.magic
                    (FStar_Tactics_Unseal.unseal
                       b.FStar_Reflection_V2_Data.ppname3))
                 (fun uu___ ->
                    (fun uu___ ->
                       Obj.magic
                         (Pulse_PP.pp Pulse_PP.printable_string uu___)) uu___)))
           (fun uu___ ->
              (fun uu___ ->
                 Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Pulse.Checker.Prover.AutoLem.fst"
                               (Prims.of_int (200)) (Prims.of_int (53))
                               (Prims.of_int (200)) (Prims.of_int (93)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Pulse.Checker.Prover.AutoLem.fst"
                               (Prims.of_int (200)) (Prims.of_int (29))
                               (Prims.of_int (200)) (Prims.of_int (93)))))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Prover.AutoLem.fst"
                                     (Prims.of_int (200)) (Prims.of_int (75))
                                     (Prims.of_int (200)) (Prims.of_int (93)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Prover.AutoLem.fst"
                                     (Prims.of_int (200)) (Prims.of_int (53))
                                     (Prims.of_int (200)) (Prims.of_int (93)))))
                            (Obj.magic
                               (Pulse_PP.pp Pulse_PP.printable_int
                                  b.FStar_Reflection_V2_Data.uniq1))
                            (fun uu___1 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___2 ->
                                    FStar_Pprint.op_Hat_Hat
                                      (FStar_Pprint.doc_of_string "--")
                                      uu___1))))
                      (fun uu___1 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___2 ->
                              FStar_Pprint.op_Hat_Hat uu___ uu___1)))) uu___))
  }
let (instantiate_fun :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      FStar_Reflection_Types.env ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            ((FStar_Reflection_Types.env * FStar_Reflection_Types.term
               Prims.list * FStar_Reflection_Types.term *
               FStar_Reflection_Types.typ),
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      fun e ->
        fun t ->
          fun typ ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                       (Prims.of_int (204)) (Prims.of_int (14))
                       (Prims.of_int (204)) (Prims.of_int (32)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                       (Prims.of_int (203)) (Prims.of_int (142))
                       (Prims.of_int (216)) (Prims.of_int (57)))))
              (Obj.magic (FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs typ))
              (fun uu___ ->
                 (fun uu___ ->
                    match uu___ with
                    | (bs, c) ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.AutoLem.fst"
                                      (Prims.of_int (211))
                                      (Prims.of_int (11))
                                      (Prims.of_int (211))
                                      (Prims.of_int (90)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.AutoLem.fst"
                                      (Prims.of_int (211))
                                      (Prims.of_int (93))
                                      (Prims.of_int (216))
                                      (Prims.of_int (57)))))
                             (Obj.magic
                                (FStar_Tactics_Util.fold_left
                                   (fun e1 ->
                                      fun b ->
                                        push_binding e1
                                          (FStar_Tactics_NamedView.binder_to_binding
                                             b)) e bs))
                             (fun uu___1 ->
                                (fun e' ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.AutoLem.fst"
                                                 (Prims.of_int (212))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (212))
                                                 (Prims.of_int (37)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.AutoLem.fst"
                                                 (Prims.of_int (211))
                                                 (Prims.of_int (93))
                                                 (Prims.of_int (216))
                                                 (Prims.of_int (57)))))
                                        (Obj.magic (apply_wild e' t bs))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              match uu___1 with
                                              | (t', s, uvs) ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.AutoLem.fst"
                                                                (Prims.of_int (213))
                                                                (Prims.of_int (10))
                                                                (Prims.of_int (213))
                                                                (Prims.of_int (59)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.AutoLem.fst"
                                                                (Prims.of_int (214))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (216))
                                                                (Prims.of_int (57)))))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             FStar_Reflection_V2_Builtins.inspect_comp
                                                               (FStar_Reflection_V2_Builtins.subst_comp
                                                                  s
                                                                  (FStar_Reflection_V2_Builtins.pack_comp
                                                                    c))))
                                                       (fun c1 ->
                                                          match c1 with
                                                          | FStar_Reflection_V2_Data.C_Total
                                                              ty ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___2
                                                                   ->
                                                                   (e', uvs,
                                                                    t', ty))
                                                          | uu___2 ->
                                                              FStar_Tactics_V1_Derived.fail
                                                                "instantiate_fun: not a total comp")))
                                             uu___1))) uu___1))) uu___)
let rec (explode :
  Pulse_Syntax_Base.term ->
    (FStar_Reflection_Types.term Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       match Pulse_Syntax_Pure.inspect_term t with
       | Pulse_Syntax_Pure.Tm_Star (l, r) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.Prover.AutoLem.fst"
                            (Prims.of_int (233)) (Prims.of_int (19))
                            (Prims.of_int (233)) (Prims.of_int (28)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.Prover.AutoLem.fst"
                            (Prims.of_int (233)) (Prims.of_int (19))
                            (Prims.of_int (233)) (Prims.of_int (40)))))
                   (Obj.magic (explode l))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.AutoLem.fst"
                                       (Prims.of_int (233))
                                       (Prims.of_int (31))
                                       (Prims.of_int (233))
                                       (Prims.of_int (40)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.AutoLem.fst"
                                       (Prims.of_int (233))
                                       (Prims.of_int (19))
                                       (Prims.of_int (233))
                                       (Prims.of_int (40)))))
                              (Obj.magic (explode r))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      FStar_List_Tot_Base.op_At uu___ uu___1))))
                        uu___)))
       | Pulse_Syntax_Pure.Tm_FStar t1 ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [t1])))
       | uu___ ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> []))))
      uu___
let rec (remove1 :
  FStar_Reflection_Types.env ->
    Pulse_Syntax_Base.vprop Prims.list ->
      FStar_Reflection_Types.term ->
        (Pulse_Syntax_Base.vprop Prims.list, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun ctx ->
      fun p ->
        match ctx with
        | [] ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                       (Prims.of_int (240)) (Prims.of_int (4))
                       (Prims.of_int (240)) (Prims.of_int (54)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                       (Prims.of_int (241)) (Prims.of_int (4))
                       (Prims.of_int (241)) (Prims.of_int (15)))))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "Pulse.Checker.Prover.AutoLem.fst"
                             (Prims.of_int (240)) (Prims.of_int (18))
                             (Prims.of_int (240)) (Prims.of_int (54)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "Pulse.Checker.Prover.AutoLem.fst"
                             (Prims.of_int (240)) (Prims.of_int (4))
                             (Prims.of_int (240)) (Prims.of_int (54)))))
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Prover.AutoLem.fst"
                                   (Prims.of_int (240)) (Prims.of_int (46))
                                   (Prims.of_int (240)) (Prims.of_int (52)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "prims.fst"
                                   (Prims.of_int (590)) (Prims.of_int (19))
                                   (Prims.of_int (590)) (Prims.of_int (31)))))
                          (Obj.magic
                             (Pulse_Show.show Pulse_Show.tac_showable_r_term
                                p))
                          (fun uu___ ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 ->
                                  Prims.strcat "Could not find in ctx:" uu___))))
                    (fun uu___ ->
                       (fun uu___ ->
                          Obj.magic (FStar_Tactics_V1_Builtins.print uu___))
                         uu___)))
              (fun uu___ -> FStar_Tactics_Effect.raise Retry)
        | q::qs ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                       (Prims.of_int (242)) (Prims.of_int (16))
                       (Prims.of_int (242)) (Prims.of_int (31)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                       (Prims.of_int (242)) (Prims.of_int (13))
                       (Prims.of_int (242)) (Prims.of_int (64)))))
              (Obj.magic (FStar_Tactics_V2_Builtins.unify_env e q p))
              (fun uu___ ->
                 (fun uu___ ->
                    if uu___
                    then
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> qs)))
                    else
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.AutoLem.fst"
                                       (Prims.of_int (242))
                                       (Prims.of_int (48))
                                       (Prims.of_int (242))
                                       (Prims.of_int (64)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.AutoLem.fst"
                                       (Prims.of_int (242))
                                       (Prims.of_int (45))
                                       (Prims.of_int (242))
                                       (Prims.of_int (64)))))
                              (Obj.magic (remove1 e qs p))
                              (fun uu___2 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 -> q :: uu___2))))) uu___)
let rec (remove :
  FStar_Reflection_Types.env ->
    Pulse_Syntax_Base.vprop Prims.list ->
      FStar_Reflection_Types.term Prims.list ->
        (Pulse_Syntax_Base.vprop Prims.list, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun e ->
           fun ctx ->
             fun pre ->
               match pre with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ctx)))
               | p::ps ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.AutoLem.fst"
                                    (Prims.of_int (248)) (Prims.of_int (4))
                                    (Prims.of_int (248)) (Prims.of_int (69)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.AutoLem.fst"
                                    (Prims.of_int (249)) (Prims.of_int (4))
                                    (Prims.of_int (249)) (Prims.of_int (33)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.AutoLem.fst"
                                          (Prims.of_int (248))
                                          (Prims.of_int (10))
                                          (Prims.of_int (248))
                                          (Prims.of_int (69)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Prover.AutoLem.fst"
                                          (Prims.of_int (248))
                                          (Prims.of_int (4))
                                          (Prims.of_int (248))
                                          (Prims.of_int (69)))))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Prover.AutoLem.fst"
                                                (Prims.of_int (248))
                                                (Prims.of_int (34))
                                                (Prims.of_int (248))
                                                (Prims.of_int (68)))))
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
                                                      "Pulse.Checker.Prover.AutoLem.fst"
                                                      (Prims.of_int (248))
                                                      (Prims.of_int (34))
                                                      (Prims.of_int (248))
                                                      (Prims.of_int (40)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Prover.AutoLem.fst"
                                                      (Prims.of_int (248))
                                                      (Prims.of_int (34))
                                                      (Prims.of_int (248))
                                                      (Prims.of_int (68)))))
                                             (Obj.magic
                                                (Pulse_Show.show
                                                   Pulse_Show.tac_showable_r_term
                                                   p))
                                             (fun uu___ ->
                                                (fun uu___ ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Prover.AutoLem.fst"
                                                                 (Prims.of_int (248))
                                                                 (Prims.of_int (43))
                                                                 (Prims.of_int (248))
                                                                 (Prims.of_int (68)))))
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
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (68)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                              (Obj.magic
                                                                 (Pulse_Show.show
                                                                    (
                                                                    Pulse_Show.tac_showable_list
                                                                    Pulse_Show.tac_showable_r_term)
                                                                    ctx))
                                                              (fun uu___1 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___2 ->
                                                                    Prims.strcat
                                                                    ") from ctx: "
                                                                    uu___1))))
                                                        (fun uu___1 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___2 ->
                                                                Prims.strcat
                                                                  uu___
                                                                  uu___1))))
                                                  uu___)))
                                       (fun uu___ ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___1 ->
                                               Prims.strcat
                                                 "TRYING to remove (" uu___))))
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
                                               "Pulse.Checker.Prover.AutoLem.fst"
                                               (Prims.of_int (249))
                                               (Prims.of_int (13))
                                               (Prims.of_int (249))
                                               (Prims.of_int (30)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.AutoLem.fst"
                                               (Prims.of_int (249))
                                               (Prims.of_int (4))
                                               (Prims.of_int (249))
                                               (Prims.of_int (33)))))
                                      (Obj.magic (remove1 e ctx p))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            Obj.magic (remove e uu___1 ps))
                                           uu___1))) uu___)))) uu___2 uu___1
          uu___
let (typ_of_fv :
  FStar_Reflection_Types.fv ->
    (FStar_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun fv ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
               (Prims.of_int (252)) (Prims.of_int (8)) (Prims.of_int (252))
               (Prims.of_int (47)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
               (Prims.of_int (252)) (Prims.of_int (2)) (Prims.of_int (258))
               (Prims.of_int (43)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                     (Prims.of_int (252)) (Prims.of_int (19))
                     (Prims.of_int (252)) (Prims.of_int (31)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Checker.Prover.AutoLem.fst"
                     (Prims.of_int (252)) (Prims.of_int (8))
                     (Prims.of_int (252)) (Prims.of_int (47)))))
            (Obj.magic (FStar_Tactics_V2_Builtins.top_env ()))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    FStar_Reflection_V2_Builtins.lookup_typ uu___
                      (FStar_Reflection_V2_Builtins.inspect_fv fv)))))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Pervasives_Native.None ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_V1_Derived.fail "sigelt not found"))
            | FStar_Pervasives_Native.Some se ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.AutoLem.fst"
                                 (Prims.of_int (255)) (Prims.of_int (10))
                                 (Prims.of_int (255)) (Prims.of_int (27)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.AutoLem.fst"
                                 (Prims.of_int (255)) (Prims.of_int (4))
                                 (Prims.of_int (258)) (Prims.of_int (43)))))
                        (Obj.magic
                           (FStar_Tactics_NamedView.inspect_sigelt se))
                        (fun uu___1 ->
                           match uu___1 with
                           | FStar_Tactics_NamedView.Sg_Let
                               { FStar_Tactics_NamedView.isrec = uu___2;
                                 FStar_Tactics_NamedView.lbs = lb::[];_}
                               ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___3 ->
                                    lb.FStar_Tactics_NamedView.lb_typ)
                           | FStar_Tactics_NamedView.Sg_Val
                               { FStar_Tactics_NamedView.nm1 = uu___2;
                                 FStar_Tactics_NamedView.univs2 = uu___3;
                                 FStar_Tactics_NamedView.typ1 = typ;_}
                               ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___4 -> typ)
                           | uu___2 ->
                               FStar_Tactics_V1_Derived.fail
                                 "unexpected sigelt")))) uu___)
let (guided_autolem1 :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop Prims.list ->
          unit ->
            Pulse_Checker_Prover_Base.prover_t ->
              FStar_Reflection_Types.fv ->
                (unit Pulse_Checker_Prover_Base.prover_state
                   FStar_Pervasives_Native.option,
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      fun q ->
        fun unsolved' ->
          fun uu___ ->
            fun prover ->
              fun fv ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.AutoLem.fst"
                           (Prims.of_int (268)) (Prims.of_int (14))
                           (Prims.of_int (268)) (Prims.of_int (29)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "Pulse.Checker.Prover.AutoLem.fst"
                           (Prims.of_int (269)) (Prims.of_int (2))
                           (Prims.of_int (373)) (Prims.of_int (13)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        FStar_Reflection_V2_Builtins.range_of_term q))
                  (fun uu___1 ->
                     (fun q_rng ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.AutoLem.fst"
                                      (Prims.of_int (269)) (Prims.of_int (2))
                                      (Prims.of_int (276)) (Prims.of_int (4)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.AutoLem.fst"
                                      (Prims.of_int (276)) (Prims.of_int (5))
                                      (Prims.of_int (373))
                                      (Prims.of_int (13)))))
                             (Obj.magic
                                (debug pst.Pulse_Checker_Prover_Base.pg
                                   (fun uu___1 ->
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.AutoLem.fst"
                                                 (Prims.of_int (270))
                                                 (Prims.of_int (31))
                                                 (Prims.of_int (276))
                                                 (Prims.of_int (3)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.AutoLem.fst"
                                                 (Prims.of_int (270))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (276))
                                                 (Prims.of_int (3)))))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Prover.AutoLem.fst"
                                                       (Prims.of_int (271))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (271))
                                                       (Prims.of_int (79)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Prover.AutoLem.fst"
                                                       (Prims.of_int (270))
                                                       (Prims.of_int (31))
                                                       (Prims.of_int (276))
                                                       (Prims.of_int (3)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Prover.AutoLem.fst"
                                                             (Prims.of_int (271))
                                                             (Prims.of_int (40))
                                                             (Prims.of_int (271))
                                                             (Prims.of_int (79)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Checker.Prover.AutoLem.fst"
                                                             (Prims.of_int (271))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (271))
                                                             (Prims.of_int (79)))))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.AutoLem.fst"
                                                                   (Prims.of_int (271))
                                                                   (Prims.of_int (40))
                                                                   (Prims.of_int (271))
                                                                   (Prims.of_int (45)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Prover.AutoLem.fst"
                                                                   (Prims.of_int (271))
                                                                   (Prims.of_int (40))
                                                                   (Prims.of_int (271))
                                                                   (Prims.of_int (79)))))
                                                          (Obj.magic
                                                             (Pulse_PP.pp
                                                                pp_fv fv))
                                                          (fun uu___2 ->
                                                             (fun uu___2 ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (79)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (79)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    q))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "for resource:")
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___2
                                                                    uu___3))))
                                                               uu___2)))
                                                    (fun uu___2 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            FStar_Pprint.op_Hat_Slash_Hat
                                                              (Pulse_PP.text
                                                                 "Trying candidate autolem")
                                                              uu___2))))
                                              (fun uu___2 ->
                                                 (fun uu___2 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Prover.AutoLem.fst"
                                                                  (Prims.of_int (270))
                                                                  (Prims.of_int (31))
                                                                  (Prims.of_int (276))
                                                                  (Prims.of_int (3)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Prover.AutoLem.fst"
                                                                  (Prims.of_int (270))
                                                                  (Prims.of_int (31))
                                                                  (Prims.of_int (276))
                                                                  (Prims.of_int (3)))))
                                                         (Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (40)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (3)))))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    pst.Pulse_Checker_Prover_Base.unsolved))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Unsolved:")
                                                                    uu___3))))
                                                               (fun uu___3 ->
                                                                  (fun uu___3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    pst.Pulse_Checker_Prover_Base.solved))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Solved:")
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (51)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Remaining ctx:")
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
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    uu___146)
                                                                    (FStar_Reflection_V2_Builtins.vars_of_env
                                                                    (Pulse_Typing.elab_env
                                                                    pst.Pulse_Checker_Prover_Base.pg))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "env =")
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    [uu___6]))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___5 ::
                                                                    uu___6))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___4 ::
                                                                    uu___5))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___3 ::
                                                                    uu___4))))
                                                                    uu___3)))
                                                         (fun uu___3 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___4 ->
                                                                 uu___2 ::
                                                                 uu___3))))
                                                   uu___2)))
                                        (fun uu___2 ->
                                           (fun uu___2 ->
                                              Obj.magic
                                                (Pulse_Typing_Env.warn_doc
                                                   pst.Pulse_Checker_Prover_Base.pg
                                                   (FStar_Pervasives_Native.Some
                                                      q_rng) uu___2)) uu___2))))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.AutoLem.fst"
                                                 (Prims.of_int (278))
                                                 (Prims.of_int (11))
                                                 (Prims.of_int (278))
                                                 (Prims.of_int (17)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Checker.Prover.AutoLem.fst"
                                                 (Prims.of_int (278))
                                                 (Prims.of_int (20))
                                                 (Prims.of_int (373))
                                                 (Prims.of_int (13)))))
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              pst.Pulse_Checker_Prover_Base.pg))
                                        (fun uu___2 ->
                                           (fun e0 ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.AutoLem.fst"
                                                            (Prims.of_int (280))
                                                            (Prims.of_int (11))
                                                            (Prims.of_int (280))
                                                            (Prims.of_int (28)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Prover.AutoLem.fst"
                                                            (Prims.of_int (280))
                                                            (Prims.of_int (31))
                                                            (Prims.of_int (373))
                                                            (Prims.of_int (13)))))
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         FStar_Tactics_NamedView.pack
                                                           (FStar_Tactics_NamedView.Tv_FVar
                                                              fv)))
                                                   (fun uu___2 ->
                                                      (fun tm ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (24)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                              (Obj.magic
                                                                 (typ_of_fv
                                                                    fv))
                                                              (fun uu___2 ->
                                                                 (fun typ ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    typ))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "typ = ")
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    [uu___2]))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.warn_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (FStar_Pervasives_Native.Some
                                                                    q_rng)
                                                                    uu___2))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Pulse_Typing.elab_env
                                                                    e0))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun fe0
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (instantiate_fun
                                                                    preamble
                                                                    pst fe0
                                                                    tm typ))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (e', uvs,
                                                                    tm1,
                                                                    typ1) ->
                                                                    (match 
                                                                    Pulse_Readback.readback_comp
                                                                    typ1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    cc ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match cc
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_Tot
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    (debug
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    pp_fv fv))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___6
                                                                    (Pulse_PP.text
                                                                    "because it's a total term")))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Skipping ")
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    [uu___6]))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.warn_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (FStar_Pervasives_Native.Some
                                                                    q_rng)
                                                                    uu___6))
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.None))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STAtomic
                                                                    (uu___4,
                                                                    uu___5,
                                                                    uu___6)
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    (debug
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    pp_fv fv))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_ctag
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    cc)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "because it's a")
                                                                    uu___9))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___8
                                                                    uu___9))))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Skipping ")
                                                                    uu___8))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    [uu___8]))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.warn_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (FStar_Pervasives_Native.Some
                                                                    q_rng)
                                                                    uu___8))
                                                                    uu___8))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pervasives_Native.None))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_ST
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    (debug
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    pp_fv fv))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_ctag
                                                                    (Pulse_Syntax_Base.ctag_of_comp_st
                                                                    cc)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "because it's a")
                                                                    uu___7))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___6
                                                                    uu___7))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Skipping ")
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    [uu___6]))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.warn_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (FStar_Pervasives_Native.Some
                                                                    q_rng)
                                                                    uu___6))
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.None))
                                                                    | 
                                                                    Pulse_Syntax_Base.C_STGhost
                                                                    (uu___4,
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    = u;
                                                                    Pulse_Syntax_Base.res
                                                                    = res;
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    = post;_})
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (debug
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (310))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    pp_fv fv))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    uu___6
                                                                    (Pulse_PP.text
                                                                    "is a ghost step")))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_universe
                                                                    u))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "u = ")
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
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    res))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "res = ")
                                                                    uu___8))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    pre))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "pre = ")
                                                                    uu___9))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    (explode
                                                                    post))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_List_Tot_Base.map
                                                                    (fun t ->
                                                                    t)
                                                                    uu___10))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    uu___10))
                                                                    uu___10)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "post = ")
                                                                    uu___10))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    [uu___10]))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    -> uu___9
                                                                    ::
                                                                    uu___10))))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> uu___8
                                                                    :: uu___9))))
                                                                    uu___8)))
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
                                                                    uu___6 ::
                                                                    uu___7))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.warn_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (FStar_Pervasives_Native.Some
                                                                    q_rng)
                                                                    uu___6))
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
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (explode
                                                                    post))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    trig::rest
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    trig))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "trig = ")
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
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    q))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "q = ")
                                                                    uu___8))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    uu___146)
                                                                    (FStar_Reflection_V2_Builtins.vars_of_env
                                                                    e')))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "env =")
                                                                    uu___9))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    [uu___9]))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> uu___8
                                                                    :: uu___9))))
                                                                    uu___8)))
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
                                                                    (Pulse_PP.text
                                                                    "Trying to unify post with the resource")
                                                                    :: uu___7))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.warn_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (FStar_Pervasives_Native.Some
                                                                    q_rng)
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
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (14)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (326))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    "{{"))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.unify_env
                                                                    e' trig q))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun b ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (14)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.print
                                                                    "}}"))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (debug
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_bool
                                                                    b))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "unif result = ")
                                                                    uu___11))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_universe
                                                                    u))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "u = ")
                                                                    uu___12))))
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
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (332))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    res))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "res = ")
                                                                    uu___13))))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (333))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    pre))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "pre = ")
                                                                    uu___14))))
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
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    (explode
                                                                    post))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_List_Tot_Base.map
                                                                    (fun t ->
                                                                    t)
                                                                    uu___15))))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    uu___15))
                                                                    uu___15)))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "post = ")
                                                                    uu___15))))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    tm1))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "t = ")
                                                                    uu___16))))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    [uu___16]))))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    uu___15
                                                                    ::
                                                                    uu___16))))
                                                                    uu___15)))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    uu___14
                                                                    ::
                                                                    uu___15))))
                                                                    uu___14)))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    uu___13
                                                                    ::
                                                                    uu___14))))
                                                                    uu___13)))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    uu___12
                                                                    ::
                                                                    uu___13))))
                                                                    uu___12)))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    uu___11
                                                                    ::
                                                                    uu___12))))
                                                                    uu___11)))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.warn_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (FStar_Pervasives_Native.Some
                                                                    q_rng)
                                                                    uu___11))
                                                                    uu___11))))
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
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                                    (if
                                                                    Prims.op_Negation
                                                                    b
                                                                    then
                                                                    FStar_Tactics_Effect.raise
                                                                    Retry
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> ()))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    (explode
                                                                    pre))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_List_Tot_Base.map
                                                                    (fun t ->
                                                                    t)
                                                                    uu___12))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun pre'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (remove
                                                                    e'
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt
                                                                    pre'))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    rest
                                                                    uu___12))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    new_ctx
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    new_ctx))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "new_ctx = ")
                                                                    uu___12))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    [uu___12]))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.warn_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (FStar_Pervasives_Native.Some
                                                                    q_rng)
                                                                    uu___12))
                                                                    uu___12)))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Checker_Prover_Base.pg
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.pg);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt
                                                                    = new_ctx;
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.uvs
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.uvs);
                                                                    Pulse_Checker_Prover_Base.ss
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.ss);
                                                                    Pulse_Checker_Prover_Base.nts
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.nts);
                                                                    Pulse_Checker_Prover_Base.solved
                                                                    =
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    q
                                                                    pst.Pulse_Checker_Prover_Base.solved);
                                                                    Pulse_Checker_Prover_Base.unsolved
                                                                    =
                                                                    unsolved';
                                                                    Pulse_Checker_Prover_Base.k
                                                                    =
                                                                    (Pulse_Checker_Base.k_elab_trans
                                                                    preamble.Pulse_Checker_Prover_Base.g0
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    preamble.Pulse_Checker_Prover_Base.ctxt
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Substs.ss_term
                                                                    pst.Pulse_Checker_Prover_Base.solved
                                                                    pst.Pulse_Checker_Prover_Base.ss))
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    (Pulse_Syntax_Pure.list_as_vprop
                                                                    new_ctx)
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Substs.ss_term
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    q
                                                                    pst.Pulse_Checker_Prover_Base.solved)
                                                                    pst.Pulse_Checker_Prover_Base.ss))
                                                                    pst.Pulse_Checker_Prover_Base.k
                                                                    (fun
                                                                    post1 ->
                                                                    fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___14
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (t, c, d)))));
                                                                    Pulse_Checker_Prover_Base.goals_inv
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.solved_inv
                                                                    = ();
                                                                    Pulse_Checker_Prover_Base.progress
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.progress);
                                                                    Pulse_Checker_Prover_Base.allow_ambiguous
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.allow_ambiguous)
                                                                    }))))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7))))
                                                                    uu___6)))
                                                                    uu___5)))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                   uu___2)))
                                                        uu___2))) uu___2)))
                                  uu___1))) uu___1)
let (guided_autolem : Pulse_Checker_Prover_Base.guided_prover_step) =
  fun preamble ->
    fun pst ->
      fun q ->
        fun unsolved' ->
          fun uu___ ->
            fun prover ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.Prover.AutoLem.fst"
                         (Prims.of_int (381)) (Prims.of_int (14))
                         (Prims.of_int (381)) (Prims.of_int (29)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.Prover.AutoLem.fst"
                         (Prims.of_int (382)) (Prims.of_int (2))
                         (Prims.of_int (398)) (Prims.of_int (66)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      FStar_Reflection_V2_Builtins.range_of_term q))
                (fun uu___1 ->
                   (fun q_rng ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.AutoLem.fst"
                                    (Prims.of_int (382)) (Prims.of_int (2))
                                    (Prims.of_int (388)) (Prims.of_int (4)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.AutoLem.fst"
                                    (Prims.of_int (388)) (Prims.of_int (5))
                                    (Prims.of_int (398)) (Prims.of_int (66)))))
                           (Obj.magic
                              (debug pst.Pulse_Checker_Prover_Base.pg
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.AutoLem.fst"
                                               (Prims.of_int (383))
                                               (Prims.of_int (31))
                                               (Prims.of_int (388))
                                               (Prims.of_int (3)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.AutoLem.fst"
                                               (Prims.of_int (383))
                                               (Prims.of_int (2))
                                               (Prims.of_int (388))
                                               (Prims.of_int (3)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.AutoLem.fst"
                                                     (Prims.of_int (384))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (384))
                                                     (Prims.of_int (48)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.AutoLem.fst"
                                                     (Prims.of_int (383))
                                                     (Prims.of_int (31))
                                                     (Prims.of_int (388))
                                                     (Prims.of_int (3)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.AutoLem.fst"
                                                           (Prims.of_int (384))
                                                           (Prims.of_int (44))
                                                           (Prims.of_int (384))
                                                           (Prims.of_int (48)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.AutoLem.fst"
                                                           (Prims.of_int (384))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (384))
                                                           (Prims.of_int (48)))))
                                                  (Obj.magic
                                                     (Pulse_PP.pp
                                                        Pulse_PP.printable_term
                                                        q))
                                                  (fun uu___2 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          FStar_Pprint.op_Hat_Slash_Hat
                                                            (Pulse_PP.text
                                                               "Trying autolem for resource:")
                                                            uu___2))))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.AutoLem.fst"
                                                                (Prims.of_int (383))
                                                                (Prims.of_int (31))
                                                                (Prims.of_int (388))
                                                                (Prims.of_int (3)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.AutoLem.fst"
                                                                (Prims.of_int (383))
                                                                (Prims.of_int (31))
                                                                (Prims.of_int (388))
                                                                (Prims.of_int (3)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (40)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (3)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (40)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (40)))))
                                                                   (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    pst.Pulse_Checker_Prover_Base.unsolved))
                                                                   (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Unsolved:")
                                                                    uu___3))))
                                                             (fun uu___3 ->
                                                                (fun uu___3
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    pst.Pulse_Checker_Prover_Base.solved))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Solved:")
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (51)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Remaining ctx:")
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    [uu___5]))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___4 ::
                                                                    uu___5))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___3 ::
                                                                    uu___4))))
                                                                  uu___3)))
                                                       (fun uu___3 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___4 ->
                                                               uu___2 ::
                                                               uu___3))))
                                                 uu___2)))
                                      (fun uu___2 ->
                                         (fun uu___2 ->
                                            Obj.magic
                                              (Pulse_Typing_Env.warn_doc
                                                 pst.Pulse_Checker_Prover_Base.pg
                                                 (FStar_Pervasives_Native.Some
                                                    q_rng) uu___2)) uu___2))))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.AutoLem.fst"
                                               (Prims.of_int (390))
                                               (Prims.of_int (14))
                                               (Prims.of_int (390))
                                               (Prims.of_int (66)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.AutoLem.fst"
                                               (Prims.of_int (392))
                                               (Prims.of_int (2))
                                               (Prims.of_int (398))
                                               (Prims.of_int (66)))))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            FStar_Reflection_V2_Builtins.lookup_attr
                                              guided_autolem_attr
                                              (Pulse_Typing_Env.fstar_env
                                                 pst.Pulse_Checker_Prover_Base.pg)))
                                      (fun uu___2 ->
                                         (fun cands ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.AutoLem.fst"
                                                          (Prims.of_int (392))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (395))
                                                          (Prims.of_int (4)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Prover.AutoLem.fst"
                                                          (Prims.of_int (398))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (398))
                                                          (Prims.of_int (66)))))
                                                 (Obj.magic
                                                    (debug
                                                       pst.Pulse_Checker_Prover_Base.pg
                                                       (fun uu___2 ->
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (3)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (3)))))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (37)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (3)))))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.AutoLem.fst"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    pp_fv)
                                                                    cands))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Candidates = ")
                                                                    uu___3))))
                                                                  (fun uu___3
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    [uu___3]))))
                                                            (fun uu___3 ->
                                                               (fun uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    Pulse_Typing_Env.warn_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (FStar_Pervasives_Native.Some
                                                                    q_rng)
                                                                    uu___3))
                                                                 uu___3))))
                                                 (fun uu___2 ->
                                                    (fun uu___2 ->
                                                       Obj.magic
                                                         (apply_first
                                                            (guided_autolem1
                                                               preamble pst q
                                                               unsolved' ()
                                                               prover) cands))
                                                      uu___2))) uu___2)))
                                uu___1))) uu___1)