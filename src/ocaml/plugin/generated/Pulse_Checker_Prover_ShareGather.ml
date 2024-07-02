open Prims
let (debug :
  Pulse_Typing_Env.env ->
    (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun f ->
           if
             Pulse_RuntimeUtils.debug_at_level (Pulse_Typing_Env.fstar_env g)
               "prover.share_gather"
           then Obj.magic (Obj.repr (f ()))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
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
            (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
               (Prims.of_int (64)) (Prims.of_int (17)) (Prims.of_int (64))
               (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
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
                              "Pulse.Checker.Prover.ShareGather.fst"
                              (Prims.of_int (65)) (Prims.of_int (8))
                              (Prims.of_int (65)) (Prims.of_int (18)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Pulse.Checker.Prover.ShareGather.fst"
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
let (destruct_pts_to :
  Pulse_Syntax_Base.vprop ->
    ((FStar_Reflection_Types.typ * FStar_Reflection_Types.term *
       FStar_Reflection_Types.term * FStar_Reflection_Types.term)
       FStar_Pervasives_Native.option,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun v ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
               (Prims.of_int (71)) (Prims.of_int (8)) (Prims.of_int (71))
               (Prims.of_int (13)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
               (Prims.of_int (71)) (Prims.of_int (2)) (Prims.of_int (76))
               (Prims.of_int (13))))) (Obj.magic (hua v))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with
              | FStar_Pervasives_Native.Some
                  (fv, uu___2,
                   (ty, FStar_Reflection_V2_Data.Q_Implicit)::(r,
                                                               FStar_Reflection_V2_Data.Q_Explicit)::
                   (p, FStar_Reflection_V2_Data.Q_Implicit)::(e,
                                                              FStar_Reflection_V2_Data.Q_Explicit)::[])
                  ->
                  if
                    (FStar_Reflection_V2_Builtins.inspect_fv fv) =
                      ["Pulse"; "Lib"; "Reference"; "pts_to"]
                  then FStar_Pervasives_Native.Some (ty, r, p, e)
                  else FStar_Pervasives_Native.None
              | uu___2 -> FStar_Pervasives_Native.None))
let (is_half :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term FStar_Pervasives_Native.option, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun p ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
               (Prims.of_int (81)) (Prims.of_int (8)) (Prims.of_int (81))
               (Prims.of_int (13)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
               (Prims.of_int (81)) (Prims.of_int (2)) (Prims.of_int (87))
               (Prims.of_int (13))))) (Obj.magic (hua p))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with
              | FStar_Pervasives_Native.Some
                  (fv, [],
                   (perm, FStar_Reflection_V2_Data.Q_Explicit)::(denom,
                                                                 FStar_Reflection_V2_Data.Q_Explicit)::[])
                  ->
                  if
                    ((FStar_Reflection_V2_Builtins.inspect_fv fv) =
                       ["FStar"; "Real"; "op_Slash_Dot"])
                      &&
                      (FStar_Reflection_V2_TermEq.term_eq denom
                         (FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_Const
                               (FStar_Reflection_V2_Data.C_Real "2.0"))))
                  then FStar_Pervasives_Native.Some perm
                  else FStar_Pervasives_Native.None
              | uu___2 -> FStar_Pervasives_Native.None))
let rec (destruct_halves :
  FStar_Reflection_Types.term ->
    ((Prims.nat * FStar_Reflection_Types.term), unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
               (Prims.of_int (91)) (Prims.of_int (8)) (Prims.of_int (91))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
               (Prims.of_int (91)) (Prims.of_int (2)) (Prims.of_int (95))
               (Prims.of_int (15))))) (Obj.magic (is_half t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Pervasives_Native.Some p ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.ShareGather.fst"
                                 (Prims.of_int (93)) (Prims.of_int (15))
                                 (Prims.of_int (93)) (Prims.of_int (32)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.ShareGather.fst"
                                 (Prims.of_int (92)) (Prims.of_int (13))
                                 (Prims.of_int (94)) (Prims.of_int (14)))))
                        (Obj.magic (destruct_halves p))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 ->
                                match uu___1 with
                                | (n, p1) -> ((n + Prims.int_one), p1)))))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> (Prims.int_zero, t))))) uu___)
let (destruct_pts_to_half_n :
  Pulse_Syntax_Base.vprop ->
    ((Prims.nat * FStar_Reflection_Types.typ * FStar_Reflection_Types.term *
       FStar_Reflection_Types.term * FStar_Reflection_Types.term)
       FStar_Pervasives_Native.option,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun v ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
               (Prims.of_int (98)) (Prims.of_int (8)) (Prims.of_int (98))
               (Prims.of_int (25)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
               (Prims.of_int (98)) (Prims.of_int (2)) (Prims.of_int (103))
               (Prims.of_int (13))))) (Obj.magic (destruct_pts_to v))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Pervasives_Native.Some (ty, r, p, e) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.ShareGather.fst"
                                 (Prims.of_int (100)) (Prims.of_int (15))
                                 (Prims.of_int (100)) (Prims.of_int (32)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.ShareGather.fst"
                                 (Prims.of_int (99)) (Prims.of_int (26))
                                 (Prims.of_int (102)) (Prims.of_int (3)))))
                        (Obj.magic (destruct_halves p))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 ->
                                match uu___1 with
                                | (n, p1) ->
                                    FStar_Pervasives_Native.Some
                                      (n, ty, r, p1, e)))))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> FStar_Pervasives_Native.None)))) uu___)
let (destruct_pts_to_half :
  Pulse_Syntax_Base.vprop ->
    ((FStar_Reflection_Types.typ * FStar_Reflection_Types.term *
       FStar_Reflection_Types.term * FStar_Reflection_Types.term)
       FStar_Pervasives_Native.option,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun v ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
               (Prims.of_int (106)) (Prims.of_int (8)) (Prims.of_int (106))
               (Prims.of_int (25)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
               (Prims.of_int (106)) (Prims.of_int (2)) (Prims.of_int (112))
               (Prims.of_int (13))))) (Obj.magic (destruct_pts_to v))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Pervasives_Native.Some (ty, r, p, e) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.ShareGather.fst"
                                 (Prims.of_int (108)) (Prims.of_int (11))
                                 (Prims.of_int (108)) (Prims.of_int (20)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Prover.ShareGather.fst"
                                 (Prims.of_int (107)) (Prims.of_int (26))
                                 (Prims.of_int (111)) (Prims.of_int (3)))))
                        (Obj.magic (is_half p))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 ->
                                match uu___1 with
                                | FStar_Pervasives_Native.Some p' ->
                                    FStar_Pervasives_Native.Some
                                      (ty, r, p', e)
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.None))))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> FStar_Pervasives_Native.None)))) uu___)
let (is_pts_to :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        Pulse_Syntax_Base.vprop ->
          (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t_r ->
    fun t_p ->
      fun t_e ->
        fun v ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "Pulse.Checker.Prover.ShareGather.fst"
                     (Prims.of_int (115)) (Prims.of_int (8))
                     (Prims.of_int (115)) (Prims.of_int (25)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "Pulse.Checker.Prover.ShareGather.fst"
                     (Prims.of_int (115)) (Prims.of_int (2))
                     (Prims.of_int (117)) (Prims.of_int (17)))))
            (Obj.magic (destruct_pts_to v))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    match uu___ with
                    | FStar_Pervasives_Native.Some (uu___2, r, p, e) ->
                        ((FStar_Reflection_V2_TermEq.term_eq t_r r) &&
                           (FStar_Reflection_V2_TermEq.term_eq t_p p))
                          && (FStar_Reflection_V2_TermEq.term_eq t_e e)
                    | FStar_Pervasives_Native.None -> false))
let (is_pts_to_half_any :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      Pulse_Syntax_Base.vprop ->
        (FStar_Reflection_Types.term FStar_Pervasives_Native.option, 
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t_r ->
    fun t_p ->
      fun v ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
                   (Prims.of_int (120)) (Prims.of_int (8))
                   (Prims.of_int (120)) (Prims.of_int (30)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
                   (Prims.of_int (120)) (Prims.of_int (2))
                   (Prims.of_int (125)) (Prims.of_int (16)))))
          (Obj.magic (destruct_pts_to_half v))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  match uu___ with
                  | FStar_Pervasives_Native.Some (uu___2, r, p, e) ->
                      if
                        (FStar_Reflection_V2_TermEq.term_eq t_r r) &&
                          (FStar_Reflection_V2_TermEq.term_eq t_p p)
                      then FStar_Pervasives_Native.Some e
                      else FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None))
let (is_pts_to_half :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        Pulse_Syntax_Base.vprop ->
          (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t_r ->
    fun t_p ->
      fun t_e ->
        fun v ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "Pulse.Checker.Prover.ShareGather.fst"
                     (Prims.of_int (128)) (Prims.of_int (8))
                     (Prims.of_int (128)) (Prims.of_int (30)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "Pulse.Checker.Prover.ShareGather.fst"
                     (Prims.of_int (128)) (Prims.of_int (2))
                     (Prims.of_int (130)) (Prims.of_int (17)))))
            (Obj.magic (destruct_pts_to_half v))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    match uu___ with
                    | FStar_Pervasives_Native.Some (uu___2, r, p, e) ->
                        ((FStar_Reflection_V2_TermEq.term_eq t_r r) &&
                           (FStar_Reflection_V2_TermEq.term_eq t_p p))
                          && (FStar_Reflection_V2_TermEq.term_eq t_e e)
                    | FStar_Pervasives_Native.None -> false))
let mk_pts_to :
  'uuuuu .
    'uuuuu ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term -> Pulse_Syntax_Base.term
  =
  fun rng ->
    fun ty ->
      fun r ->
        fun p ->
          fun e ->
            FStar_Reflection_V2_Derived.mk_app
              (FStar_Reflection_V2_Builtins.pack_ln
                 (FStar_Reflection_V2_Data.Tv_FVar
                    (FStar_Reflection_V2_Builtins.pack_fv
                       ["Pulse"; "Lib"; "Reference"; "pts_to"])))
              [(ty, FStar_Reflection_V2_Data.Q_Implicit);
              (r, FStar_Reflection_V2_Data.Q_Explicit);
              (p, FStar_Reflection_V2_Data.Q_Implicit);
              (e, FStar_Reflection_V2_Data.Q_Explicit)]
let rec (find_pts_to :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        Pulse_Syntax_Base.vprop Prims.list ->
          ((Pulse_Syntax_Base.vprop * Pulse_Syntax_Base.vprop Prims.list)
             FStar_Pervasives_Native.option,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun t_r ->
             fun t_p ->
               fun t_v ->
                 fun ctx ->
                   match ctx with
                   | [] ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> FStar_Pervasives_Native.None)))
                   | v::vs ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Prover.ShareGather.fst"
                                        (Prims.of_int (144))
                                        (Prims.of_int (7))
                                        (Prims.of_int (144))
                                        (Prims.of_int (30)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Prover.ShareGather.fst"
                                        (Prims.of_int (144))
                                        (Prims.of_int (4))
                                        (Prims.of_int (148))
                                        (Prims.of_int (24)))))
                               (Obj.magic (is_pts_to t_r t_p t_v v))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     if uu___
                                     then
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  FStar_Pervasives_Native.Some
                                                    (v, vs))))
                                     else
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.ShareGather.fst"
                                                        (Prims.of_int (147))
                                                        (Prims.of_int (22))
                                                        (Prims.of_int (147))
                                                        (Prims.of_int (48)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.ShareGather.fst"
                                                        (Prims.of_int (147))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (148))
                                                        (Prims.of_int (24)))))
                                               (Obj.magic
                                                  (find_pts_to t_r t_p t_v vs))
                                               (fun uu___2 ->
                                                  (fun uu___2 ->
                                                     Obj.magic
                                                       (op_let_Bang uu___26
                                                          () ()
                                                          (Obj.magic uu___2)
                                                          (fun uu___3 ->
                                                             (fun uu___3 ->
                                                                let uu___3 =
                                                                  Obj.magic
                                                                    uu___3 in
                                                                match uu___3
                                                                with
                                                                | (v', vs1)
                                                                    ->
                                                                    Obj.magic
                                                                    (return
                                                                    uu___26
                                                                    ()
                                                                    (Obj.magic
                                                                    (v', (v
                                                                    :: vs1)))))
                                                               uu___3)))
                                                    uu___2)))) uu___))))
            uu___3 uu___2 uu___1 uu___
let rec (find_pts_to_half :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        Pulse_Syntax_Base.vprop Prims.list ->
          ((Pulse_Syntax_Base.vprop * Pulse_Syntax_Base.vprop Prims.list)
             FStar_Pervasives_Native.option,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun t_r ->
             fun t_p ->
               fun t_v ->
                 fun ctx ->
                   match ctx with
                   | [] ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> FStar_Pervasives_Native.None)))
                   | v::vs ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Prover.ShareGather.fst"
                                        (Prims.of_int (154))
                                        (Prims.of_int (7))
                                        (Prims.of_int (154))
                                        (Prims.of_int (35)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Prover.ShareGather.fst"
                                        (Prims.of_int (154))
                                        (Prims.of_int (4))
                                        (Prims.of_int (158))
                                        (Prims.of_int (24)))))
                               (Obj.magic (is_pts_to_half t_r t_p t_v v))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     if uu___
                                     then
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  FStar_Pervasives_Native.Some
                                                    (v, vs))))
                                     else
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.ShareGather.fst"
                                                        (Prims.of_int (157))
                                                        (Prims.of_int (22))
                                                        (Prims.of_int (157))
                                                        (Prims.of_int (53)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Prover.ShareGather.fst"
                                                        (Prims.of_int (157))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (158))
                                                        (Prims.of_int (24)))))
                                               (Obj.magic
                                                  (find_pts_to_half t_r t_p
                                                     t_v vs))
                                               (fun uu___2 ->
                                                  (fun uu___2 ->
                                                     Obj.magic
                                                       (op_let_Bang uu___26
                                                          () ()
                                                          (Obj.magic uu___2)
                                                          (fun uu___3 ->
                                                             (fun uu___3 ->
                                                                let uu___3 =
                                                                  Obj.magic
                                                                    uu___3 in
                                                                match uu___3
                                                                with
                                                                | (v', vs1)
                                                                    ->
                                                                    Obj.magic
                                                                    (return
                                                                    uu___26
                                                                    ()
                                                                    (Obj.magic
                                                                    (v', (v
                                                                    :: vs1)))))
                                                               uu___3)))
                                                    uu___2)))) uu___))))
            uu___3 uu___2 uu___1 uu___
let rec (find_pts_to_half_any :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      Pulse_Syntax_Base.vprop Prims.list ->
        ((FStar_Reflection_Types.term * Pulse_Syntax_Base.vprop *
           Pulse_Syntax_Base.vprop Prims.list) FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun t_r ->
           fun t_p ->
             fun ctx ->
               match ctx with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> FStar_Pervasives_Native.None)))
               | v::vs ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.ShareGather.fst"
                                    (Prims.of_int (164)) (Prims.of_int (10))
                                    (Prims.of_int (164)) (Prims.of_int (38)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.ShareGather.fst"
                                    (Prims.of_int (164)) (Prims.of_int (4))
                                    (Prims.of_int (168)) (Prims.of_int (28)))))
                           (Obj.magic (is_pts_to_half_any t_r t_p v))
                           (fun uu___ ->
                              (fun uu___ ->
                                 match uu___ with
                                 | FStar_Pervasives_Native.Some e ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                FStar_Pervasives_Native.Some
                                                  (e, v, vs))))
                                 | FStar_Pervasives_Native.None ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Prover.ShareGather.fst"
                                                      (Prims.of_int (167))
                                                      (Prims.of_int (26))
                                                      (Prims.of_int (167))
                                                      (Prims.of_int (57)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Checker.Prover.ShareGather.fst"
                                                      (Prims.of_int (167))
                                                      (Prims.of_int (6))
                                                      (Prims.of_int (168))
                                                      (Prims.of_int (28)))))
                                             (Obj.magic
                                                (find_pts_to_half_any t_r t_p
                                                   vs))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   Obj.magic
                                                     (op_let_Bang uu___26 ()
                                                        () (Obj.magic uu___1)
                                                        (fun uu___2 ->
                                                           (fun uu___2 ->
                                                              let uu___2 =
                                                                Obj.magic
                                                                  uu___2 in
                                                              match uu___2
                                                              with
                                                              | (e', v', vs1)
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    return
                                                                    uu___26
                                                                    ()
                                                                    (Obj.magic
                                                                    (e', v',
                                                                    (v ::
                                                                    vs1)))))
                                                             uu___2))) uu___1))))
                                uu___)))) uu___2 uu___1 uu___
let rec (find_two_halves :
  Pulse_Syntax_Base.vprop Prims.list ->
    (((FStar_Reflection_Types.typ * FStar_Reflection_Types.term *
       FStar_Reflection_Types.term * FStar_Reflection_Types.term) *
       FStar_Reflection_Types.term * Pulse_Syntax_Base.vprop *
       Pulse_Syntax_Base.vprop * Pulse_Syntax_Base.vprop Prims.list)
       FStar_Pervasives_Native.option,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun ctx ->
       match ctx with
       | [] ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pervasives_Native.None)))
       | v::vs ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.Prover.ShareGather.fst"
                            (Prims.of_int (175)) (Prims.of_int (6))
                            (Prims.of_int (176)) (Prims.of_int (32)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.Prover.ShareGather.fst"
                            (Prims.of_int (178)) (Prims.of_int (4))
                            (Prims.of_int (182)) (Prims.of_int (19)))))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         fun uu___1 ->
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.ShareGather.fst"
                                      (Prims.of_int (175))
                                      (Prims.of_int (32))
                                      (Prims.of_int (175))
                                      (Prims.of_int (50)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Checker.Prover.ShareGather.fst"
                                      (Prims.of_int (175)) (Prims.of_int (6))
                                      (Prims.of_int (176))
                                      (Prims.of_int (32)))))
                             (Obj.magic (find_two_halves vs))
                             (fun uu___2 ->
                                (fun uu___2 ->
                                   Obj.magic
                                     (op_let_Bang uu___26 () ()
                                        (Obj.magic uu___2)
                                        (fun uu___3 ->
                                           (fun uu___3 ->
                                              let uu___3 = Obj.magic uu___3 in
                                              Obj.magic
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___4 ->
                                                      match uu___3 with
                                                      | (r, e, v1, v2, vs1)
                                                          ->
                                                          FStar_Pervasives_Native.Some
                                                            (r, e, v1, v2, (v
                                                              :: vs1)))))
                                             uu___3))) uu___2)))
                   (fun uu___ ->
                      (fun fallback ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.ShareGather.fst"
                                       (Prims.of_int (178))
                                       (Prims.of_int (4))
                                       (Prims.of_int (182))
                                       (Prims.of_int (6)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.ShareGather.fst"
                                       (Prims.of_int (178))
                                       (Prims.of_int (4))
                                       (Prims.of_int (182))
                                       (Prims.of_int (19)))))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.ShareGather.fst"
                                             (Prims.of_int (179))
                                             (Prims.of_int (27))
                                             (Prims.of_int (179))
                                             (Prims.of_int (49)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.ShareGather.fst"
                                             (Prims.of_int (178))
                                             (Prims.of_int (4))
                                             (Prims.of_int (182))
                                             (Prims.of_int (6)))))
                                    (Obj.magic (destruct_pts_to_half v))
                                    (fun uu___ ->
                                       (fun uu___ ->
                                          Obj.magic
                                            (op_let_Bang uu___26 () ()
                                               (Obj.magic uu___)
                                               (fun uu___1 ->
                                                  (fun uu___1 ->
                                                     let uu___1 =
                                                       Obj.magic uu___1 in
                                                     match uu___1 with
                                                     | (ty, r, p, e) ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (54)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (42)))))
                                                              (Obj.magic
                                                                 (find_pts_to_half_any
                                                                    r p vs))
                                                              (fun uu___2 ->
                                                                 (fun uu___2
                                                                    ->
                                                                    Obj.magic
                                                                    (op_let_Bang
                                                                    uu___26
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___2)
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    let uu___3
                                                                    =
                                                                    Obj.magic
                                                                    uu___3 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (e', v',
                                                                    vs') ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((ty, r,
                                                                    p, e),
                                                                    e', v,
                                                                    v', vs'))))
                                                                    uu___3)))
                                                                   uu___2)))
                                                    uu___1))) uu___)))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    Obj.magic
                                      (op_Less_Bar_Greater
                                         (alternative_option ()) uu___
                                         fallback)) uu___))) uu___)))) uu___
let (eager_gather1 :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit Pulse_Checker_Prover_Base.prover_state
         FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun preamble ->
    fun pst ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
                 (Prims.of_int (188)) (Prims.of_int (12))
                 (Prims.of_int (190)) (Prims.of_int (29)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
                 (Prims.of_int (193)) (Prims.of_int (2)) (Prims.of_int (230))
                 (Prims.of_int (13)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              match pst.Pulse_Checker_Prover_Base.remaining_ctxt with
              | [] -> FStar_Range.range_0
              | v::uu___1 -> FStar_Reflection_V2_Builtins.range_of_term v))
        (fun uu___ ->
           (fun rng ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.Prover.ShareGather.fst"
                            (Prims.of_int (193)) (Prims.of_int (2))
                            (Prims.of_int (199)) (Prims.of_int (6)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "Pulse.Checker.Prover.ShareGather.fst"
                            (Prims.of_int (200)) (Prims.of_int (2))
                            (Prims.of_int (230)) (Prims.of_int (13)))))
                   (Obj.magic
                      (debug pst.Pulse_Checker_Prover_Base.pg
                         (fun uu___ ->
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.ShareGather.fst"
                                       (Prims.of_int (194))
                                       (Prims.of_int (31))
                                       (Prims.of_int (199))
                                       (Prims.of_int (5)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.ShareGather.fst"
                                       (Prims.of_int (194))
                                       (Prims.of_int (4))
                                       (Prims.of_int (199))
                                       (Prims.of_int (5)))))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.ShareGather.fst"
                                             (Prims.of_int (194))
                                             (Prims.of_int (31))
                                             (Prims.of_int (199))
                                             (Prims.of_int (5)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Prover.ShareGather.fst"
                                             (Prims.of_int (194))
                                             (Prims.of_int (31))
                                             (Prims.of_int (199))
                                             (Prims.of_int (5)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.ShareGather.fst"
                                                   (Prims.of_int (196))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (196))
                                                   (Prims.of_int (42)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Checker.Prover.ShareGather.fst"
                                                   (Prims.of_int (194))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (199))
                                                   (Prims.of_int (5)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.ShareGather.fst"
                                                         (Prims.of_int (196))
                                                         (Prims.of_int (27))
                                                         (Prims.of_int (196))
                                                         (Prims.of_int (42)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.ShareGather.fst"
                                                         (Prims.of_int (196))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (196))
                                                         (Prims.of_int (42)))))
                                                (Obj.magic
                                                   (Pulse_PP.pp
                                                      (Pulse_PP.printable_list
                                                         Pulse_PP.printable_term)
                                                      pst.Pulse_Checker_Prover_Base.unsolved))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        FStar_Pprint.op_Hat_Hat
                                                          (Pulse_PP.text
                                                             "Unsolved: ")
                                                          uu___1))))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.ShareGather.fst"
                                                              (Prims.of_int (194))
                                                              (Prims.of_int (31))
                                                              (Prims.of_int (199))
                                                              (Prims.of_int (5)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.ShareGather.fst"
                                                              (Prims.of_int (194))
                                                              (Prims.of_int (31))
                                                              (Prims.of_int (199))
                                                              (Prims.of_int (5)))))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (38)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (5)))))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (38)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (38)))))
                                                                 (Obj.magic
                                                                    (
                                                                    Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    pst.Pulse_Checker_Prover_Base.solved))
                                                                 (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "Solved: ")
                                                                    uu___2))))
                                                           (fun uu___2 ->
                                                              (fun uu___2 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (194))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (Pulse_PP.text
                                                                    "Remaining ctx: ")
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    [uu___3]))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___2 ::
                                                                    uu___3))))
                                                                uu___2)))
                                                     (fun uu___2 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 ->
                                                             uu___1 :: uu___2))))
                                               uu___1)))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            (Pulse_PP.text
                                               "Trying eager gather")
                                            :: uu___1))))
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    Obj.magic
                                      (Pulse_Typing_Env.warn_doc
                                         pst.Pulse_Checker_Prover_Base.pg
                                         (FStar_Pervasives_Native.Some rng)
                                         uu___1)) uu___1))))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.ShareGather.fst"
                                       (Prims.of_int (200))
                                       (Prims.of_int (8))
                                       (Prims.of_int (200))
                                       (Prims.of_int (42)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Prover.ShareGather.fst"
                                       (Prims.of_int (200))
                                       (Prims.of_int (2))
                                       (Prims.of_int (230))
                                       (Prims.of_int (13)))))
                              (Obj.magic
                                 (find_two_halves
                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt))
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    match uu___1 with
                                    | FStar_Pervasives_Native.None ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.ShareGather.fst"
                                                         (Prims.of_int (202))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (202))
                                                         (Prims.of_int (33)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.ShareGather.fst"
                                                         (Prims.of_int (203))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (203))
                                                         (Prims.of_int (8)))))
                                                (Obj.magic
                                                   (FStar_Tactics_V1_Builtins.print
                                                      "No two halves found"))
                                                (fun uu___2 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 ->
                                                        FStar_Pervasives_Native.None))))
                                    | FStar_Pervasives_Native.Some
                                        ((ty, r, p, e), e', v1, v2, ctxt') ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   FStar_Pervasives_Native.Some
                                                     {
                                                       Pulse_Checker_Prover_Base.pg
                                                         =
                                                         (pst.Pulse_Checker_Prover_Base.pg);
                                                       Pulse_Checker_Prover_Base.remaining_ctxt
                                                         =
                                                         ((mk_pts_to
                                                             (FStar_Reflection_V2_Builtins.range_of_term
                                                                v1) ty r p e)
                                                         ::
                                                         (Pulse_Syntax_Pure.tm_pure
                                                            (Pulse_Reflection_Util.mk_eq2
                                                               (FStar_Reflection_V2_Builtins.pack_universe
                                                                  FStar_Reflection_V2_Data.Uv_Zero)
                                                               ty e e')) ::
                                                         ctxt');
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
                                                         (pst.Pulse_Checker_Prover_Base.solved);
                                                       Pulse_Checker_Prover_Base.unsolved
                                                         =
                                                         (pst.Pulse_Checker_Prover_Base.unsolved);
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
                                                                    ((
                                                                    mk_pts_to
                                                                    (FStar_Reflection_V2_Builtins.range_of_term
                                                                    v1) ty r
                                                                    p e) ::
                                                                    (Pulse_Syntax_Pure.tm_pure
                                                                    (Pulse_Reflection_Util.mk_eq2
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Zero)
                                                                    ty e e'))
                                                                    :: ctxt'))
                                                                  preamble.Pulse_Checker_Prover_Base.frame)
                                                               (Pulse_Checker_Prover_Substs.ss_term
                                                                  pst.Pulse_Checker_Prover_Base.solved
                                                                  pst.Pulse_Checker_Prover_Base.ss))
                                                            pst.Pulse_Checker_Prover_Base.k
                                                            (fun post ->
                                                               fun uu___3 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
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
                                                     })))) uu___1))) uu___)))
             uu___)
let rec (eager_gather : Pulse_Checker_Prover_Base.eager_prover_step) =
  fun preamble ->
    fun pst ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
                 (Prims.of_int (233)) (Prims.of_int (8)) (Prims.of_int (233))
                 (Prims.of_int (25)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Checker.Prover.ShareGather.fst"
                 (Prims.of_int (233)) (Prims.of_int (2)) (Prims.of_int (235))
                 (Prims.of_int (15)))))
        (Obj.magic (eager_gather1 preamble pst))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives_Native.Some pst' ->
                  Obj.magic
                    (Obj.repr
                       (eager_gather preamble
                          {
                            Pulse_Checker_Prover_Base.pg =
                              (pst'.Pulse_Checker_Prover_Base.pg);
                            Pulse_Checker_Prover_Base.remaining_ctxt =
                              (pst'.Pulse_Checker_Prover_Base.remaining_ctxt);
                            Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                              = ();
                            Pulse_Checker_Prover_Base.uvs =
                              (pst'.Pulse_Checker_Prover_Base.uvs);
                            Pulse_Checker_Prover_Base.ss =
                              (pst'.Pulse_Checker_Prover_Base.ss);
                            Pulse_Checker_Prover_Base.nts =
                              (pst'.Pulse_Checker_Prover_Base.nts);
                            Pulse_Checker_Prover_Base.solved =
                              (pst'.Pulse_Checker_Prover_Base.solved);
                            Pulse_Checker_Prover_Base.unsolved =
                              (pst'.Pulse_Checker_Prover_Base.unsolved);
                            Pulse_Checker_Prover_Base.k =
                              (pst'.Pulse_Checker_Prover_Base.k);
                            Pulse_Checker_Prover_Base.goals_inv = ();
                            Pulse_Checker_Prover_Base.solved_inv = ();
                            Pulse_Checker_Prover_Base.progress = true;
                            Pulse_Checker_Prover_Base.allow_ambiguous =
                              (pst'.Pulse_Checker_Prover_Base.allow_ambiguous)
                          }))
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> pst))))
             uu___)
let rec (mk_n_half :
  Prims.nat -> FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun n ->
    fun p ->
      if n = Prims.int_zero
      then p
      else
        FStar_Reflection_V2_Derived.mk_e_app
          (FStar_Reflection_V2_Builtins.pack_ln
             (FStar_Reflection_V2_Data.Tv_FVar
                (FStar_Reflection_V2_Builtins.pack_fv
                   ["FStar"; "Real"; "op_Slash_Dot"])))
          [mk_n_half (n - Prims.int_one) p;
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_Const
               (FStar_Reflection_V2_Data.C_Real "2.0"))]
let (mk_half : FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun p -> mk_n_half Prims.int_one p
let rec (find_least_split :
  Prims.nat ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            Pulse_Syntax_Base.vprop Prims.list ->
              ((Prims.nat * FStar_Reflection_Types.term *
                 Pulse_Syntax_Base.vprop * Pulse_Syntax_Base.vprop Prims.list
                 * Pulse_Syntax_Base.vprop Prims.list)
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nsplits ->
    fun ty ->
      fun r ->
        fun p ->
          fun e ->
            fun ctx ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.Prover.ShareGather.fst"
                         (Prims.of_int (258)) (Prims.of_int (11))
                         (Prims.of_int (258)) (Prims.of_int (30)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.Prover.ShareGather.fst"
                         (Prims.of_int (259)) (Prims.of_int (2))
                         (Prims.of_int (268)) (Prims.of_int (36)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> mk_n_half nsplits p))
                (fun uu___ ->
                   (fun p' ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.ShareGather.fst"
                                    (Prims.of_int (259)) (Prims.of_int (8))
                                    (Prims.of_int (259)) (Prims.of_int (30)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.ShareGather.fst"
                                    (Prims.of_int (259)) (Prims.of_int (2))
                                    (Prims.of_int (268)) (Prims.of_int (36)))))
                           (Obj.magic (find_pts_to r p' e ctx))
                           (fun uu___ ->
                              (fun uu___ ->
                                 match uu___ with
                                 | FStar_Pervasives_Native.None ->
                                     Obj.magic
                                       (Obj.repr
                                          (if nsplits > Prims.int_zero
                                           then
                                             Obj.repr
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.ShareGather.fst"
                                                           (Prims.of_int (263))
                                                           (Prims.of_int (23))
                                                           (Prims.of_int (263))
                                                           (Prims.of_int (56)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.ShareGather.fst"
                                                           (Prims.of_int (264))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (265))
                                                           (Prims.of_int (43)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___1 ->
                                                        mk_pts_to
                                                          FStar_Range.range_0
                                                          ty r p' e))
                                                  (fun uu___1 ->
                                                     (fun other_half ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (77)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (43)))))
                                                             (Obj.magic
                                                                (find_least_split
                                                                   (nsplits -
                                                                    Prims.int_one)
                                                                   ty r p e
                                                                   ctx))
                                                             (fun uu___1 ->
                                                                (fun uu___1
                                                                   ->
                                                                   Obj.magic
                                                                    (op_let_Bang
                                                                    uu___26
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___1)
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    let uu___2
                                                                    =
                                                                    Obj.magic
                                                                    uu___2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (n, p'1,
                                                                    v, hs,
                                                                    ctx') ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (n, p'1,
                                                                    v,
                                                                    (other_half
                                                                    :: hs),
                                                                    ctx'))))
                                                                    uu___2)))
                                                                  uu___1)))
                                                       uu___1))
                                           else
                                             Obj.repr
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     FStar_Pervasives_Native.None))))
                                 | FStar_Pervasives_Native.Some (v, ctxt') ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                FStar_Pervasives_Native.Some
                                                  (nsplits, p', v, [], ctxt')))))
                                uu___))) uu___)
let (share : Pulse_Checker_Prover_Base.guided_prover_step) =
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
                         "Pulse.Checker.Prover.ShareGather.fst"
                         (Prims.of_int (276)) (Prims.of_int (14))
                         (Prims.of_int (276)) (Prims.of_int (29)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.Prover.ShareGather.fst"
                         (Prims.of_int (277)) (Prims.of_int (2))
                         (Prims.of_int (337)) (Prims.of_int (11)))))
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
                                    "Pulse.Checker.Prover.ShareGather.fst"
                                    (Prims.of_int (277)) (Prims.of_int (2))
                                    (Prims.of_int (283)) (Prims.of_int (4)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.ShareGather.fst"
                                    (Prims.of_int (285)) (Prims.of_int (2))
                                    (Prims.of_int (337)) (Prims.of_int (11)))))
                           (Obj.magic
                              (debug pst.Pulse_Checker_Prover_Base.pg
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.ShareGather.fst"
                                               (Prims.of_int (278))
                                               (Prims.of_int (31))
                                               (Prims.of_int (283))
                                               (Prims.of_int (3)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.ShareGather.fst"
                                               (Prims.of_int (278))
                                               (Prims.of_int (2))
                                               (Prims.of_int (283))
                                               (Prims.of_int (3)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.ShareGather.fst"
                                                     (Prims.of_int (279))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (279))
                                                     (Prims.of_int (46)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.ShareGather.fst"
                                                     (Prims.of_int (278))
                                                     (Prims.of_int (31))
                                                     (Prims.of_int (283))
                                                     (Prims.of_int (3)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.ShareGather.fst"
                                                           (Prims.of_int (279))
                                                           (Prims.of_int (42))
                                                           (Prims.of_int (279))
                                                           (Prims.of_int (46)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.ShareGather.fst"
                                                           (Prims.of_int (279))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (279))
                                                           (Prims.of_int (46)))))
                                                  (Obj.magic
                                                     (Pulse_PP.pp
                                                        Pulse_PP.printable_term
                                                        q))
                                                  (fun uu___2 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          FStar_Pprint.op_Hat_Slash_Hat
                                                            (Pulse_PP.text
                                                               "Trying share for resource:")
                                                            uu___2))))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.ShareGather.fst"
                                                                (Prims.of_int (278))
                                                                (Prims.of_int (31))
                                                                (Prims.of_int (283))
                                                                (Prims.of_int (3)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.ShareGather.fst"
                                                                (Prims.of_int (278))
                                                                (Prims.of_int (31))
                                                                (Prims.of_int (283))
                                                                (Prims.of_int (3)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (40)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (3)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (40)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (280))
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
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (281))
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
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (282))
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
                                               "Pulse.Checker.Prover.ShareGather.fst"
                                               (Prims.of_int (285))
                                               (Prims.of_int (8))
                                               (Prims.of_int (285))
                                               (Prims.of_int (32)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.ShareGather.fst"
                                               (Prims.of_int (285))
                                               (Prims.of_int (2))
                                               (Prims.of_int (337))
                                               (Prims.of_int (11)))))
                                      (Obj.magic (destruct_pts_to_half_n q))
                                      (fun uu___2 ->
                                         (fun uu___2 ->
                                            match uu___2 with
                                            | FStar_Pervasives_Native.None ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.ShareGather.fst"
                                                              (Prims.of_int (287))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (290))
                                                              (Prims.of_int (6)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.ShareGather.fst"
                                                              (Prims.of_int (291))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (291))
                                                              (Prims.of_int (8)))))
                                                     (Obj.magic
                                                        (debug
                                                           pst.Pulse_Checker_Prover_Base.pg
                                                           (fun uu___3 ->
                                                              Pulse_Typing_Env.warn_doc
                                                                pst.Pulse_Checker_Prover_Base.pg
                                                                (FStar_Pervasives_Native.Some
                                                                   (FStar_Reflection_V2_Builtins.range_of_term
                                                                    q))
                                                                [Pulse_PP.text
                                                                   "Goal is not a pts_to"])))
                                                     (fun uu___3 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             FStar_Pervasives_Native.None)))
                                            | FStar_Pervasives_Native.Some
                                                (nsplits, ty, r, p, e) ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.ShareGather.fst"
                                                              (Prims.of_int (296))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (296))
                                                              (Prims.of_int (60)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.ShareGather.fst"
                                                              (Prims.of_int (296))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (337))
                                                              (Prims.of_int (11)))))
                                                     (Obj.magic
                                                        (find_least_split
                                                           nsplits ty r p e
                                                           pst.Pulse_Checker_Prover_Base.remaining_ctxt))
                                                     (fun uu___3 ->
                                                        (fun uu___3 ->
                                                           match uu___3 with
                                                           | FStar_Pervasives_Native.None
                                                               ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (6)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (8)))))
                                                                    (
                                                                    Obj.magic
                                                                    (debug
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.warn_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (FStar_Pervasives_Native.Some
                                                                    q_rng)
                                                                    [
                                                                    Pulse_PP.text
                                                                    "NO SPLIT FOUND"])))
                                                                    (
                                                                    fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.None)))
                                                           | FStar_Pervasives_Native.Some
                                                               (n', p', v,
                                                                hs, ctxt')
                                                               ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (4)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (11)))))
                                                                    (
                                                                    Obj.magic
                                                                    (debug
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (92)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (92)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    Pulse_PP.printable_term
                                                                    q))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (92)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (92)))))
                                                                    (Obj.magic
                                                                    (Pulse_PP.pp
                                                                    (Pulse_PP.printable_tuple5
                                                                    Pulse_PP.printable_int
                                                                    Pulse_PP.printable_term
                                                                    Pulse_PP.printable_term
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term)
                                                                    (Pulse_PP.printable_list
                                                                    Pulse_PP.printable_term))
                                                                    (n', p',
                                                                    v, hs,
                                                                    ctxt')))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "in ctx")
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
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (Pulse_PP.text
                                                                    "Found half of: ")
                                                                    uu___5))))
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
                                                                    (Pulse_Typing_Env.warn_doc
                                                                    pst.Pulse_Checker_Prover_Base.pg
                                                                    (FStar_Pervasives_Native.Some
                                                                    q_rng)
                                                                    uu___5))
                                                                    uu___5))))
                                                                    (
                                                                    fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Checker_Prover_Base.pg
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.pg);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt
                                                                    =
                                                                    (FStar_List_Tot_Base.op_At
                                                                    hs ctxt');
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
                                                                    (FStar_List_Tot_Base.op_At
                                                                    hs ctxt'))
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Substs.ss_term
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    q
                                                                    pst.Pulse_Checker_Prover_Base.solved)
                                                                    pst.Pulse_Checker_Prover_Base.ss))
                                                                    pst.Pulse_Checker_Prover_Base.k
                                                                    (fun post
                                                                    ->
                                                                    fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___6
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
                                                          uu___3))) uu___2)))
                                uu___1))) uu___1)
let (gather : Pulse_Checker_Prover_Base.guided_prover_step) =
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
                         "Pulse.Checker.Prover.ShareGather.fst"
                         (Prims.of_int (345)) (Prims.of_int (14))
                         (Prims.of_int (345)) (Prims.of_int (29)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "Pulse.Checker.Prover.ShareGather.fst"
                         (Prims.of_int (346)) (Prims.of_int (2))
                         (Prims.of_int (434)) (Prims.of_int (17)))))
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
                                    "Pulse.Checker.Prover.ShareGather.fst"
                                    (Prims.of_int (346)) (Prims.of_int (2))
                                    (Prims.of_int (352)) (Prims.of_int (4)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Checker.Prover.ShareGather.fst"
                                    (Prims.of_int (354)) (Prims.of_int (2))
                                    (Prims.of_int (434)) (Prims.of_int (17)))))
                           (Obj.magic
                              (debug pst.Pulse_Checker_Prover_Base.pg
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.ShareGather.fst"
                                               (Prims.of_int (347))
                                               (Prims.of_int (31))
                                               (Prims.of_int (352))
                                               (Prims.of_int (3)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.ShareGather.fst"
                                               (Prims.of_int (347))
                                               (Prims.of_int (2))
                                               (Prims.of_int (352))
                                               (Prims.of_int (3)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.ShareGather.fst"
                                                     (Prims.of_int (348))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (348))
                                                     (Prims.of_int (47)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Checker.Prover.ShareGather.fst"
                                                     (Prims.of_int (347))
                                                     (Prims.of_int (31))
                                                     (Prims.of_int (352))
                                                     (Prims.of_int (3)))))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.ShareGather.fst"
                                                           (Prims.of_int (348))
                                                           (Prims.of_int (43))
                                                           (Prims.of_int (348))
                                                           (Prims.of_int (47)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Prover.ShareGather.fst"
                                                           (Prims.of_int (348))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (348))
                                                           (Prims.of_int (47)))))
                                                  (Obj.magic
                                                     (Pulse_PP.pp
                                                        Pulse_PP.printable_term
                                                        q))
                                                  (fun uu___2 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          FStar_Pprint.op_Hat_Slash_Hat
                                                            (Pulse_PP.text
                                                               "Trying gather for resource:")
                                                            uu___2))))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.ShareGather.fst"
                                                                (Prims.of_int (347))
                                                                (Prims.of_int (31))
                                                                (Prims.of_int (352))
                                                                (Prims.of_int (3)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Checker.Prover.ShareGather.fst"
                                                                (Prims.of_int (347))
                                                                (Prims.of_int (31))
                                                                (Prims.of_int (352))
                                                                (Prims.of_int (3)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (40)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (3)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (40)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (349))
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
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (350))
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
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (351))
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
                                               "Pulse.Checker.Prover.ShareGather.fst"
                                               (Prims.of_int (354))
                                               (Prims.of_int (8))
                                               (Prims.of_int (354))
                                               (Prims.of_int (25)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Checker.Prover.ShareGather.fst"
                                               (Prims.of_int (354))
                                               (Prims.of_int (2))
                                               (Prims.of_int (434))
                                               (Prims.of_int (17)))))
                                      (Obj.magic (destruct_pts_to q))
                                      (fun uu___2 ->
                                         (fun uu___2 ->
                                            match uu___2 with
                                            | FStar_Pervasives_Native.None ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.ShareGather.fst"
                                                              (Prims.of_int (356))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (359))
                                                              (Prims.of_int (6)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.ShareGather.fst"
                                                              (Prims.of_int (360))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (360))
                                                              (Prims.of_int (8)))))
                                                     (Obj.magic
                                                        (debug
                                                           pst.Pulse_Checker_Prover_Base.pg
                                                           (fun uu___3 ->
                                                              Pulse_Typing_Env.warn_doc
                                                                pst.Pulse_Checker_Prover_Base.pg
                                                                (FStar_Pervasives_Native.Some
                                                                   q_rng)
                                                                [Pulse_PP.text
                                                                   "Goal is not a pts_to"])))
                                                     (fun uu___3 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             FStar_Pervasives_Native.None)))
                                            | FStar_Pervasives_Native.Some
                                                (ty, r, p, e) ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.ShareGather.fst"
                                                              (Prims.of_int (365))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (365))
                                                              (Prims.of_int (44)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Checker.Prover.ShareGather.fst"
                                                              (Prims.of_int (365))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (434))
                                                              (Prims.of_int (17)))))
                                                     (Obj.magic
                                                        (find_pts_to r p e
                                                           pst.Pulse_Checker_Prover_Base.remaining_ctxt))
                                                     (fun uu___3 ->
                                                        (fun uu___3 ->
                                                           match uu___3 with
                                                           | FStar_Pervasives_Native.Some
                                                               (v, ctxt') ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Checker_Prover_Base.pg
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.pg);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt
                                                                    = ctxt';
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
                                                                    ctxt')
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Substs.ss_term
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    q
                                                                    pst.Pulse_Checker_Prover_Base.solved)
                                                                    pst.Pulse_Checker_Prover_Base.ss))
                                                                    pst.Pulse_Checker_Prover_Base.k
                                                                    (fun post
                                                                    ->
                                                                    fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___5
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
                                                                    })))
                                                           | FStar_Pervasives_Native.None
                                                               ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    (find_pts_to_half
                                                                    r p e
                                                                    pst.Pulse_Checker_Prover_Base.remaining_ctxt))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (v,
                                                                    ctxt') ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.ShareGather.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    (find_pts_to_half
                                                                    r p e
                                                                    ctxt'))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (v',
                                                                    ctxt'')
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Checker_Prover_Base.pg
                                                                    =
                                                                    (pst.Pulse_Checker_Prover_Base.pg);
                                                                    Pulse_Checker_Prover_Base.remaining_ctxt
                                                                    = ctxt'';
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
                                                                    ctxt'')
                                                                    preamble.Pulse_Checker_Prover_Base.frame)
                                                                    (Pulse_Checker_Prover_Substs.ss_term
                                                                    (Pulse_Checker_Prover_Base.op_Star
                                                                    q
                                                                    pst.Pulse_Checker_Prover_Base.solved)
                                                                    pst.Pulse_Checker_Prover_Base.ss))
                                                                    pst.Pulse_Checker_Prover_Base.k
                                                                    (fun post
                                                                    ->
                                                                    fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
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
                                                                    })))))
                                                                    uu___4))))
                                                          uu___3))) uu___2)))
                                uu___1))) uu___1)