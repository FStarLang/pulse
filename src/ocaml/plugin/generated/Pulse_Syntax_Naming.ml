open Prims
let rec (pattern_shift_n : Pulse_Syntax_Base.pattern -> Prims.nat) =
  fun p ->
    match p with
    | Pulse_Syntax_Base.Pat_Constant uu___ -> Prims.int_zero
    | Pulse_Syntax_Base.Pat_Dot_Term uu___ -> Prims.int_zero
    | Pulse_Syntax_Base.Pat_Var (uu___, uu___1) -> Prims.int_one
    | Pulse_Syntax_Base.Pat_Cons (fv, l) -> pattern_args_shift_n l
and (pattern_args_shift_n :
  (Pulse_Syntax_Base.pattern * Prims.bool) Prims.list -> Prims.nat) =
  fun ps ->
    match ps with
    | [] -> Prims.int_zero
    | (p, uu___)::tl -> (pattern_shift_n p) + (pattern_args_shift_n tl)
type subst_elt = FStar_Reflection_Typing.subst_elt
let (shift_subst_elt :
  Prims.nat ->
    FStar_Reflection_Typing.subst_elt -> FStar_Reflection_Typing.subst_elt)
  = FStar_Reflection_Typing.shift_subst_elt
type subst = FStar_Reflection_Typing.subst
let (shift_subst_n :
  Prims.nat ->
    FStar_Reflection_Typing.subst_elt Prims.list ->
      FStar_Reflection_Typing.subst_elt Prims.list)
  = fun n -> FStar_Reflection_Typing.shift_subst_n n
let (shift_subst :
  FStar_Reflection_Typing.subst_elt Prims.list ->
    FStar_Reflection_Typing.subst_elt Prims.list)
  = FStar_Reflection_Typing.shift_subst
let (r_subst_of_rt_subst_elt : subst_elt -> FStar_Syntax_Syntax.subst_elt) =
  fun x ->
    match x with
    | FStar_Reflection_Typing.DT (i, t) ->
        (match FStar_Reflection_V2_Builtins.inspect_ln t with
         | FStar_Reflection_V2_Data.Tv_Var n -> FStar_Syntax_Syntax.DB (i, n)
         | uu___ -> FStar_Syntax_Syntax.DT (i, t))
    | FStar_Reflection_Typing.NT (x1, t) ->
        FStar_Syntax_Syntax.NT
          ((FStar_Reflection_Typing.var_as_namedv x1), t)
    | FStar_Reflection_Typing.ND (x1, i) ->
        FStar_Syntax_Syntax.NM
          ((FStar_Reflection_Typing.var_as_namedv x1), i)
let (subst_host_term' :
  Pulse_Syntax_Base.term -> subst -> FStar_Reflection_Types.term) =
  fun t ->
    fun ss ->
      FStar_Reflection_V2_Builtins.subst_term
        (FStar_List_Tot_Base.map r_subst_of_rt_subst_elt ss) t
let (subst_host_term :
  Pulse_Syntax_Base.term -> subst -> Pulse_Syntax_Base.term) =
  fun t -> fun ss -> let res0 = subst_host_term' t ss in res0
let (subst_term : Pulse_Syntax_Base.term -> subst -> Pulse_Syntax_Base.term)
  = fun t -> fun ss -> subst_host_term t ss
let (open_term' :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.term)
  =
  fun t -> fun v -> fun i -> subst_term t [FStar_Reflection_Typing.DT (i, v)]
let (subst_st_comp :
  Pulse_Syntax_Base.st_comp -> subst -> Pulse_Syntax_Base.st_comp) =
  fun s ->
    fun ss ->
      {
        Pulse_Syntax_Base.u = (s.Pulse_Syntax_Base.u);
        Pulse_Syntax_Base.res = (subst_term s.Pulse_Syntax_Base.res ss);
        Pulse_Syntax_Base.pre = (subst_term s.Pulse_Syntax_Base.pre ss);
        Pulse_Syntax_Base.post =
          (subst_term s.Pulse_Syntax_Base.post (shift_subst ss))
      }
let (open_st_comp' :
  Pulse_Syntax_Base.st_comp ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.st_comp)
  =
  fun s ->
    fun v -> fun i -> subst_st_comp s [FStar_Reflection_Typing.DT (i, v)]
let (subst_comp : Pulse_Syntax_Base.comp -> subst -> Pulse_Syntax_Base.comp)
  =
  fun c ->
    fun ss ->
      match c with
      | Pulse_Syntax_Base.C_Tot t ->
          Pulse_Syntax_Base.C_Tot (subst_term t ss)
      | Pulse_Syntax_Base.C_ST s ->
          Pulse_Syntax_Base.C_ST (subst_st_comp s ss)
      | Pulse_Syntax_Base.C_STAtomic (inames, obs, s) ->
          Pulse_Syntax_Base.C_STAtomic
            ((subst_term inames ss), obs, (subst_st_comp s ss))
      | Pulse_Syntax_Base.C_STGhost (inames, s) ->
          Pulse_Syntax_Base.C_STGhost
            ((subst_term inames ss), (subst_st_comp s ss))
let (open_comp' :
  Pulse_Syntax_Base.comp ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.comp)
  =
  fun c -> fun v -> fun i -> subst_comp c [FStar_Reflection_Typing.DT (i, v)]
let (subst_term_opt :
  Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
    subst -> Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun t ->
    fun ss ->
      match t with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some t1 ->
          FStar_Pervasives_Native.Some (subst_term t1 ss)
let (open_term_opt' :
  Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index ->
        Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun t ->
    fun v -> fun i -> subst_term_opt t [FStar_Reflection_Typing.DT (i, v)]
let rec (subst_term_list :
  Pulse_Syntax_Base.term Prims.list ->
    subst -> Pulse_Syntax_Base.term Prims.list)
  =
  fun t ->
    fun ss ->
      match t with
      | [] -> []
      | hd::tl -> (subst_term hd ss) :: (subst_term_list tl ss)
let (open_term_list' :
  Pulse_Syntax_Base.term Prims.list ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.term Prims.list)
  =
  fun t ->
    fun v -> fun i -> subst_term_list t [FStar_Reflection_Typing.DT (i, v)]
let (subst_binder :
  Pulse_Syntax_Base.binder -> subst -> Pulse_Syntax_Base.binder) =
  fun b ->
    fun ss ->
      {
        Pulse_Syntax_Base.binder_ty =
          (subst_term b.Pulse_Syntax_Base.binder_ty ss);
        Pulse_Syntax_Base.binder_ppname = (b.Pulse_Syntax_Base.binder_ppname);
        Pulse_Syntax_Base.binder_attrs = (b.Pulse_Syntax_Base.binder_attrs)
      }
let (open_binder :
  Pulse_Syntax_Base.binder ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.binder)
  =
  fun b ->
    fun v ->
      fun i ->
        {
          Pulse_Syntax_Base.binder_ty =
            (open_term' b.Pulse_Syntax_Base.binder_ty v i);
          Pulse_Syntax_Base.binder_ppname =
            (b.Pulse_Syntax_Base.binder_ppname);
          Pulse_Syntax_Base.binder_attrs = (b.Pulse_Syntax_Base.binder_attrs)
        }
let rec (subst_term_pairs :
  (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term) Prims.list ->
    subst -> (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term) Prims.list)
  =
  fun t ->
    fun ss ->
      match t with
      | [] -> []
      | (t1, t2)::tl -> ((subst_term t1 ss), (subst_term t2 ss)) ::
          (subst_term_pairs tl ss)
let (subst_proof_hint :
  Pulse_Syntax_Base.proof_hint_type ->
    subst -> Pulse_Syntax_Base.proof_hint_type)
  =
  fun ht ->
    fun ss ->
      match ht with
      | Pulse_Syntax_Base.ASSERT { Pulse_Syntax_Base.p = p;_} ->
          Pulse_Syntax_Base.ASSERT
            { Pulse_Syntax_Base.p = (subst_term p ss) }
      | Pulse_Syntax_Base.UNFOLD
          { Pulse_Syntax_Base.names1 = names; Pulse_Syntax_Base.p2 = p;_} ->
          Pulse_Syntax_Base.UNFOLD
            {
              Pulse_Syntax_Base.names1 = names;
              Pulse_Syntax_Base.p2 = (subst_term p ss)
            }
      | Pulse_Syntax_Base.FOLD
          { Pulse_Syntax_Base.names = names; Pulse_Syntax_Base.p1 = p;_} ->
          Pulse_Syntax_Base.FOLD
            {
              Pulse_Syntax_Base.names = names;
              Pulse_Syntax_Base.p1 = (subst_term p ss)
            }
      | Pulse_Syntax_Base.RENAME
          { Pulse_Syntax_Base.pairs = pairs; Pulse_Syntax_Base.goal = goal;
            Pulse_Syntax_Base.tac_opt = tac_opt;_}
          ->
          Pulse_Syntax_Base.RENAME
            {
              Pulse_Syntax_Base.pairs = (subst_term_pairs pairs ss);
              Pulse_Syntax_Base.goal = (subst_term_opt goal ss);
              Pulse_Syntax_Base.tac_opt = (subst_term_opt tac_opt ss)
            }
      | Pulse_Syntax_Base.REWRITE
          { Pulse_Syntax_Base.t1 = t1; Pulse_Syntax_Base.t2 = t2;
            Pulse_Syntax_Base.tac_opt1 = tac_opt;_}
          ->
          Pulse_Syntax_Base.REWRITE
            {
              Pulse_Syntax_Base.t1 = (subst_term t1 ss);
              Pulse_Syntax_Base.t2 = (subst_term t2 ss);
              Pulse_Syntax_Base.tac_opt1 = (subst_term_opt tac_opt ss)
            }
      | Pulse_Syntax_Base.WILD -> ht
      | Pulse_Syntax_Base.SHOW_PROOF_STATE uu___ -> ht
let (open_term_pairs' :
  (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term) Prims.list ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index ->
        (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term) Prims.list)
  =
  fun t ->
    fun v -> fun i -> subst_term_pairs t [FStar_Reflection_Typing.DT (i, v)]
let (close_term_pairs' :
  (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term) Prims.list ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index ->
        (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term) Prims.list)
  =
  fun t ->
    fun x -> fun i -> subst_term_pairs t [FStar_Reflection_Typing.ND (x, i)]
let (open_proof_hint' :
  Pulse_Syntax_Base.proof_hint_type ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.proof_hint_type)
  =
  fun ht ->
    fun v -> fun i -> subst_proof_hint ht [FStar_Reflection_Typing.DT (i, v)]
let (close_proof_hint' :
  Pulse_Syntax_Base.proof_hint_type ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.proof_hint_type)
  =
  fun ht ->
    fun x -> fun i -> subst_proof_hint ht [FStar_Reflection_Typing.ND (x, i)]
let map2_opt :
  'a 'b 'c .
    ('a -> 'b -> 'c) ->
      'a FStar_Pervasives_Native.option ->
        'b -> 'c FStar_Pervasives_Native.option
  =
  fun f ->
    fun x ->
      fun y ->
        match x with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some x1 ->
            FStar_Pervasives_Native.Some (f x1 y)
let (subst_ascription :
  Pulse_Syntax_Base.comp_ascription ->
    subst -> Pulse_Syntax_Base.comp_ascription)
  =
  fun c ->
    fun ss ->
      {
        Pulse_Syntax_Base.annotated =
          (map2_opt subst_comp c.Pulse_Syntax_Base.annotated ss);
        Pulse_Syntax_Base.elaborated =
          (map2_opt subst_comp c.Pulse_Syntax_Base.elaborated ss)
      }
let (open_term_nv :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.nvar -> Pulse_Syntax_Base.term)
  =
  fun t ->
    fun nv -> open_term' t (Pulse_Syntax_Pure.term_of_nvar nv) Prims.int_zero
let (open_comp_with :
  Pulse_Syntax_Base.comp -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp)
  = fun c -> fun x -> open_comp' c x Prims.int_zero
let (open_comp_nv :
  Pulse_Syntax_Base.comp -> Pulse_Syntax_Base.nvar -> Pulse_Syntax_Base.comp)
  =
  fun c ->
    fun nv -> open_comp' c (Pulse_Syntax_Pure.term_of_nvar nv) Prims.int_zero
let (close_term' :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.term)
  =
  fun t -> fun v -> fun i -> subst_term t [FStar_Reflection_Typing.ND (v, i)]
let (close_st_comp' :
  Pulse_Syntax_Base.st_comp ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.st_comp)
  =
  fun s ->
    fun v -> fun i -> subst_st_comp s [FStar_Reflection_Typing.ND (v, i)]
let (close_comp' :
  Pulse_Syntax_Base.comp ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.comp)
  =
  fun c -> fun v -> fun i -> subst_comp c [FStar_Reflection_Typing.ND (v, i)]
let (close_term_opt' :
  Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index ->
        Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun t ->
    fun v -> fun i -> subst_term_opt t [FStar_Reflection_Typing.ND (v, i)]
let (close_term_list' :
  Pulse_Syntax_Base.term Prims.list ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.term Prims.list)
  =
  fun t ->
    fun v -> fun i -> subst_term_list t [FStar_Reflection_Typing.ND (v, i)]
let (close_binder :
  Pulse_Syntax_Base.binder ->
    FStar_Reflection_V2_Data.var -> Prims.nat -> Pulse_Syntax_Base.binder)
  =
  fun b ->
    fun v -> fun i -> subst_binder b [FStar_Reflection_Typing.ND (v, i)]
let (close_term :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term)
  = fun t -> fun v -> close_term' t v Prims.int_zero
let (close_comp :
  Pulse_Syntax_Base.comp -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.comp)
  = fun t -> fun v -> close_comp' t v Prims.int_zero
let close_n :
  'a .
    'a ->
      ('a -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.index -> 'a) ->
        Pulse_Syntax_Base.var Prims.list -> 'a
  =
  fun x ->
    fun f ->
      fun vs ->
        let rec aux i vs1 x1 =
          match vs1 with
          | [] -> x1
          | v::vs2 -> aux (i + Prims.int_one) vs2 (f x1 v i) in
        aux Prims.int_zero (FStar_List_Tot_Base.rev vs) x
let (close_term_n :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.var Prims.list -> Pulse_Syntax_Base.term)
  = fun t -> fun vs -> close_n t close_term' vs
let (close_comp_n :
  Pulse_Syntax_Base.comp ->
    Pulse_Syntax_Base.var Prims.list -> Pulse_Syntax_Base.comp)
  = fun c -> fun vs -> close_n c close_comp' vs
let (open_ascription' :
  Pulse_Syntax_Base.comp_ascription ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.comp_ascription)
  =
  fun t ->
    fun v -> fun i -> subst_ascription t [FStar_Reflection_Typing.DT (i, v)]
let (close_ascription' :
  Pulse_Syntax_Base.comp_ascription ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.index -> Pulse_Syntax_Base.comp_ascription)
  =
  fun t ->
    fun x -> fun i -> subst_ascription t [FStar_Reflection_Typing.ND (x, i)]
let (close_binders :
  Pulse_Syntax_Base.binder Prims.list ->
    Pulse_Syntax_Base.var Prims.list -> Pulse_Syntax_Base.binder Prims.list)
  =
  fun bs ->
    fun xs ->
      let rec aux s out bs1 xs1 =
        match (bs1, xs1) with
        | ([], []) -> FStar_List_Tot_Base.rev out
        | (b::bs2, x::xs2) ->
            let b1 =
              {
                Pulse_Syntax_Base.binder_ty =
                  (subst_term b.Pulse_Syntax_Base.binder_ty s);
                Pulse_Syntax_Base.binder_ppname =
                  (b.Pulse_Syntax_Base.binder_ppname);
                Pulse_Syntax_Base.binder_attrs =
                  (b.Pulse_Syntax_Base.binder_attrs)
              } in
            let s1 = (FStar_Reflection_Typing.ND (x, Prims.int_zero)) ::
              (shift_subst s) in
            aux s1 (b1 :: out) bs2 xs2 in
      aux [] [] bs xs