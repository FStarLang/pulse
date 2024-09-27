open Prims
let (check_equiv_now :
  FStar_Reflection_Types.env ->
    FStar_Tactics_NamedView.term ->
      FStar_Tactics_NamedView.term ->
        ((unit FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tcenv ->
    fun t0 ->
      fun t1 ->
        Pulse_RuntimeUtils.disable_admit_smt_queries
          (fun uu___ ->
             FStar_Tactics_V2_Derived.with_policy
               FStar_Tactics_Types.ForceSMT
               (fun uu___1 ->
                  FStar_Tactics_V2_Derived.check_equiv tcenv t0 t1))
let (check_equiv_now_nosmt :
  FStar_Reflection_Types.env ->
    FStar_Tactics_NamedView.term ->
      FStar_Tactics_NamedView.term ->
        ((unit FStar_Pervasives_Native.option * FStar_Issue.issue Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tcenv ->
    fun t0 ->
      fun t1 ->
        Pulse_RuntimeUtils.disable_admit_smt_queries
          (fun uu___ ->
             FStar_Tactics_V2_Derived.check_equiv_nosmt tcenv t0 t1)
let (universe_of_now :
  FStar_Reflection_Types.env ->
    FStar_Tactics_NamedView.term ->
      ((FStar_Tactics_NamedView.universe FStar_Pervasives_Native.option *
         FStar_Issue.issue Prims.list),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun e ->
      FStar_Tactics_V2_Derived.with_policy FStar_Tactics_Types.ForceSMT
        (fun uu___ -> FStar_Tactics_V2_Builtins.universe_of g e)