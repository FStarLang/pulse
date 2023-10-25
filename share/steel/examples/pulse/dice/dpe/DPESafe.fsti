module DPESafe
open DPE
open Pulse.Lib.Pervasives
open EngineTypes
open DPETypes
open EngineCore
open DPEStateful
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module A = Pulse.Lib.Array
val snapshot (s:sid_t) (s:state_t) : vprop

val snapshot_dup (#o:_) (s:sid_t) (st:state_t)
  : stt_ghost unit o
    (requires snapshot s st)
    (ensures fun _ -> snapshot s st ** snapshot s st)

let next (s0 s1:state_t) =
    match s0, s1 with
    | SessionStart _, EngineInitialized _ _ -> True
    | EngineInitialized _ uds, L0 _ uds' cdi r -> uds==uds'
    | L0 _ _ cdi _, L1 _ l1_ctxt -> cdi == l1_ctxt.cdi
    (* destroy context preserving history *)
    | EngineInitialized _ _, SessionStart (Some h)
    | L0 _ _ _ _, SessionStart (Some h)
    | L1 _ _, SessionStart (Some h) -> 
      h == s0
    | _ -> False
let leads_to x y : prop = 
    squash (FStar.ReflexiveTransitiveClosure.closure next x y)

val snapshots_related (#o:_) (s:sid_t) (st0 st1:state_t)
  : stt_ghost unit o
    (requires
        snapshot s st0 **
        snapshot s st1)
    (ensures fun _ ->
        pure (st0 `leads_to` st1 \/ st1 `leads_to` st0))
        
val get_profile (_:unit)
  : stt profile_descriptor_t 
    (requires emp)
    (ensures fun _ -> emp)

val open_session (_:unit)
  : stt (option sid_t)
    (requires emp)
    (function
      | None -> emp
      | Some sid -> snapshot sid (SessionStart None))

val initialize_context (sid:sid_t)
                       (uds:A.larray U8.t (SZ.v uds_len))
                       (#rd:perm)
                       (#uds_bytes:erased bytes)
  : stt (option ctxt_hndl_t) 
    (requires
      A.pts_to uds #rd uds_bytes)
    (ensures fun hdl ->
      A.pts_to uds #rd uds_bytes **
      (match hdl with
       | None -> emp
       | Some hdl -> 
         snapshot sid (EngineInitialized hdl uds_bytes)))

val derive_child (sid:sid_t)
                 (ctxt_hndl:ctxt_hndl_t)
                 (record:record_t)
                 (#repr:erased repr_t)
                 (#rd:perm)
                 (#s:state_t)
  : stt (option ctxt_hndl_t) 
    (requires
      record_perm record rd repr)
    (ensures fun hdl ->
      record_perm record rd repr **
      (match hdl with
       | None -> emp
       | Some hdl ->
         exists_ (fun s' -> snapshot sid s')))

val destroy_context (sid:sid_t)
                    (ctxt_hndl:ctxt_hndl_t)
  : stt bool
    (requires emp)
    (ensures fun b ->
      if b
      then exists_ (fun h -> snapshot sid (SessionStart (Some h)))
      else emp)
