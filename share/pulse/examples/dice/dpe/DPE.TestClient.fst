(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module DPE.TestClient
#lang-pulse

open Pulse.Lib.Pervasives
open EngineTypes
open DPETypes
open DPE

module U8 = FStar.UInt8
module US = FStar.SizeT

assume val get_uds ()  // used only for testing a client
  : stt (larray U8.t (US.v uds_len))
        (requires emp)
        (ensures fun uds -> exists* uds_repr. pts_to uds uds_repr)

assume val get_engine_record ()  // used only for testing a client
  : stt record_t
        (requires emp)
        (ensures fun r ->
           pure (Engine_record? r) **
           (exists* repr. pure (Engine_repr? repr) ** record_perm r 1.0R repr))

assume val get_l0_record ()  // used only for testing a client
  : stt record_t
        (requires emp)
        (ensures fun r ->
           pure (L0_record? r) **
           (exists* repr. pure (L0_repr? repr) ** record_perm r 1.0R repr))


fn dpe_client ()
  requires emp
  ensures emp
{
  let sid_opt = DPE.open_session ();
  match sid_opt {
    Some sid -> {
      let uds = get_uds ();
      with uds_repr. assert (pts_to uds uds_repr);
      unfold (open_session_client_perm (Some sid));
      initialize_context sid _ uds;
      unfold (initialize_context_client_perm sid uds_repr);
      let r = get_engine_record ();
      with repr. assert (record_perm r 1.0R repr);
      with t. assert (sid_pts_to trace_ref sid t);
      let res = derive_child sid _ r;
      if res {
        unfold (derive_child_client_perm sid t repr true);
        let r = get_l0_record ();
        let hopt = derive_child sid _ r;
        drop_ (pts_to uds uds_repr);
        drop_ (derive_child_client_perm _ _ _ _);
      } else {
        drop_ (pts_to uds uds_repr);
        drop_ (derive_child_client_perm _ _ _ _)
      }
    }
    None -> {
      rewrite (open_session_client_perm None) as emp
    }
  }
}


[@@ expect_failure]

fn dpe_client_err ()
  requires emp
  ensures emp
{
  let sid_opt = DPE.open_session ();
  match sid_opt {
    Some sid -> {
      let uds = get_uds ();
      with uds_repr. assert (pts_to uds uds_repr);
      unfold (open_session_client_perm (Some sid));
      initialize_context sid _ uds;
      unfold (initialize_context_client_perm sid uds_repr);
      let r = get_l0_record ();
      let hopt = derive_child sid _ r;
      admit ()  //used only for testing a client
    }
    None -> {
      rewrite (open_session_client_perm None) as emp
    }
  }

}

