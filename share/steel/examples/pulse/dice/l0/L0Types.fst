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

module L0Types
open Pulse.Lib.Pervasives

let x509_version_t : Type0 = admit()

let x509_serialNumber_t : Type0 = admit()

let deviceIDCRI_t : Type0 = admit()

let deviceIDCSR_t (len: US.t) : Type0 = admit()

let aliasKeyTBS_t : Type0 = admit()

let aliasKeyCRT_t (len: US.t) : Type0 = admit()