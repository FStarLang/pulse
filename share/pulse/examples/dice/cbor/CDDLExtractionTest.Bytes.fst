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

module CDDLExtractionTest.Bytes
open Pulse.Lib.Pervasives
open CBOR.Spec
open CDDL.Spec
open CBOR.Pulse
open CDDL.Pulse

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_mytype = impl_bytes ()

```pulse
fn test
    (c: cbor)
    (v: Ghost.erased raw_data_item)
    #full_perm
requires
    raw_data_item_match full_perm c v
ensures
    raw_data_item_match full_perm c v
{
    // let unused = eval_impl_typ impl_mytype c; // this also typechecks, but does not extract either
    let unused = impl_bytes () c;
    ()
}
```
