(*
   Copyright REDACTED

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

module Async

open Pulse.Lib.Pervasives

val asynch (a:Type0) (post : a -> slprop) : Type0

val async_joinable
  (#a : Type0)
  (#post : a -> slprop)
  (h : asynch a post)
  : slprop

val async
  (#a : Type0)
  (#pre : slprop)
  (#post : (a -> slprop))
  (f : (unit -> stt a pre post))
  : stt (asynch a post) pre (fun h -> async_joinable h)

val await
  (#a : Type0)
  (#post : (a -> slprop))
  (h : asynch a post)
  : stt a (async_joinable h) (fun x -> post x)

val map
  (#a : Type0)
  (#b : Type0)
  (#post1 : (a -> slprop))
  (#post2 : (b -> slprop))
  (f : (x:a -> stt b (post1 x) post2))
  (h : asynch a post1)
  : stt (asynch b post2) (async_joinable h) (fun x -> async_joinable x)
