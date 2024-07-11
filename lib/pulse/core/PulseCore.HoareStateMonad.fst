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

module PulseCore.HoareStateMonad


let return (#s:Type u#s)
           (#a:Type u#a)
           (x:a)
: st a (fun _ -> True) (fun s0 v s1 -> x == v /\ s0 == s1)           
= fun s -> x, s

let bind
      (#s:Type u#s)
      (#a:Type u#a)
      (#b:Type u#b)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:a -> req_t s)
      (#ens_g:a -> ens_t s b)
      (f:st a req_f ens_f)
      (g:(x:a -> st b (req_g x) (ens_g x)))
: st b
  (fun s0 -> req_f s0 /\ (forall x s1. ens_f s0 x s1 ==> (req_g x) s1))
  (fun s0 r s2 -> req_f s0 /\ (exists x s1. ens_f s0 x s1 /\ (req_g x) s1 /\ (ens_g x) s1 r s2))
= fun s0 -> let x, s1 = f s0 in g x s1

let weaken
      (#s:Type u#s)
      (#a:Type u#a)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:req_t s)
      (#ens_g:ens_t s a)
      (f:st a req_f ens_f)
    : Pure (st a req_g ens_g)
      (requires
        (forall s. req_g s ==> req_f s) /\
        (forall s0 x s1. (req_g s0 /\ ens_f s0 x s1) ==> ens_g s0 x s1))
      (ensures fun _ -> True)
= fun s -> f s

let get (#s:Type u#s) (_:unit)
: st s (fun _ -> True) (fun s0 x s1 -> s0 == s1 /\ x == s0)
= fun s -> s, s

let put (#s:Type u#s) (v:s)
: st unit (fun s0 -> True) (fun s0 x s1 -> v == s1)
= fun _ -> (), v
