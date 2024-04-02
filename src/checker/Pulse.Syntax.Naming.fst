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

module Pulse.Syntax.Naming
module RTB = FStar.Reflection.Typing.Builtins
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
open FStar.List.Tot
module E = Pulse.Elaborate.Pure
open Pulse.Syntax.Base
module U = Pulse.Syntax.Pure
module R2 = FStar.Reflection.V2
module RU = Pulse.RuntimeUtils
let r_subst_of_rt_subst_elt (x:subst_elt)
  : FStar.Reflection.V2.subst_elt
  = match x with
    | DT i t -> R2.DT i (E.elab_term t)
    | NT x t -> R2.NT (RT.var_as_namedv x) (E.elab_term t) 
    | ND x i -> R2.NM (RT.var_as_namedv x) i

let subst_host_term' (t:term) (ss:subst) =
  R2.subst_term (L.map r_subst_of_rt_subst_elt ss) t

let subst_host_term (t:term) (ss:subst) =
  let res0 = subst_host_term' t ss in
  assume (res0 == RT.subst_term t (rt_subst ss));
  res0

let close_open_inverse' (t:term) 
                            (x:var { ~(x `Set.mem` freevars t) } )
                            (i:index)
  : Lemma (ensures close_term' (open_term' t (U.term_of_no_name_var x) i) x i == t)
  = RT.close_open_inverse' i t x

let close_open_inverse_comp' (c:comp)
                             (x:var { ~(x `Set.mem` freevars_comp c) } )
                             (i:index)
  : Lemma (ensures close_comp' (open_comp' c (U.term_of_no_name_var x) i) x i == c)
  = match c with
    | C_Tot t ->
      close_open_inverse' t x i

    | C_ST s 
    | C_STGhost s -> 
      close_open_inverse' s.res x i;
      close_open_inverse' s.pre x i;      
      close_open_inverse' s.post x (i + 1)

    | C_STAtomic n _ s ->    
      close_open_inverse' n x i;    
      close_open_inverse' s.res x i;
      close_open_inverse' s.pre x i;      
      close_open_inverse' s.post x (i + 1)

let close_open_inverse_opt' (t:option term)
                            (x:var { ~(x `Set.mem` freevars_term_opt t) })
                            (i:index)
  : Lemma (ensures close_term_opt' (open_term_opt' t (U.term_of_no_name_var x) i) x i == t)
  = match t with
    | None -> ()
    | Some t -> close_open_inverse' t x i


let rec close_open_inverse_list' (t:list term)
                                 (x:var { ~(x `Set.mem` freevars_list t) })
                                 (i:index)
  : Lemma (ensures close_term_list' (open_term_list' t (U.term_of_no_name_var x) i) x i == t)
  = match t with
    | [] -> ()
    | hd::tl ->
      close_open_inverse' hd x i;
      close_open_inverse_list' tl x i


let rec close_open_inverse_pairs' (t:list (term * term))
                                  (x:var { ~(x `Set.mem` freevars_pairs t) })
                                  (i:index)
  : Lemma (ensures close_term_pairs' (open_term_pairs' t (U.term_of_no_name_var x) i) x i == t)
  = match t with
    | [] -> ()
    | (hd1, hd2)::tl ->
      close_open_inverse' hd1 x i;
      close_open_inverse' hd2 x i;
      close_open_inverse_pairs' tl x i

let close_open_inverse_proof_hint_type' (ht:proof_hint_type)
                                        (x:var { ~(x `Set.mem` freevars_proof_hint ht) })
                                        (i:index)
  : Lemma (ensures close_proof_hint' (open_proof_hint' ht (U.term_of_no_name_var x) i) x i == ht)
  = match ht with
    | ASSERT { p }
    | FOLD { p }
    | UNFOLD { p } -> close_open_inverse' p x i
    | RENAME { pairs; goal } ->
      close_open_inverse_pairs' pairs x i;
      close_open_inverse_opt' goal x i
    | REWRITE { t1; t2 } ->
      close_open_inverse' t1 x i;
      close_open_inverse' t2 x i
    | WILD
    | SHOW_PROOF_STATE _ -> ()

let open_ascription' (t:comp_ascription) (v:term) (i:index) : comp_ascription =
  subst_ascription t [DT i v]
let close_ascription' (t:comp_ascription) (x:var) (i:index) : comp_ascription =
  subst_ascription t [ND x i]

let close_open_inverse_ascription' (t:comp_ascription)
                                   (x:var { ~(x `Set.mem` freevars_ascription t) } )
                                   (i:index)
  : Lemma (ensures close_ascription' (open_ascription' t (U.term_of_no_name_var x) i) x i == t)
  = (match t.annotated with
     | None -> ()
     | Some c -> close_open_inverse_comp' c x i);
    (match t.elaborated with
     | None -> ()
     | Some c -> close_open_inverse_comp' c x i)
          
let rec close_open_inverse_st'  (t:st_term) 
                                (x:var { ~(x `Set.mem` freevars_st t) } )
                                (i:index)
  : Lemma (ensures close_st_term' (open_st_term' t (U.term_of_no_name_var x) i) x i == t)
          (decreases t)
  = match t.term with
    | Tm_Return { expected_type; term = t } ->
      close_open_inverse' expected_type x i;
      close_open_inverse' t x i

    | Tm_ElimExists { p } ->
      close_open_inverse' p x i    

    | Tm_Abs { b; ascription; body } ->
      close_open_inverse' b.binder_ty x i;
      close_open_inverse_st' body x (i + 1); 
      close_open_inverse_ascription' ascription x (i + 1)

    | Tm_Bind { binder; head; body } ->
      close_open_inverse' binder.binder_ty x i;
      close_open_inverse_st' head x i;
      close_open_inverse_st' body x (i + 1)

    | Tm_TotBind { binder; head; body } ->
      close_open_inverse' binder.binder_ty x i;
      close_open_inverse' head x i;
      close_open_inverse_st' body x (i + 1)

    | Tm_STApp { head; arg } ->
      close_open_inverse' head x i;
      close_open_inverse' arg x i
    
    | Tm_IntroExists { p; witnesses } ->
      close_open_inverse' p x i;
      close_open_inverse_list' witnesses x i
    
    | Tm_IntroPure { p }
    | Tm_ElimExists { p } ->
      close_open_inverse' p x i
      
    | Tm_While { invariant; condition; body } ->
      close_open_inverse' invariant x (i + 1);
      close_open_inverse_st' condition x i;
      close_open_inverse_st' body x i

    | Tm_If { b; then_; else_; post } ->
      close_open_inverse' b x i;    
      close_open_inverse_st' then_ x i;    
      close_open_inverse_st' else_ x i;
      close_open_inverse_opt' post x (i + 1)

    | Tm_Match { sc; returns_; brs } ->
      close_open_inverse' sc x i;
      close_open_inverse_opt' returns_ x i;
      admit(); // need map dec fusion
      ()

    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      close_open_inverse' pre1 x i;
      close_open_inverse_st' body1 x i;
      close_open_inverse' post1 x (i + 1);
      close_open_inverse' pre2 x i;
      close_open_inverse_st' body2 x i;
      close_open_inverse' post2 x (i + 1)

    | Tm_WithLocal { binder; initializer; body } ->
      close_open_inverse' binder.binder_ty x i; 
      close_open_inverse' initializer x i;
      close_open_inverse_st' body x (i + 1)

    | Tm_WithLocalArray { binder; initializer; length; body } ->
      close_open_inverse' binder.binder_ty x i; 
      close_open_inverse' initializer x i;
      close_open_inverse' length x i;
      close_open_inverse_st' body x (i + 1)

    | Tm_Rewrite { t1; t2 } ->
      close_open_inverse' t1 x i;
      close_open_inverse' t2 x i

    | Tm_Admit { typ; post } ->
      close_open_inverse' typ x i;
      close_open_inverse_opt' post x (i + 1)

    | Tm_Unreachable -> ()
    
    | Tm_ProofHintWithBinders { binders; hint_type; t} ->
      let n = L.length binders in
      close_open_inverse_proof_hint_type' hint_type x (i + n);
      close_open_inverse_st' t x (i + n)
      
    | Tm_WithInv { name; body; returns_inv } ->
      close_open_inverse' name x i;
      close_open_inverse_st' body x i;
      match returns_inv with
      | None -> ()
      | Some (b, r) ->
        close_open_inverse' b.binder_ty x i;
        close_open_inverse' r x (i + 1)
   
let close_open_inverse (t:term) (x:var { ~(x `Set.mem` freevars t) } )
  : Lemma (ensures close_term (open_term t x) x == t)
          (decreases t)
  = close_open_inverse' t x 0

let close_open_inverse_st (t:st_term) (x:var { ~(x `Set.mem` freevars_st t) } )
  : Lemma (ensures close_st_term (open_st_term t x) x == t)
          (decreases t)
  = close_open_inverse_st' t x 0

let open_with_gt_ln (e:term) (i:int) (t:term) (j:nat)
  : Lemma
      (requires ln' e i /\ i < j)
      (ensures open_term' e t j == e)
  = admit ()  // following what used to be in the case of Tm_FStar earlier

let open_with_gt_ln_st (s:st_comp) (i:int) (t:term) (j:nat)
  : Lemma (requires ln_st_comp s i /\ i < j)
          (ensures open_st_comp' s t j == s) =
  let {res; pre; post} = s in
  open_with_gt_ln res i t j;
  open_with_gt_ln pre i t j;
  open_with_gt_ln post (i + 1) t (j + 1)

let open_with_gt_ln_comp (c:comp) (i:int) (t:term) (j:nat)
  : Lemma (requires ln_c' c i /\ i < j)
          (ensures open_comp' c t j == c) =
  match c with
  | C_Tot t1 -> open_with_gt_ln t1 i t j
  | C_ST s
  | C_STGhost s -> open_with_gt_ln_st s i t j
  | C_STAtomic inames _ s ->
    open_with_gt_ln inames i t j;
    open_with_gt_ln_st s i t j

let close_with_non_freevar (e:term) (x:var) (i:nat)
  : Lemma
      (requires ~ (x `Set.mem` freevars e))
      (ensures close_term' e x i == e)
  = admit ()  // following what used to be in the case of Tm_FStar earlier

let close_with_non_freevar_st (s:st_comp) (x:var) (i:nat)
  : Lemma
    (requires ~ (x `Set.mem` freevars_st_comp s))
    (ensures close_st_comp' s x i == s) =
  let {res; pre; post} = s in
  close_with_non_freevar res x i;
  close_with_non_freevar pre x i;
  close_with_non_freevar post x (i + 1)

let close_comp_with_non_free_var (c:comp) (x:var) (i:nat)
  : Lemma
    (requires ~ (x `Set.mem` freevars_comp c))
    (ensures close_comp' c x i == c) =
  match c with
  | C_Tot t1 -> close_with_non_freevar t1 x i
  | C_ST s 
  | C_STGhost s ->
    close_with_non_freevar_st s x i
  | C_STAtomic inames _ s ->
    close_with_non_freevar inames x i;
    close_with_non_freevar_st s x i

let close_binders (bs:list binder) (xs:list var { L.length bs == L.length xs }) =
  let rec aux s out (bs:_) (xs:_{ L.length bs == L.length xs}) : Tot (list binder) (decreases bs) = 
    match bs, xs with
    | [], [] -> L.rev out
    | b::bs, x::xs ->
      let b = { b with binder_ty = subst_term b.binder_ty s } in
      let s = ND x 0 :: shift_subst s in
      aux s (b::out) bs xs
  in
  aux [] [] bs xs
