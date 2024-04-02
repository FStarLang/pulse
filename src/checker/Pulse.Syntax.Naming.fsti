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

open FStar.List.Tot
open Pulse.Syntax.Base
open Pulse.Common

module L = FStar.List.Tot

module R = FStar.Reflection
module RTB = FStar.Reflection.Typing.Builtins
module RT = FStar.Reflection.Typing
module RU = Pulse.RuntimeUtils
module U = Pulse.Syntax.Pure
module E = Pulse.Elaborate.Pure

let freevars (t:term) : Set.set var = RT.freevars t

let freevars_st_comp (s:st_comp) : Set.set var =
  freevars s.res `Set.union`
  freevars s.pre `Set.union`
  freevars s.post

let freevars_comp (c:comp) : Tot (Set.set var) (decreases c) =
  match c with
  | C_Tot t -> freevars t
  | C_ST s
  | C_STGhost s -> freevars_st_comp s
  | C_STAtomic inames _ s ->
    freevars inames `Set.union` freevars_st_comp s

let freevars_opt (f: 'a -> Set.set var) (x:option 'a) : Set.set var =
  match x with
  | None -> Set.empty
  | Some x -> f x

let freevars_term_opt (t:option term) : Set.set var =
  freevars_opt freevars t

let rec freevars_list (t:list term) : Set.set var =
  match t with
  | [] -> Set.empty
  | hd::tl -> freevars hd `Set.union` freevars_list tl

let rec freevars_pairs (pairs:list (term & term)) : Set.set var =
  match pairs with
  | [] -> Set.empty
  | (t1, t2)::tl -> Set.union (freevars t1) (freevars t2) `Set.union` freevars_pairs tl

let freevars_proof_hint (ht:proof_hint_type) : Set.set var = 
  match ht with
  | ASSERT { p }
  | FOLD { p }
  | UNFOLD { p } -> freevars p
  | RENAME { pairs; goal } ->
    Set.union (freevars_pairs pairs) (freevars_term_opt goal)
  | REWRITE { t1; t2 } ->
    Set.union (freevars t1) (freevars t2)
  | WILD
  | SHOW_PROOF_STATE _ -> Set.empty

let freevars_ascription (c:comp_ascription) 
  : Set.set var
  = Set.union (freevars_opt freevars_comp c.elaborated)
              (freevars_opt freevars_comp c.annotated)

let rec freevars_st (t:st_term)
  : Set.set var
  = match t.term with
    | Tm_Return { expected_type; term } ->
      Set.union (freevars expected_type) (freevars term)
    | Tm_Abs { b; ascription; body } ->
      Set.union (freevars b.binder_ty) 
                (Set.union (freevars_st body)
                           (freevars_ascription ascription))
    | Tm_STApp { head; arg } ->
      Set.union (freevars head) (freevars arg)
    | Tm_Bind { binder; head; body } ->
      Set.union 
        (Set.union (freevars binder.binder_ty) 
                   (freevars_st head))
        (freevars_st body)
    | Tm_TotBind { binder; head; body } ->
      Set.union
        (Set.union (freevars binder.binder_ty)
                   (freevars head))
        (freevars_st body)
    | Tm_If { b; then_; else_; post } ->
      Set.union (Set.union (freevars b) (freevars_st then_))
                (Set.union (freevars_st else_) (freevars_term_opt post))

    | Tm_Match { sc ; returns_; brs } ->
      let (@@) = Set.union in
      freevars sc
        @@ freevars_term_opt returns_
        @@ freevars_branches brs

    | Tm_IntroPure { p }
    | Tm_ElimExists { p } ->
      freevars p
    | Tm_IntroExists { p; witnesses } ->
      Set.union (freevars p) (freevars_list witnesses)
    | Tm_While { invariant; condition; body } ->
      Set.union (freevars invariant)
                (Set.union (freevars_st condition)
                           (freevars_st body))
    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      Set.union
        (Set.union (freevars pre1)
                   (Set.union (freevars_st body1)
                              (freevars post1)))
        (Set.union (freevars pre2)
                   (Set.union (freevars_st body2)
                              (freevars post2)))

    | Tm_WithLocal { binder; initializer; body } ->
      Set.union (freevars binder.binder_ty)
                (Set.union (freevars initializer)
                           (freevars_st body))

    | Tm_WithLocalArray { binder; initializer; length; body } ->
      Set.union (freevars binder.binder_ty)
                (Set.union (freevars initializer)
                           (Set.union (freevars length)
                                      (freevars_st body)))

    | Tm_Rewrite { t1; t2 } ->
      Set.union (freevars t1) (freevars t2)

    | Tm_Admit { typ; post } ->
      Set.union (freevars typ)
                (freevars_term_opt post)

    | Tm_Unreachable ->
      Set.empty

    | Tm_ProofHintWithBinders { binders; hint_type; t } ->
      Set.union (freevars_proof_hint hint_type) (freevars_st t)

    | Tm_WithInv { name; body; returns_inv } ->
      Set.union (Set.union (freevars name) (freevars_st body))
                (freevars_opt 
                  (fun (b, r) ->
                    (Set.union (freevars b.binder_ty) 
                               (freevars r)))
                  returns_inv)

and freevars_branches (t:list (pattern & st_term)) : Set.set var =
  match t with
  | [] -> Set.empty
  | (_, b)::tl -> freevars_st b `Set.union` freevars_branches tl


let ln' (t:term) (i:int) : bool = RT.ln' t i

let ln_st_comp (s:st_comp) (i:int) : bool =
  ln' s.res i &&
  ln' s.pre i &&
  ln' s.post (i + 1) (* post has 1 impliict abstraction *)


let ln_c' (c:comp) (i:int)
  : bool
  = match c with
    | C_Tot t -> ln' t i
    | C_ST s
    | C_STGhost s -> ln_st_comp s i
    | C_STAtomic inames _ s ->
      ln' inames i &&
      ln_st_comp s i

let ln_opt' (f: ('a -> int -> bool)) (t:option 'a) (i:int) : bool =
  match t with
  | None -> true
  | Some t -> f t i

let rec ln_list' (t:list term) (i:int) : bool =
  match t with
  | [] -> true
  | hd::tl -> ln' hd i && ln_list' tl i

let rec ln_terms' (t:list (term & term)) (i:int) : bool =
  match t with
  | [] -> true
  | (t1, t2)::tl -> ln' t1 i && ln' t2 i && ln_terms' tl i

let ln_proof_hint' (ht:proof_hint_type) (i:int) : bool =
  match ht with
  | ASSERT { p }
  | UNFOLD { p }
  | FOLD   { p } -> ln' p i
  | RENAME { pairs; goal } ->
    ln_terms' pairs i &&
    ln_opt' ln' goal i
  | REWRITE { t1; t2 } ->
    ln' t1 i &&
    ln' t2 i
  | WILD
  | SHOW_PROOF_STATE _ -> true

let rec pattern_shift_n (p:pattern)
  : Tot nat
  = match p with
    | Pat_Constant _ 
    | Pat_Dot_Term _ -> 
      0
    | Pat_Var _ _ ->
      1
    | Pat_Cons fv l ->
      pattern_args_shift_n l
and pattern_args_shift_n (ps:list (pattern & bool))
  : Tot nat
  = match ps with
    | [] -> 0
    | (p, _)::tl ->
      pattern_shift_n p + pattern_args_shift_n tl

let rec ln_pattern' (p : pattern) (i:int)
  : Tot bool (decreases p)
  = match p with
    | Pat_Constant _ 
    | Pat_Var _ _ 
    | Pat_Dot_Term None ->
      true
    | Pat_Dot_Term (Some e) ->
      ln' e i
    | Pat_Cons fv l ->
      ln_pattern_args' l i
 
and ln_pattern_args' (p:list (pattern & bool)) (i:int)
  : Tot bool (decreases p)
  = match p with
    | [] ->
      true
    | (p, _)::tl ->
      ln_pattern' p i &&
      ln_pattern_args' tl (i + pattern_shift_n p)

let ln_ascription' (c:comp_ascription) (i:int)
  : bool
  = ln_opt' ln_c' c.elaborated i &&
    ln_opt' ln_c' c.annotated i

let rec ln_st' (t:st_term) (i:int)
  : Tot bool (decreases t)
  = match t.term with
    | Tm_Return { expected_type; term } ->
      ln' expected_type i &&
      ln' term i
      
    | Tm_Abs { b; ascription; body } ->
      ln' b.binder_ty i &&
      ln_st' body (i + 1) &&
      ln_ascription' ascription (i + 1)

    | Tm_STApp { head; arg } ->
      ln' head i &&
      ln' arg i

    | Tm_Bind { binder; head; body } ->
      ln' binder.binder_ty i &&
      ln_st' head i &&
      ln_st' body (i + 1)

    | Tm_TotBind { binder; head; body } ->
      ln' binder.binder_ty i &&
      ln' head i &&
      ln_st' body (i + 1)

    | Tm_If { b; then_; else_; post } ->
      ln' b i &&
      ln_st' then_ i &&
      ln_st' else_ i &&
      ln_opt' ln' post (i + 1)
  
    | Tm_Match {sc; returns_; brs } ->
      ln' sc i &&
      ln_opt' ln' returns_ i &&
      ln_branches' t brs i

    | Tm_IntroPure { p }
    | Tm_ElimExists { p } ->
      ln' p i

    | Tm_IntroExists { p; witnesses } ->
      ln' p i &&
      ln_list' witnesses i
  
    | Tm_While { invariant; condition; body } ->
      ln' invariant (i + 1) &&
      ln_st' condition i &&
      ln_st' body i

    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      ln' pre1 i &&
      ln_st' body1 i &&
      ln' post1 (i + 1) &&
      ln' pre2 i &&
      ln_st' body2 i &&
      ln' post2 (i + 1)

    | Tm_WithLocal { binder; initializer; body } ->
      ln' binder.binder_ty i &&
      ln' initializer i &&
      ln_st' body (i + 1)

    | Tm_WithLocalArray { binder; initializer; length; body } ->
      ln' binder.binder_ty i &&
      ln' initializer i &&
      ln' length i &&
      ln_st' body (i + 1)

    | Tm_Rewrite { t1; t2 } ->
      ln' t1 i &&
      ln' t2 i

    | Tm_Admit { typ; post } ->
      ln' typ i &&
      ln_opt' ln' post (i + 1)

    | Tm_Unreachable ->
      true

    | Tm_ProofHintWithBinders { binders; hint_type; t } ->
      let n = L.length binders in
      ln_proof_hint' hint_type (i + n) &&
      ln_st' t (i + n)

    | Tm_WithInv { name; body; returns_inv } ->
      ln' name i &&
      ln_st' body i &&
      ln_opt'
        (fun (b, r) i ->
          ln' b.binder_ty i &&
          ln' r (i + 1))
        returns_inv i

and ln_branch' (b : pattern & st_term) (i:int) : Tot bool (decreases b) =
  let (p, e) = b in
  ln_pattern' p i &&
  ln_st' e (i + pattern_shift_n p)
  
and ln_branches' (t:st_term) (brs : list branch{brs << t}) (i:int) : Tot bool (decreases brs) =
  for_all_dec t brs (fun b -> ln_branch' b i)

let ln (t:term) = ln' t (-1)
let ln_st (t:st_term) = ln_st' t (-1)
let ln_c (c:comp) = ln_c' c (-1)

noeq
type subst_elt =
  | DT : nat -> term -> subst_elt
  | NT : var -> term -> subst_elt
  | ND : var -> nat -> subst_elt

let shift_subst_elt (n:nat) = function
  | DT i t -> DT (i + n) t
  | NT x t -> NT x t
  | ND x i -> ND x (i + n)

let subst = list subst_elt

let shift_subst_n (n:nat) = L.map (shift_subst_elt n)

let shift_subst = shift_subst_n 1

let rt_subst_elt = function
  | DT i t -> RT.DT i (E.elab_term t)
  | NT x t -> RT.NT x (E.elab_term t)
  | ND x i -> RT.ND x i

let rt_subst = L.map rt_subst_elt

val subst_host_term (t:term) (ss:subst)
  : Tot (t':term { t' == RT.subst_term t (rt_subst ss) })

let subst_term (t:term) (ss:subst) : term = subst_host_term t ss

let open_term' (t:term) (v:term) (i:index) =
  subst_term t [ DT i v ]

let subst_st_comp (s:st_comp) (ss:subst)
 : st_comp =

 { s with res = subst_term s.res ss;
          pre = subst_term s.pre ss;
          post = subst_term s.post (shift_subst ss) }

let open_st_comp' (s:st_comp) (v:term) (i:index) : st_comp =
  subst_st_comp s [ DT i v ]

let subst_comp (c:comp) (ss:subst)
  : comp
  = match c with
    | C_Tot t ->
      C_Tot (subst_term t ss)

    | C_ST s -> C_ST (subst_st_comp s ss)

    | C_STAtomic inames obs s ->
      C_STAtomic (subst_term inames ss) obs
                 (subst_st_comp s ss)

    | C_STGhost s ->
      C_STGhost (subst_st_comp s ss)

let open_comp' (c:comp) (v:term) (i:index) : comp =
  subst_comp c [ DT i v ]

let subst_term_opt (t:option term) (ss:subst)
  : Tot (option term)
  = match t with
    | None -> None
    | Some t -> Some (subst_term t ss)

let open_term_opt' (t:option term) (v:term) (i:index)
  : Tot (option term) = subst_term_opt t [ DT i v ]

let rec subst_term_list (t:list term) (ss:subst)
  : Tot (list term)
  = match t with
    | [] -> []
    | hd::tl -> subst_term hd ss :: subst_term_list tl ss

let open_term_list' (t:list term) (v:term) (i:index)
  : Tot (list term) = subst_term_list t [ DT i v ]

let subst_binder b ss = 
  {b with binder_ty=subst_term b.binder_ty ss}

let open_binder b v i = 
  {b with binder_ty=open_term' b.binder_ty v i}

let rec subst_term_pairs (t:list (term & term)) (ss:subst)
  : Tot (list (term & term))
  = match t with
    | [] -> []
    | (t1, t2)::tl -> (subst_term t1 ss, subst_term t2 ss) :: subst_term_pairs tl ss 

let subst_proof_hint (ht:proof_hint_type) (ss:subst) 
  : proof_hint_type
  = match ht with
    | ASSERT { p } -> ASSERT { p=subst_term p ss }
    | UNFOLD { names; p } -> UNFOLD {names; p=subst_term p ss}
    | FOLD { names; p } -> FOLD { names; p=subst_term p ss }
    | RENAME { pairs; goal } -> RENAME { pairs=subst_term_pairs pairs ss;
                                         goal=subst_term_opt goal ss }
    | REWRITE { t1; t2 } -> REWRITE { t1=subst_term t1 ss;
                                      t2=subst_term t2 ss }
    | WILD
    | SHOW_PROOF_STATE _ -> ht

let open_term_pairs' (t:list (term * term)) (v:term) (i:index) =
  subst_term_pairs t [DT i v]

let close_term_pairs' (t:list (term * term)) (x:var) (i:index) =
  subst_term_pairs t [ND x i]

let open_proof_hint'  (ht:proof_hint_type) (v:term) (i:index) =
  subst_proof_hint ht [DT i v]

let close_proof_hint' (ht:proof_hint_type) (x:var) (i:index) =
  subst_proof_hint ht [ND x i]

let rec subst_pat (p:pattern) (ss:subst)
  : Tot pattern (decreases p)
  = match p with
    | Pat_Constant _
    | Pat_Dot_Term None ->
      p
    | Pat_Var n t -> 
      let t = RU.map_seal t (fun t -> RT.subst_term t (rt_subst ss)) in
      Pat_Var n t
    | Pat_Dot_Term (Some e) ->
      Pat_Dot_Term (Some (subst_term e ss))
    | Pat_Cons d args ->
      let args = subst_pat_args args ss in
      Pat_Cons d args
and subst_pat_args (args:list (pattern & bool)) (ss:subst)
  : Tot (list (pattern & bool)) (decreases args)
  = match args with
    | [] -> []
    | (arg, b)::tl ->
      let arg' = subst_pat arg ss in
      let tl = subst_pat_args tl (shift_subst_n (pattern_shift_n arg) ss) in
      (arg', b)::tl

let map2_opt (f: 'a -> 'b -> 'c) (x:option 'a) (y:'b)
  : option 'c
  = match x with
    | None -> None
    | Some x -> Some (f x y)

let subst_ascription (c:comp_ascription) (ss:subst)
  : comp_ascription
  = { elaborated = map2_opt subst_comp c.elaborated ss;
       annotated = map2_opt subst_comp c.annotated ss }

let rec subst_st_term (t:st_term) (ss:subst)
  : Tot st_term (decreases t)
  = let t' =
    match t.term with
    | Tm_Return { expected_type; insert_eq; term } ->
      Tm_Return { expected_type=subst_term expected_type ss;
                  insert_eq;
                  term=subst_term term ss }

    | Tm_Abs { b; q; ascription; body } ->
      Tm_Abs { b=subst_binder b ss;
               q;
               ascription=subst_ascription ascription (shift_subst ss);
               body=subst_st_term body (shift_subst ss) }

    | Tm_STApp { head; arg_qual; arg } ->
      Tm_STApp { head = subst_term head ss;
                 arg_qual;
                 arg=subst_term arg ss }

    | Tm_Bind { binder; head; body } ->
      Tm_Bind { binder = subst_binder binder ss;
                head = subst_st_term head ss;
                body = subst_st_term body (shift_subst ss) }

    | Tm_TotBind { binder; head; body } ->
      Tm_TotBind { binder = subst_binder binder ss;
                   head = subst_term head ss;
                   body = subst_st_term body (shift_subst ss) }

    | Tm_If { b; then_; else_; post } ->
      Tm_If { b = subst_term b ss;
              then_ = subst_st_term then_ ss;
              else_ = subst_st_term else_ ss;
              post = subst_term_opt post (shift_subst ss) }

    | Tm_Match { sc; returns_; brs } ->
      Tm_Match { sc = subst_term sc ss;
                 returns_ = subst_term_opt returns_ ss;
                 brs = subst_branches t ss brs }

    | Tm_IntroPure { p } ->
      Tm_IntroPure { p = subst_term p ss }

    | Tm_ElimExists { p } ->
      Tm_ElimExists { p = subst_term p ss }
      
    | Tm_IntroExists { p; witnesses } ->
      Tm_IntroExists { p = subst_term p ss;
                       witnesses = subst_term_list witnesses ss }                             

    | Tm_While { invariant; condition; body; condition_var } ->
      Tm_While { invariant = subst_term invariant (shift_subst ss);
                 condition = subst_st_term condition ss;
                 body = subst_st_term body ss;
                 condition_var }

    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      Tm_Par { pre1=subst_term pre1 ss;
               body1=subst_st_term body1 ss;
               post1=subst_term post1 (shift_subst ss);
               pre2=subst_term pre2 ss;
               body2=subst_st_term body2 ss;
               post2=subst_term post2 (shift_subst ss) }

    | Tm_WithLocal { binder; initializer; body } ->
      Tm_WithLocal { binder = subst_binder binder ss;
                     initializer = subst_term initializer ss;
                     body = subst_st_term body (shift_subst ss) }

    | Tm_WithLocalArray { binder; initializer; length; body } ->
      Tm_WithLocalArray { binder = subst_binder binder ss;
                          initializer = subst_term initializer ss;
                          length = subst_term length ss;
                          body = subst_st_term body (shift_subst ss) }

    | Tm_Rewrite { t1; t2 } ->
      Tm_Rewrite { t1 = subst_term t1 ss;
                   t2 = subst_term t2 ss }

    | Tm_Admit { ctag; u; typ; post } ->
      Tm_Admit { ctag;
                 u; 
                 typ=subst_term typ ss;
                 post=subst_term_opt post (shift_subst ss) }

    | Tm_Unreachable -> Tm_Unreachable
    
    | Tm_ProofHintWithBinders { hint_type; binders; t} ->
      let n = L.length binders in
      let ss = shift_subst_n n ss in
      Tm_ProofHintWithBinders { binders;
                                hint_type=subst_proof_hint hint_type ss; 
                                t = subst_st_term t ss }

    | Tm_WithInv { name; body; returns_inv } ->
      let name = subst_term name ss in
      let body = subst_st_term body ss in
      let returns_inv =
        match returns_inv with
        | None -> None
        | Some (b, r) ->
          Some (subst_binder b ss, 
                subst_term r (shift_subst ss))
      in
      Tm_WithInv { name; body; returns_inv }

    in
    { t with term = t' }

and subst_branches (t:st_term) (ss:subst) (brs : list branch{brs << t})
: Tot (list branch) (decreases brs)
= map_dec t brs (fun br -> subst_branch ss br)

and subst_branch (ss:subst) (b : pattern & st_term) : Tot (pattern & st_term) (decreases b) =
  let (p, e) = b in
  let p = subst_pat p ss in
  let ss = shift_subst_n (pattern_shift_n p) ss in
  p, subst_st_term e ss


let open_st_term' (t:st_term) (v:term) (i:index) : st_term =
  subst_st_term t [ DT i v ]

let open_term_nv t nv =
    open_term' t (U.term_of_nvar nv) 0

// Can use this no-name version in specs only
let open_term t v : GTot term =
    open_term_nv t (v_as_nv v)

let open_st_term_nv t nv =
    open_st_term' t (U.term_of_nvar nv) 0

// Can use this no-name version in specs only
let open_st_term t v : GTot st_term =
    open_st_term_nv t (v_as_nv v)

let open_comp_with (c:comp) (x:term) = open_comp' c x 0

let open_comp_nv c nv =
    open_comp' c (U.term_of_nvar nv) 0

let close_term' (t:term) (v:var) (i:index) : term =
  subst_term t [ ND v i ]

let close_st_comp' (s:st_comp) (v:var) (i:index) : st_comp =
  subst_st_comp s [ ND v i ]

let close_comp' (c:comp) (v:var) (i:index) : comp =
  subst_comp c [ ND v i ]

let close_term_opt' (t:option term) (v:var) (i:index) : option term =
  subst_term_opt t [ ND v i ]

let close_term_list' (t:list term) (v:var) (i:index) : list term =
  subst_term_list t [ ND v i ]

let close_binder b v i =
  subst_binder b [ ND v i ]
             
let close_st_term' (t:st_term) (v:var) (i:index) : st_term =
  subst_st_term t [ ND v i ]
      
let close_term t v = close_term' t v 0
let close_st_term t v = close_st_term' t v 0
let close_comp t v = close_comp' t v 0

let close_term_n t vs =
  let rec aux (i:nat) (vs:list var) (t:term) : Tot term (decreases vs) =
    match vs with
    | [] -> t
    | v::vs ->
      aux (i+1) vs (close_term' t v i)
  in
  aux 0 (List.rev vs) t

let close_st_term_n t vs =
  let rec aux (i:nat) (vs:list var) (t:st_term) : Tot st_term (decreases vs) =
    match vs with
    | [] -> t
    | v::vs ->
      aux (i+1) vs (close_st_term' t v i)
  in
  aux 0 (List.rev vs) t

val close_open_inverse' (t:term) 
                        (x:var { ~(x `Set.mem` freevars t) } )
                        (i:index)
  : Lemma (ensures close_term' (open_term' t (U.term_of_no_name_var x) i) x i == t)

val close_open_inverse_comp' (c:comp)
                             (x:var { ~(x `Set.mem` freevars_comp c) } )
                             (i:index)
  : Lemma (ensures close_comp' (open_comp' c (U.term_of_no_name_var x) i) x i == c)

val close_open_inverse_opt' (t:option term)
                            (x:var { ~(x `Set.mem` freevars_term_opt t) })
                            (i:index)
  : Lemma (ensures close_term_opt' (open_term_opt' t (U.term_of_no_name_var x) i) x i == t)

val close_open_inverse_list' (t:list term)
                             (x:var { ~(x `Set.mem` freevars_list t) })
                             (i:index)
  : Lemma (ensures close_term_list' (open_term_list' t (U.term_of_no_name_var x) i) x i == t)

val close_open_inverse_st' (t:st_term) 
                           (x:var { ~(x `Set.mem` freevars_st t) } )
                           (i:index)
  : Lemma (ensures close_st_term' (open_st_term' t (U.term_of_no_name_var x) i) x i == t)

val close_open_inverse (t:term) (x:var { ~(x `Set.mem` freevars t) } )
  : Lemma (ensures close_term (open_term t x) x == t)
          (decreases t)

val close_open_inverse_st (t:st_term) (x:var { ~(x `Set.mem` freevars_st t) } )
  : Lemma (ensures close_st_term (open_st_term t x) x == t)
          (decreases t)

val open_with_gt_ln (e:term) (i:int) (t:term) (j:nat)
  : Lemma
      (requires ln' e i /\ i < j)
      (ensures open_term' e t j == e)

val open_with_gt_ln_st (s:st_comp) (i:int) (t:term) (j:nat)
  : Lemma (requires ln_st_comp s i /\ i < j)
          (ensures open_st_comp' s t j == s)

val open_with_gt_ln_comp (c:comp) (i:int) (t:term) (j:nat)
  : Lemma (requires ln_c' c i /\ i < j)
          (ensures open_comp' c t j == c)

val close_with_non_freevar (e:term) (x:var) (i:nat)
  : Lemma
      (requires ~ (x `Set.mem` freevars e))
      (ensures close_term' e x i == e)

val close_with_non_freevar_st (s:st_comp) (x:var) (i:nat)
  : Lemma
    (requires ~ (x `Set.mem` freevars_st_comp s))
    (ensures close_st_comp' s x i == s)

val close_comp_with_non_free_var (c:comp) (x:var) (i:nat)
  : Lemma
    (requires ~ (x `Set.mem` freevars_comp c))
    (ensures close_comp' c x i == c)

val close_binders (bs:list binder) (vs:list var { L.length bs == L.length vs })
  : list binder
