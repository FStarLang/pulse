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

module Pulse.Checker.Prover.Substs

open FStar.List.Tot

open Pulse.Syntax
open Pulse.Typing.Env
open Pulse.Typing
open Pulse.Checker.Pure

module L = FStar.List.Tot

module Env = Pulse.Typing.Env
module Metatheory = Pulse.Typing.Metatheory

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b {y == x} = x

let rec no_repeats (l:list var) : Type0 =
  match l with
  | [] -> True
  | x::tl -> (~ (L.memP x tl)) /\ no_repeats tl  

type ss_dom = l:list var { no_repeats l }

type ss_map = m:Map.t var term {
  forall (x:var). (~ (Map.contains m x)) ==> Map.sel m x == tm_unknown
}

let remove_map (m:ss_map) (x:var) =
  Map.restrict (Set.complement (Set.singleton x)) (Map.upd m x tm_unknown)

let rec is_dom (l:ss_dom) (m:ss_map) : Type0 =
  match l with
  | [] -> Set.equal (Map.domain m) Set.empty
  | x::tl ->
    Map.contains m x /\ is_dom tl (remove_map m x)

let rec is_dom_mem (l:ss_dom) (m:ss_map)
  : Lemma
      (requires is_dom l m)
      (ensures forall (x:var).{:pattern L.memP x l \/ Map.contains m x}
                              L.memP x l <==> Map.contains m x)
      [SMTPat (is_dom l m)] =
  match l with
  | [] -> ()
  | y::tl -> is_dom_mem tl (remove_map m y)

noeq
type ss_t = {
  l : ss_dom;
  m : m:ss_map { is_dom l m }
}

let rec separate_map (sep:document)
   (f : 'a -> T.Tac document)
   (xs : list 'a)
   : T.Tac document =
  match xs with
  | [] -> empty
  | [x] -> f x
  | x::xs ->
    let doc = f x in
    let docs = separate_map sep f xs in
    doc ^^ sep ^^ docs

instance pp_ss_t : printable ss_t = {
  pp = (function {l;m} ->
        //  doc_of_string "dom="
        //  pp (l <: list int) ^^
        //  doc_of_string " |-> " ^^
        l |> separate_map comma (fun k ->
               pp (k <: int) ^^ doc_of_string " -> " ^^ pp (Map.sel m k))
        );
}

let ln_ss_t (s:ss_t) =
  List.Tot.for_all (fun x -> ln (Map.sel s.m x)) s.l

let as_map (ss:ss_t) = ss.m

let empty = { l = []; m = Map.const_on Set.empty tm_unknown }

let is_dom_push
  (l:ss_dom)
  (m:ss_map { is_dom l m })
  (x:var { ~ (Map.contains m x ) })
  (t:term)
  : Lemma (is_dom (x::l) (Map.upd m x t)) =

  assert (Map.equal (remove_map (Map.upd m x t) x) m)

let lemma_dom_empty () = ()

let push (ss:ss_t) (x:var { ~ (contains ss x) }) (t:term) : ss_t =
  
  is_dom_push ss.l ss.m x t;
  { l = x::ss.l;
    m = Map.upd ss.m x t }

let tail (ss:ss_t { Cons? ss.l }) : ss_t =
   { l = L.tl ss.l; m = remove_map ss.m (L.hd ss.l) }

let rec push_ss (ss1:ss_t) (ss2:ss_t { Set.disjoint (dom ss1) (dom ss2) })
  : Tot ss_t (decreases L.length ss2.l) =
  match ss2.l with
  | [] -> ss1
  | x::tl ->
    push_ss (push ss1 x (Map.sel ss2.m x)) (tail ss2)

let check_disjoint ss1 ss2 =
  admit ();
  not (L.existsb (fun v1 -> L.mem v1 ss2.l) ss1.l)

let rec diff_aux (ss1 ss2:ss_t) (acc:ss_t { Set.disjoint (dom acc) (dom ss2) })
  : Tot (ss:ss_t { Set.disjoint (dom ss) (dom ss2) }) (decreases L.length ss1.l) =
  match ss1.l with
  | [] -> acc
  | x::l ->
    if L.mem x ss2.l
    then let ss1 = { ss1 with l; m = remove_map ss1.m x } in
         diff_aux ss1 ss2 acc
    else let acc_l = x::acc.l in
         let acc_m = Map.upd acc.m x (Map.sel ss1.m x) in
         assume (no_repeats acc_l /\ is_dom acc_l acc_m);
         let acc = { l = acc_l; m = acc_m } in
         let ss1 = { ss1 with l; m = remove_map ss1.m x } in
         diff_aux ss1 ss2 acc

let diff ss1 ss2 = diff_aux ss1 ss2 empty

#push-options "--warn_error -271"
let push_as_map (ss1 ss2:ss_t)
  : Lemma (requires Set.disjoint (dom ss1) (dom ss2))
          (ensures Map.equal (as_map (push_ss ss1 ss2))
                             (Map.concat (as_map ss1) (as_map ss2)))
          (decreases L.length ss2.l)
          [SMTPat (as_map (push_ss ss1 ss2))] =

  let rec aux (ss1 ss2:ss_t)
    : Lemma (requires Set.disjoint (dom ss1) (dom ss2))
            (ensures Map.equal (as_map (push_ss ss1 ss2))
                               (Map.concat (as_map ss1) (as_map ss2)))
            (decreases L.length ss2.l)
            [SMTPat ()] =
    match ss2.l with
    | [] -> ()
    | x::tl -> aux (push ss1 x (Map.sel ss2.m x)) (tail ss2)
  in
  ()
#pop-options

let rec remove_l (l:ss_dom) (x:var { L.memP x l })
  : Pure ss_dom
         (requires True)
         (ensures fun r -> forall (y:var). L.memP y r <==> (L.memP y l /\ y =!= x)) =
  match l with
  | [] -> assert False; []
  | y::tl ->
    if y = x then tl
    else y::(remove_l tl x)

let rec is_dom_remove
  (l:ss_dom)
  (m:ss_map { is_dom l m })
  (x:var { Map.contains m x })
  : Lemma (is_dom (remove_l l x) (remove_map m x))
          [SMTPat (remove_l l x); SMTPat (remove_map m x)] =
 
  match l with
  | [] -> ()
  | y::tl ->
    if x = y then ()
    else let t_y = Map.sel m y in
         let m1 = remove_map m y in
         is_dom_remove tl m1 x;
         assert (is_dom (remove_l tl x) (remove_map m1 x));
         is_dom_push (remove_l tl x) (remove_map m1 x) y t_y;
         assert (Map.equal (Map.upd (remove_map m1 x) y t_y)
                           (remove_map m x))

let rec ss_term (t:term) (ss:ss_t) : Tot term (decreases L.length ss.l) =
  match ss.l with
  | [] -> t
  | y::tl ->
    let t = subst_term t [ RT.NT y (Map.sel ss.m y) ] in
    ss_term t (tail ss)

let rec ss_st_term (t:st_term) (ss:ss_t) : Tot st_term (decreases L.length ss.l) =
  match ss.l with
  | [] -> t
  | y::tl ->
    let t = subst_st_term t [ RT.NT y (Map.sel ss.m y) ] in
    ss_st_term t (tail ss)

let rec ss_st_comp (s:st_comp) (ss:ss_t)
  : Tot st_comp (decreases L.length ss.l) =
  match ss.l with
  | [] -> s
  | y::tl ->
    let s = subst_st_comp s [ RT.NT y (Map.sel ss.m y) ] in
    ss_st_comp s (tail ss)

let rec ss_comp (c:comp) (ss:ss_t)
  : Tot comp (decreases L.length ss.l) =
  match ss.l with
  | [] -> c
  | y::tl ->
    let c = subst_comp c [ RT.NT y (Map.sel ss.m y) ] in
    ss_comp c (tail ss)

let rec ss_binder (b:binder) (ss:ss_t)
  : Tot binder (decreases L.length ss.l) =
  match ss.l with
  | [] -> b
  | y::tl ->
    let b = subst_binder b [ RT.NT y (Map.sel ss.m y) ] in
    ss_binder b (tail ss)

let rec ss_env (g:env) (ss:ss_t)
  : Tot (g':env { fstar_env g' == fstar_env g /\
                  Env.dom g' == Env.dom g })
        (decreases L.length ss.l) =
  admit ();
  match ss.l with
  | [] -> g
  | y::tl -> ss_env (subst_env g [ RT.NT y (Map.sel ss.m y) ]) (tail ss)

let rec ss_st_comp_commutes (s:st_comp) (ss:ss_t)
  : Lemma (ensures
             ss_st_comp s ss ==
             { s with res = ss_term s.res ss;
                      pre = ss_term s.pre ss;
                      post = ss_term s.post ss; })  // no shifting required
          (decreases L.length ss.l)
          [SMTPat (ss_st_comp s ss)] =
  match ss.l with
  | [] -> ()
  | y::tl -> ss_st_comp_commutes (subst_st_comp s [ RT.NT y (Map.sel ss.m y) ]) (tail ss)

let rec ss_comp_commutes (c:comp) (ss:ss_t)
  : Lemma (ensures
             (let r = ss_comp c ss in
              (C_Tot? c ==> r == C_Tot (ss_term (comp_res c) ss)) /\
              (C_ST? c ==> r == C_ST (ss_st_comp (st_comp_of_comp c) ss)) /\
              (C_STAtomic? c ==> r == C_STAtomic (ss_term (comp_inames c) ss)
                                                 (C_STAtomic?.obs c)
                                                 (ss_st_comp (st_comp_of_comp c) ss)) /\
              (C_STGhost? c ==> r == C_STGhost (ss_term (comp_inames c) ss)
                                               (ss_st_comp (st_comp_of_comp c) ss))))
          (decreases L.length ss.l)
          [SMTPat (ss_comp c ss)] =
  match ss.l with
  | [] -> ()
  | y::tl -> ss_comp_commutes (subst_comp c [ RT.NT y (Map.sel ss.m y) ]) (tail ss)

let rec nt_substs_st_comp_commutes (s:st_comp) (nts:nt_substs)
  : Lemma (ensures
             nt_subst_st_comp s nts ==
             { s with res = nt_subst_term s.res nts;
                      pre = nt_subst_term s.pre nts;
                      post = nt_subst_term s.post nts; })  // no shifting required
          (decreases nts)
          [SMTPat (nt_subst_st_comp s nts)] =
  match nts with
  | [] -> ()
  | (RT.NT x e)::nts_tl -> nt_substs_st_comp_commutes (nt_subst_st_comp s [ RT.NT x e ]) nts_tl

let rec nt_subst_comp_commutes (c:comp) (nts:nt_substs)
  : Lemma (ensures
             (let r = nt_subst_comp c nts in
              (C_Tot? c ==> r == C_Tot (nt_subst_term (comp_res c) nts)) /\
              (C_ST? c ==> r == C_ST (nt_subst_st_comp (st_comp_of_comp c) nts)) /\
              (C_STAtomic? c ==> r == C_STAtomic (nt_subst_term (comp_inames c) nts)
                                                 (C_STAtomic?.obs c)
                                                 (nt_subst_st_comp (st_comp_of_comp c) nts)) /\
              (C_STGhost? c ==> r == C_STGhost (nt_subst_term (comp_inames c) nts)
                                               (nt_subst_st_comp (st_comp_of_comp c) nts))))
          (decreases nts)
          [SMTPat (nt_subst_comp c nts)] =
  match nts with
  | [] -> ()
  | (RT.NT x e)::nts_tl -> nt_subst_comp_commutes (nt_subst_comp c [ RT.NT x e ]) nts_tl

let rec is_permutation (nts:nt_substs) (ss:ss_t) : Type0 =
  match nts, ss.l with
  | [], [] -> True
  | (RT.NT x e)::nts_rest, _::_ ->
    Map.contains ss.m x /\
    Map.sel ss.m x == e /\
    is_permutation nts_rest ({l=remove_l ss.l x; m=remove_map ss.m x})
  | _ -> False

#push-options "--z3rlimit 20"
let rec ss_to_nt_substs (g:env) (uvs:env) (ss:ss_t)
  : T.Tac (either (nts:nt_substs &
                   effect_labels:list T.tot_or_ghost {
                     well_typed_nt_substs g uvs nts effect_labels /\
                     is_permutation nts ss
                   })
                  string) =

  let g = Env.push_context g "ss_to_nt_substs" (range_of_env g) in
  match bindings uvs with
  | [] ->
    (match ss.l with
     | [] -> Inl (| [], [] |)
     | x::_ ->
       Inr (Printf.sprintf "extra uvars in the substitutions collected by the prover, e.g._#%d" x))
  | _ ->
    let x, ty, rest_uvs = remove_binding uvs in
    if Map.contains ss.m x
    then let t = Map.sel ss.m x in
         let (| eff, d |) = core_check_term_at_type g t ty in
         let _ = FStar.Squash.return_squash d in
         let ropt =
           ss_to_nt_substs g (subst_env rest_uvs [ RT.NT x t ]) {l=remove_l ss.l x;
                                                              m=remove_map ss.m x} in
         match ropt with
         | Inr e -> Inr e
         | Inl (| nts, effect_labels |) ->
           let r : (nts:nt_substs &
                    effect_labels:list T.tot_or_ghost {
                      well_typed_nt_substs g uvs nts effect_labels /\
                      is_permutation nts ss
                    }) = (| (RT.NT x t)::nts, eff::effect_labels |) in
           Inl r
    else Inr (Printf.sprintf "prover could not prove uvar _#%d" x)
#pop-options

let rec well_typed_nt_substs_prefix
  (g:env)
  (uvs:env)
  (nts:nt_substs)
  (effect_labels:list T.tot_or_ghost)
  (uvs1:env)
  : Pure (nt_substs & list T.tot_or_ghost)
         (requires well_typed_nt_substs g uvs nts effect_labels /\ env_extends uvs uvs1)
         (ensures fun (nts1, effect_labels1) -> well_typed_nt_substs g uvs1 nts1 effect_labels1)
         (decreases L.length nts) =
  match bindings uvs1, bindings uvs with
  | [], _ -> [], []
  | _::_, _::_ ->
    let x1, ty1, rest_uvs1 = remove_binding uvs1 in
    let x, ty, rest_uvs = remove_binding uvs in
    assume (x1 == x /\ ty1 == ty);
    let (RT.NT y e)::nts_rest = nts in
    let eff::effect_labels_rest = effect_labels in
    assume (env_extends (subst_env rest_uvs [ RT.NT y e ]) (subst_env rest_uvs1 [ RT.NT y e ]));
    let nts, labs =
      well_typed_nt_substs_prefix
        g
        (subst_env rest_uvs [ RT.NT y e ])
        nts_rest
        effect_labels_rest
        (subst_env rest_uvs1 [ RT.NT y e ]) in
    ((RT.NT y e)::nts),
    (eff::labs)

let ss_nt_subst (g:env) (uvs:env) (ss:ss_t) (nts:nt_substs) (effect_labels:list T.tot_or_ghost)
  : Lemma
      (requires
         disjoint uvs g /\
         well_typed_nt_substs g uvs nts effect_labels /\
         is_permutation nts ss)
      (ensures
         (forall (t:term). nt_subst_term t nts == ss_term t ss) /\
         (forall (b:binder). nt_subst_binder b nts == ss_binder b ss) /\
         (forall (t:st_term). nt_subst_st_term t nts == ss_st_term t ss) /\
         (forall (c:comp). nt_subst_comp c nts == ss_comp c ss) /\
         (forall (s:st_comp). nt_subst_st_comp s nts == ss_st_comp s ss)) = admit ()

#push-options "--z3rlimit 20"
let rec st_typing_nt_substs
  (g:env) (uvs:env) (g':env { pairwise_disjoint g uvs g' })
  (#t:st_term) (#c:comp_st) (t_typing:st_typing (push_env g (push_env uvs g')) t c)
  (nts:nt_substs)
  (effect_labels:list T.tot_or_ghost { well_typed_nt_substs g uvs nts effect_labels })
  : Tot (either
           (st_typing (push_env g (nt_subst_env g' nts)) (nt_subst_st_term t nts) (nt_subst_comp c nts))
           (var & term))
        (decreases L.length nts) =

  match bindings uvs with
  | [] ->
    assert (equal (push_env uvs g') g');
    Inl t_typing
  | _ ->
    let x, ty, uvs_rest = remove_binding uvs in
    let (RT.NT _ e)::nts_rest = nts in
    let eff::effect_labels_rest = effect_labels in
    let e_typing : typing g e eff ty = FStar.IndefiniteDescription.elim_squash () in
    if (not (eff = T.E_Ghost)) || C_STGhost? c
    then begin
      push_env_assoc (singleton_env (fstar_env uvs) x ty) uvs_rest g';
      let t_typing
        : st_typing (push_env g (push_env (singleton_env (fstar_env g) x ty) (push_env uvs_rest g'))) t c
        = coerce_eq t_typing () in
      let t_typing
        : st_typing (push_env g (subst_env (push_env uvs_rest g') [ RT.NT x e ]))
                    (subst_st_term t [ RT.NT x e ])
                    (subst_comp c [ RT.NT x e ])
        = Metatheory.st_typing_subst g x ty (push_env uvs_rest g') e_typing t_typing () in

      assume (subst_env (push_env uvs_rest g') [ RT.NT x e ] ==
              push_env (subst_env uvs_rest [ RT.NT x e ]) (subst_env g' [ RT.NT x e ]));


      st_typing_nt_substs g
        (subst_env uvs_rest [ RT.NT x e ])
        (subst_env g' [ RT.NT x e ])
        t_typing nts_rest effect_labels_rest
    end
    else Inr (x, e)
#pop-options

// let st_typing_subst (g:env) (uvs:env { disjoint uvs g }) (t:st_term) (c:comp_st)
//   (d:st_typing (push_env g uvs) t c)
//   (ss:ss_t)

//   : T.Tac (option (st_typing g (ss_st_term t ss) (ss_comp c ss))) =

//   let nts_opt = ss_to_nt_substs g uvs ss in
//   match nts_opt with
//   | Inr e -> None
//   | Some nts ->
//     let g' = mk_env (fstar_env g) in
//     assert (equal (push_env uvs g') uvs);
//     let d = st_typing_nt_substs g uvs g' d nts in
//     assume (equal (push_env g (nt_subst_env g' nts)) g);
//     Some d

let st_typing_nt_substs_derived
  (g:env) (uvs:env { disjoint uvs g })
  (#t:st_term) (#c:comp_st) (t_typing:st_typing (push_env g uvs) t c)
  (ss:nt_substs)
  (effect_labels:list T.tot_or_ghost { well_typed_nt_substs g uvs ss effect_labels })
  : either (st_typing g (nt_subst_st_term t ss) (nt_subst_comp c ss)) (var & term) =

  let g' = mk_env (fstar_env g) in
  assert (equal (push_env g (push_env uvs g')) (push_env g uvs));
  let d = st_typing_nt_substs g uvs g' (coerce_eq t_typing ()) ss effect_labels in
  assume (nt_subst_env g' ss == g');
  assert (equal (push_env g (nt_subst_env g' ss)) g);
  d

let vprop_equiv_nt_substs_derived _ _ _ _ _ = admit ()
