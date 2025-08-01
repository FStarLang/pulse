open Fstarcompiler
open Prims
open FStarC_Ident
open Pulse_Syntax_Base
module U = Pulse_Syntax_Pure
module S = FStarC_Syntax_Syntax
type universe = Pulse_Syntax_Base.universe
type range = FStarC_Range.range
let u_zero : universe = U.u_zero
let u_succ (u:universe) : universe = U.u_succ u
let u_var (s:string) : universe = U.u_var s
let u_max (u0:universe) (u1:universe) : universe = U.u_max u0 u1
let u_unknown : universe = U.u_unknown

type qualifier = Pulse_Syntax_Base.qualifier
let as_qual (imp:bool) = if imp then Some Pulse_Syntax_Base.Implicit else None
let tc_qual = Some Pulse_Syntax_Base.TcArg
type bv = Pulse_Syntax_Base.bv
let mk_bv (i:index) (name:string) (r:range) : bv =
 let pp = { name; range=r} in
 { bv_index = i; bv_ppname=pp }
let index_of_bv (x:bv) = x.bv_index
type nm = Pulse_Syntax_Base.nm
let mk_nm (i:index) (name:string) (r:range) : nm =
 let pp = { name; range=r} in
 { nm_index = i; nm_ppname=pp }


type fv = Pulse_Syntax_Base.fv
let mk_fv (nm:lident) (r:range) : fv = 
 { fv_name = FStarC_Ident.path_of_lid nm;
   fv_range = r }

type term = Pulse_Syntax_Base.term
type binder = Pulse_Syntax_Base.binder
type comp = Pulse_Syntax_Base.comp
type slprop = term

let meta_qual t = Some (Pulse_Syntax_Base.Meta t)

let ppname_of_id (i:ident) : ppname = { name = FStarC_Ident.string_of_id i; range = i.idRange }

let mk_binder_with_attrs (x:ident) (t:term) (attrs:term list) : binder =
  { binder_ty = t;
    binder_ppname=ppname_of_id x;
    binder_attrs=attrs}
  
let mk_binder (x:ident) (t:term) : binder =
  mk_binder_with_attrs x t []

let tm_bvar (bv:bv) : term = U.tm_bvar bv
let tm_var (x:nm) : term = U.tm_var x
let tm_fvar (x:fv) : term = U.tm_fvar x
let tm_uinst (l:fv) (us:universe list) : term = U.tm_uinst l us
let wr r t = Pulse_Syntax_Pure.pack_term_view_wr t r
let tm_emp r : term = wr r Tm_Emp
let tm_pure (p:term) r : term = wr r (Tm_Pure p)
let tm_star (p0:term) (p1:term) r : term = wr r (Tm_Star (p0, p1))
let tm_exists (b:binder) (body:slprop) r : term = wr r (Tm_ExistsSL (U_unknown, b, body))
let tm_forall (b:binder) (body:slprop) r : term = wr r (Tm_ForallSL (U_unknown, b, body))
let map_aqual (q:S.aqual) =
  match q with
  | Some { S.aqual_implicit = true } -> Some Implicit
  | _ -> None
let tm_arrow (b:binder) (q:S.aqual) (body:comp) : term =
  U.tm_arrow b (map_aqual q) body
let tm_expr (t:S.term) r : term = Pulse_Syntax_Pure.wr t r
let tm_unknown r : term = wr r Tm_Unknown
let tm_emp_inames :term = wr FStarC_Range.dummyRange Tm_EmpInames
let tm_add_inv (names:term) (n:term) r : term =
  Pulse_RuntimeUtils.set_range (Pulse_Syntax_Pure.tm_add_inv names n) r

let is_tm_exists (t:term) : bool =
  match Pulse_Syntax_Pure.inspect_term t with
  | Tm_ExistsSL _ -> true
  | _ -> false

let mk_tot (t:term) : comp = C_Tot t

let mk_st_comp (pre:term) (ret:binder) (post:term) : st_comp =
  { u = U_unknown;
    res = ret.binder_ty;
    pre = pre;
    post = post
  }

let mk_comp (pre:term) (ret:binder) (post:term) : comp =
   C_ST (mk_st_comp pre ret post)

let ghost_comp (inames:term) (pre:term) (ret:binder) (post:term) : comp =
   C_STGhost (inames, mk_st_comp pre ret post)

let neutral_comp (inames:term) (pre:term) (ret:binder) (post:term) : comp =
   C_STAtomic (inames, Neutral, mk_st_comp pre ret post)

let atomic_comp (inames:term) (pre:term) (ret:binder) (post:term) : comp =
   C_STAtomic (inames, Observable, mk_st_comp pre ret post)

let unobs_comp (inames:term) (pre:term) (ret:binder) (post:term) : comp =
   C_STAtomic (inames, Neutral, mk_st_comp pre ret post)

module PSB = Pulse_Syntax_Builder
type constant = Pulse_Syntax_Base.constant
let inspect_const = FStarC_Reflection_V2_Builtins.inspect_const

type pattern = Pulse_Syntax_Base.pattern

let pat_var s _r = PSB.(pat_var s S.tun)
let pat_constant c _r = PSB.(pat_const c)
let pat_cons fv vs _r = PSB.(pat_cons fv (List.map (fun v -> (v,false)) vs))

type st_term = Pulse_Syntax_Base.st_term
type branch = Pulse_Syntax_Base.branch

let mk_branch (p:pattern) (t:st_term) (norw:bool) : branch =
  PSB.mk_branch p t norw

let tm_return (t:term) r : st_term = PSB.(with_range (tm_return (tm_unknown r) false t) r)

let tm_ghost_return (t:term) r : st_term = PSB.(with_range (tm_return (tm_unknown r) false t) r)

let tm_abs (b:binder)
           (q:qualifier option)
           (c:comp option)
           (body:st_term)
           r
  : st_term 
  = let asc = { annotated = c; elaborated = None } in
    PSB.(with_range (tm_abs b q asc body) r)

let tm_st_app (head:term) (q:S.aqual) (arg:term) r : st_term =
  PSB.(with_range (tm_stapp head (map_aqual q) arg) r)
    
let tm_bind (x:binder) (e1:st_term) (e2:st_term) r : st_term =
  PSB.(with_range (tm_bind x e1 e2) r)

let tm_totbind (x:binder) (e1:term) (e2:st_term) r : st_term =
  PSB.(with_range (tm_totbind x e1 e2) r)

let tm_let_mut (x:binder) (v:term) (k:st_term) r : st_term =
  PSB.(with_range (tm_with_local x v k) r)

let tm_let_mut_array (x:binder) (v:term) (n:term) (k:st_term) (r:range) : st_term =
  PSB.(with_range (tm_with_local_array x v n k) r)

let tm_while (head:st_term) (invariant: (ident * slprop)) (body:st_term) r : st_term =
  PSB.(with_range (tm_while (snd invariant) head (ppname_of_id (fst invariant)) body) r)
   
let tm_nuwhile (head:st_term) (invariant: slprop) (body:st_term) r : st_term =
  PSB.(with_range (tm_nuwhile invariant head body) r)
   
let tm_if (head:term) (returns_annot:slprop option) (then_:st_term) (else_:st_term) r : st_term =
  PSB.(with_range (tm_if head then_ else_ returns_annot) r)

let tm_match (sc:term) (returns_:slprop option) (brs:branch list) r : st_term =
  PSB.(with_range (tm_match sc returns_ brs) r)

let tm_intro_exists (p:slprop) (witnesses:term list) r : st_term =
  PSB.(with_range (tm_intro_exists p witnesses) r)

let is_tm_intro_exists (s:st_term) : bool =
  match s.term1 with
  | Tm_IntroExists _ -> true
  | _ -> false

let trans_ns = function
  | None -> None
  | Some l -> Some (List.map FStarC_Ident.string_of_lid l)

type hint_type = Pulse_Syntax_Base.proof_hint_type

let mk_wild_hint_type = Pulse_Syntax_Base.WILD
let mk_show_proof_state_hint_type r = Pulse_Syntax_Base.SHOW_PROOF_STATE r
let mk_assert_hint_type vp = PSB.mk_assert_hint_type vp
let mk_unfold_hint_type names vp = PSB.mk_unfold_hint_type names vp
let mk_fold_hint_type names vp = PSB.mk_fold_hint_type names vp
let mk_rename_hint_type pairs goal tac_opt = PSB.mk_rename_hint_type pairs goal tac_opt
let mk_rewrite_hint_type p1 p2 tac_opt = PSB.mk_rewrite_hint_type p1 p2 tac_opt

let tm_proof_hint_with_binders (ht:_) (binders: binder list)  (s:st_term) r : st_term =
  PSB.(with_range (Tm_ProofHintWithBinders { hint_type=ht;
                                             binders;
                                             t=s }) r)

let tm_with_inv (name:term) (body:st_term) returns_inv r : st_term =
  PSB.(with_range (tm_with_inv name body returns_inv) r)

let tm_par p1 p2 q1 q2 b1 b2 r : st_term =
  PSB.(with_range (tm_par p1 b1 q1 p2 b2 q2) r)

let tm_admit r : st_term =
  PSB.(with_range (tm_admit STT u_zero (tm_unknown r) None) r)
let tm_unreachable r : st_term =
  let dummy_comp = C_Tot (tm_unknown r) in
  PSB.(with_range (tm_unreachable { c = dummy_comp }) r)
  
let close_term t v = Pulse_Syntax_Naming.close_term t v
let close_st_term t v = Pulse_Syntax_Naming.close_st_term t v
let close_st_term_n t v = Pulse_Syntax_Naming.close_st_term_n t v
let close_comp t v = Pulse_Syntax_Naming.close_comp t v
let close_comp_n t v = Pulse_Syntax_Naming.close_comp_n t v
let comp_pre c =
  match c with
   | C_ST st
   | C_STAtomic (_, _, st)
   | C_STGhost (_, st) -> st.pre
   | _ -> Pulse_Syntax_Pure.tm_emp

let comp_res c =
  match c with
   | C_ST st
   | C_STAtomic (_, _, st)
   | C_STGhost (_, st) -> st.res
   | C_Tot t -> t

let comp_post c =
  match c with
   | C_ST st
   | C_STAtomic (_, _, st)
   | C_STGhost (_, st) -> st.post
   | _ -> Pulse_Syntax_Pure.tm_emp

let mark_statement_sequence (s : st_term) : st_term =
  PSB.mark_statement_sequence s

let mark_not_source (s : st_term) : st_term =
  PSB.mark_not_source s

let print_exn (e:exn) = Printexc.to_string e

open FStar_Pervasives
module Env = FStarC_TypeChecker_Env
let tac_to_string (env:Env.env) f =
    let ps =
        FStarC_Tactics_V2_Basic.proofstate_of_goals 
                (Env.get_range env)
                env
                []
                []
    in
    match f ps with
    | FStarC_Tactics_Result.Success (x, _) -> x
    | FStarC_Tactics_Result.Failed (exn, _) -> failwith (print_exn exn)

let binder_to_string (env:Env.env) (b:binder)
  : string
  = tac_to_string env (Pulse_Syntax_Printer.binder_to_string b)
let bv_to_string (x:bv) : string =
    x.bv_ppname.name ^ "@" ^
     (string_of_int x.bv_index)
let term_to_string (env:Env.env) (t:term)
  : string
  = tac_to_string env (Pulse_Syntax_Printer.term_to_string t)
let st_term_to_string (env:Env.env) (t:st_term)
  : string
  = tac_to_string env (Pulse_Syntax_Printer.st_term_to_string t)
type decl = Pulse_Syntax_Base.decl
let decl_to_string (env:Env.env) (t:decl)
  : string
  = tac_to_string env (Pulse_Syntax_Printer.decl_to_string t)
let comp_to_string (env:Env.env) (t:comp)
  : string
  = tac_to_string env (Pulse_Syntax_Printer.comp_to_string t)  
let close_binders bs xs = Pulse_Syntax_Naming.close_binders bs xs
let bvs_as_subst bvs =
  List.fold_left
    (fun s b -> Fstar_pluginlib.FStar_Reflection_Typing.ND (b, Z.of_int 0)::(Pulse_Syntax_Naming.shift_subst s))
    [] bvs
let subst_term s t = Pulse_Syntax_Naming.subst_term t s
let subst_st_term s t = Pulse_Syntax_Naming.subst_st_term t s
let subst_proof_hint s t = Pulse_Syntax_Naming.subst_proof_hint t s


let fn_defn rng id isrec us bs comp meas body =
  PSB.mk_decl (PSB.mk_fn_defn id isrec us bs comp meas body) rng
let fn_decl rng id us bs comp =
  PSB.mk_decl (PSB.mk_fn_decl id us bs comp) rng
