module Pulse.Syntax
module RTB = FStar.Reflection.Typing.Builtins
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module T = FStar.Tactics

let host_term_equality (t1 t2:host_term)
  : Lemma
    (ensures R.term_eq t1 t2 <==> t1==t2)
  = admit()

let rec eq_tm (t1 t2:term) 
  : Tot (b:bool { b <==> (t1 == t2) }) (decreases t1)
  = match t1, t2 with
    | Tm_VProp, Tm_VProp
    | Tm_Emp, Tm_Emp
    | Tm_Inames, Tm_Inames
    | Tm_EmpInames, Tm_EmpInames
    | Tm_Unknown, Tm_Unknown -> true
    | Tm_BVar x1, Tm_BVar x2 -> x1.bv_index = x2.bv_index
    | Tm_Var x1,  Tm_Var x2 -> x1.nm_index = x2.nm_index
    | Tm_FVar x1, Tm_FVar x2 -> x1.fv_name = x2.fv_name
    | Tm_UInst x1 us1, Tm_UInst x2 us2 -> x1.fv_name=x2.fv_name && us1=us2
    | Tm_Constant c1, Tm_Constant c2 -> c1=c2
    | Tm_Refine b1 t1, Tm_Refine b2 t2 -> 
      eq_tm b1.binder_ty b2.binder_ty &&
      eq_tm t1 t2
    | Tm_PureApp h1 o1 t1, Tm_PureApp h2 o2 t2 ->
      eq_tm h1 h2 &&
      o1=o2 &&
      eq_tm t1 t2
    | Tm_Star l1 r1, Tm_Star l2 r2 ->
      eq_tm l1 l2 &&
      eq_tm r1 r2
    | Tm_Pure p1, Tm_Pure p2 ->
      eq_tm p1 p2
    | Tm_Type u1, Tm_Type u2 ->
      u1=u2
    | Tm_Let t1 e1 e1', Tm_Let t2 e2 e2' ->
      eq_tm t1 t2 &&
      eq_tm e1 e2 &&
      eq_tm e1' e2'
    | Tm_ExistsSL u1 t1 b1 _, Tm_ExistsSL u2 t2 b2 _
    | Tm_ForallSL u1 t1 b1, Tm_ForallSL u2 t2 b2 ->
      u1=u2 &&
      eq_tm t1 t2 &&
      eq_tm b1 b2
    | Tm_Arrow b1 q1 c1, Tm_Arrow b2 q2 c2 ->
      eq_tm b1.binder_ty b2.binder_ty &&
      q1=q2 &&
      eq_comp c1 c2
    | Tm_UVar z1, Tm_UVar z2 ->
      z1=z2
    | Tm_FStar t1, Tm_FStar t2 ->
      host_term_equality t1 t2;
      R.term_eq t1 t2
    | _ -> false
    
and eq_comp (c1 c2:comp) 
  : Tot (b:bool { b <==> (c1 == c2) }) (decreases c1)
  = match c1, c2 with
    | C_Tot t1, C_Tot t2 ->
      eq_tm t1 t2
    | C_ST s1, C_ST s2 ->
      eq_st_comp s1 s2
    | C_STAtomic i1 s1, C_STAtomic i2 s2
    | C_STGhost i1 s1, C_STGhost i2 s2 ->
      eq_tm i1 i2 &&
      eq_st_comp s1 s2
    | _ -> false

and eq_st_comp (s1 s2:st_comp)  
  : b:bool { b <==> (s1 == s2) }
  = s1.u=s2.u && 
    eq_tm s1.res s2.res &&
    eq_tm s1.pre s2.pre &&
    eq_tm s1.post s2.post

let eq_tm_opt (t1 t2:option term)
  : b:bool { b <==> (t1 == t2) }
  = match t1, t2 with
    | None, None -> true
    | Some t1, Some t2 -> eq_tm t1 t2
    | _ -> false

let rec eq_tm_list (t1 t2:list term)
  : b:bool { b <==> (t1 == t2) }
  = match t1, t2 with
    | [], [] -> true
    | h1::t1, h2::t2 ->
      eq_tm h1 h2 &&
      eq_tm_list t1 t2
    | _ -> false

let rec eq_st_term (t1 t2:st_term) 
  : b:bool { b <==> (t1 == t2) }
  = match t1.term, t2.term with
    | Tm_Return {ctag=c1; insert_eq=b1; term=t1}, 
      Tm_Return {ctag=c2; insert_eq=b2; term=t2} ->
      c1 = c2 &&
      b1 = b2 &&
      eq_tm t1 t2

    | Tm_Abs { b=b1; q=o1; pre=p1; body=t1; post=q1},
      Tm_Abs { b=b2; q=o2; pre=p2; body=t2; post=q2} ->
      eq_tm b1.binder_ty b2.binder_ty &&
      o1=o2 &&
      eq_tm_opt p1 p2 &&
      eq_st_term t1 t2 &&
      eq_tm_opt q1 q2
  
    | Tm_STApp { head=h1; arg_qual=o1; arg=t1},
      Tm_STApp { head=h2; arg_qual=o2; arg=t2} ->
      eq_tm h1 h2 &&
      o1=o2 &&
      eq_tm t1 t2

    | Tm_Bind { binder=b1; head=t1; body=k1 },
      Tm_Bind { binder=b2; head=t2; body=k2 } ->
      eq_tm b1.binder_ty b2.binder_ty &&
      eq_st_term t1 t2 &&
      eq_st_term k1 k2

    | Tm_TotBind { head=t1; body=k1 },
      Tm_TotBind { head=t2; body=k2 } ->
      eq_tm t1 t2 &&
      eq_st_term k1 k2
      
    | Tm_IntroExists { erased=b1; p=p1; witnesses=l1 },
      Tm_IntroExists { erased=b2; p=p2; witnesses=l2 } ->
      b1 = b2 &&
      eq_tm p1 p2 &&
      eq_tm_list l1 l2

    | Tm_ElimExists {p=p1},
      Tm_ElimExists {p=p2} ->
      eq_tm p1 p2

    | Tm_If { b=g1; then_=ethen1; else_=eelse1; post=p1},
      Tm_If { b=g2; then_=ethen2; else_=eelse2; post=p2} ->
      eq_tm g1 g2 &&
      eq_st_term ethen1 ethen2 &&
      eq_st_term eelse1 eelse2 &&
      eq_tm_opt p1 p2
    
    | Tm_While { invariant=inv1; condition=cond1; body=body1 },
      Tm_While { invariant=inv2; condition=cond2; body=body2 } ->
      eq_tm inv1 inv2 &&
      eq_st_term cond1 cond2 &&
      eq_st_term body1 body2

    | Tm_Par {pre1=preL1; body1=eL1; post1=postL1; pre2=preR1; body2=eR1; post2=postR1 },
      Tm_Par {pre1=preL2; body1=eL2; post1=postL2; pre2=preR2; body2=eR2; post2=postR2 } ->
      eq_tm preL1 preL2 &&
      eq_st_term eL1 eL2 &&
      eq_tm postL1 postL2 &&
      eq_tm preR1 preR2 &&
      eq_st_term eR1 eR2 &&
      eq_tm postR1 postR2

    | Tm_WithLocal { initializer=e1; body=b1 },
      Tm_WithLocal { initializer=e2; body=b2 } ->
      eq_tm e1 e2 &&
      eq_st_term b1 b2

    | Tm_Rewrite { t1=l1; t2=r1 },
      Tm_Rewrite { t1=l2; t2=r2 } ->
      eq_tm l1 l2 &&
      eq_tm r1 r2

    | Tm_Admit { ctag=c1; u=u1; typ=t1; post=post1 }, 
      Tm_Admit { ctag=c2; u=u2; typ=t2; post=post2 } ->
      c1 = c2 &&
      u1 = u2 &&
      eq_tm t1 t2 &&
      eq_tm_opt post1 post2

    | Tm_Protect { t = t1 },
      Tm_Protect { t = t2 } ->
      eq_st_term t1 t2
      
    | _ -> false
