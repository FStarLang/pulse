module NuPool.Autocode

open Pulse.Lib.Pervasives
open Pulse.Lib.Pledge
open Pulse.Lib.Codeable
module T = FStar.Tactics.V2
open NuPool.Code
open FStar.FunctionalExtensionality

instance codeable_base
  (base:vcode)
  (p : vprop)
  (d : codeable base p)
  : codeable (poolcode base) p = {
    code_of = Base (encode p);
    pf = ();
  }

instance codeable_star
  (base:vcode)
  (p q : vprop)
  (d1 : codeable (poolcode base) p)
  (d2 : codeable (poolcode base) q)
  : codeable (poolcode base) (p ** q) = {
    // FIXME: if the encodes below are not fully annotated, clients of this
    // module will fail when lax-typechecking this interface. why???
    code_of = Star (encode #(poolcode base) p <: (poolcode base).t)
                   (encode #(poolcode base) q <: (poolcode base).t);
    pf = ();
  }

instance codeable_emp
  (base:vcode)
  : codeable (poolcode base) emp = {
    code_of = Emp;
    pf = ();
  }

instance codeable_joinable
  (base : vcode) (p : pool' base)
  (post : vprop)
  (d : codeable (poolcode base) post)
  (h : handle)
  : codeable (poolcode base) (joinable p post h) = {
    code_of = J p.p (encode post <: (poolcode base).t) h;
    pf = ();
  }

instance codeable_alive_proxy
  (base:vcode) (p : pool' base)
  (f : perm)
  : codeable (poolcode base) (alive_proxy f p) = {
    code_of = Alive f p.p;
    pf = ();
}

instance codeable_done_proxy
  (base:vcode) (p : pool' base)
  : codeable (poolcode base) (done_proxy p) = {
    code_of = Done p.p;
    pf = ();
}

instance codeable_pledge
  (base : vcode)
  (is : inames)
  (pre  : vprop) (d1 : codeable (poolcode base) pre)
  (post : vprop) (d2 : codeable (poolcode base) post)
  : codeable (poolcode base) (pledge is pre post) = {
    code_of = Pledge is (encode pre <: (poolcode base).t) (encode post <: (poolcode base).t);
    pf = ();
  }

// This should be provable from the model.
let exists_feq (#a:Type) (f1 f2 : a -> vprop) :
  Lemma (requires feq f1 f2)
        (ensures op_exists_Star f1 == op_exists_Star f2)
  = let aux (x:a) : Lemma (ensures vprop_equiv (f1 x) (f2 x)) =
      Squash.return_squash (vprop_equiv_refl (f1 x))
    in
    Classical.forall_intro aux;
    elim_vprop_equiv <| vprop_equiv_exists f1 f2 ()

instance codeable_exists
  (base:vcode)
  (ty : Type0)
  (f : ty -> vprop)
  (d : (x:ty -> codeable (poolcode base) (f x)))
  : codeable (poolcode base) (op_exists_Star #ty f) = {
    code_of = Ex0 ty (fun x -> encode (f x) #(d x));
    pf = (
      assert_norm (
        poolcode_up base (Ex0 ty (fun x -> encode (f x) #(d x)))
        ==
        op_exists_Star #ty (fun x -> poolcode_up base (encode (f x) #(d x)))
      );
      exists_feq #ty (fun x -> poolcode_up base (encode (f x) #(d x))) f
    );
  }


let test0 (base:vcode) (p : vprop) (d : codeable (poolcode base) p) : (poolcode base).t =
  encode (p ** p ** pledge emp_inames p p)

let test1 (base:vcode)
  (p : vprop) (_ : codeable (poolcode base) p)
  : (poolcode base).t
=
  encode (exists* (x:int). p)

let test2 (base:vcode)
  (p : vprop) (_ : codeable (poolcode base) p)
  (q : vprop) (_ : codeable (poolcode base) q)
  : (poolcode base).t
=
  encode (p ** q ** (exists* (x:int). pledge emp_inames p q))

let test3
  (base : vcode) (p : pool' base)
  : (poolcode base).t
=
  encode (alive_proxy 0.5R p)

// let test4
//   (p : pool)
//   (q : vprop) (_ : codeable (poolcode p.base) q)
//   (h : handle)
//   : (poolcode p.base).t
// =
//   let _ = encode (joinable p q h) in
//   let _ = encode (pool_done p) in
//   admit()


