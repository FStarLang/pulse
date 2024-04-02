module NuPool.Autocode

open Pulse.Lib.Pervasives
open Pulse.Lib.Par.Pledge
open Codeable
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

(*
// Here post is a code instead of a vprop
instance codeable_joinable
  (p : pool)
  (post : poolcode_t p.base.t)
  (h : handle)
  : codeable (poolcode p.base) (joinable p post h) = { 
    code_of = J p.p post h;
    pf = ();
  }
  *)

instance codeable_joinable
  (p : pool)
  (post : vprop)
  (d : codeable (poolcode p.base) post)
  (h : handle)
  : codeable (poolcode p.base) (joinable p post h) = { 
    code_of = J p.p (encode post <: (poolcode p.base).t) h;
    pf = ();
  }

instance codeable_pledge
  (p : pool)
  (pre  : vprop) (d1 : codeable (poolcode p.base) pre)
  (post : vprop) (d2 : codeable (poolcode p.base) post)
  : codeable (poolcode p.base) (pledge [] pre post) = { 
    code_of = Pl (encode pre <: (poolcode p.base).t) (encode post <: (poolcode p.base).t);
    pf = ();
  }

let exists_lem 
  (p : pool)
  (ty : Type0)
  (f : ty ^-> poolcode_t p.base.t)
  : Lemma (ensures poolcode_up p.base (Ex0 ty f) == op_exists_Star #ty (on ty (fun (x:ty) -> poolcode_up p.base (f x))))
  = admit()

instance codeable_exists
  (p : pool)
  (ty : Type0)
  (f : ty ^-> vprop)
  (d : (x:ty -> codeable (poolcode p.base) (f x)))
  : codeable (poolcode p.base) (op_exists_Star #ty f) = { 
    code_of = Ex0 ty (on ty <| (fun x -> encode (f x) #(d x)));
    pf = (
      // TODO: remove the asserts once this stabilizes
      exists_lem p ty (on ty (fun x -> encode (f x) #(d x)));
      assert (poolcode_up p.base (Ex0 ty (on ty (fun x -> encode (f x) #(d x))))
              == op_exists_Star #ty (on ty (fun x -> poolcode_up p.base (encode (f x) #(d x)))));

      assert (feq (fun x -> poolcode_up p.base (encode (f x) #(d x))) f);
      assert (on ty (fun x -> poolcode_up p.base (encode (f x) #(d x))) == on ty f);
      assert (on ty f == f);
      FStar.FunctionalExtensionality.extensionality ty _ (fun x -> poolcode_up p.base (encode (f x) #(d x))) f;
      assert (on ty (fun x -> poolcode_up p.base (encode (f x) #(d x))) == f);
      assert (op_exists_Star #ty (on ty (fun x -> poolcode_up p.base (encode (f x) #(d x))))
           == op_exists_Star #ty f);
      ()
    );
  }
