module PoolCodes

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open FStar.Tactics
open FStar.Preorder
open Pulse.Lib.Par.Pledge
open Pulse.Lib.Trade
module SmallTrade = Pulse.Lib.SmallTrade

noeq
type vcode = {
    t : Type u#2;
    up : t -> vprop;
    emp : (emp:t{up emp == Pulse.Lib.Core.emp});
}

let small_code : vcode = {
  t = small_vprop;
  up = up;
  emp = down emp;
}

class codeable (code:vcode) (v : vprop) = {
  code_of : code.t;
  pf : squash (code.up code_of == v);
}

let encode (#code:vcode) (v:vprop) {| codeable code v |} : code.t = code_of #code #v

instance codeable_emp : codeable small_code emp = {
  code_of = small_code.emp;
  pf = ();
}

instance codeable_star (p q : vprop)
         (d1 : codeable small_code p) 
         (d2 : codeable small_code q) 
: codeable small_code (p ** q) = {
  code_of = down (p ** q);
  pf = (admit(); small_star p q);
  // We need some more properties about down/up to prove this.
  // I think a way forward is having:
  //  val small_vprop_star : small_vprop -> small_vprop -> small_vprop
  // with
  //  val lemma (p q : small_vprop) : Lemma (up (small_vprop_star p q) == up p ** up q)
  // then define
  //
  //  code_of = small_vprop_star (encode p) (encode q)
  //  pf = lemma p q
}

#set-options "--print_universes"

assume val pool : Type0
assume val handle : Type0
assume val joinable : pool -> vprop -> handle -> vprop

noeq
type poolcode_t =
  | Small : small_vprop -> poolcode_t
  | Star  : poolcode_t -> poolcode_t -> poolcode_t
  | Emp   : poolcode_t
  | J : pool -> poolcode_t -> handle -> poolcode_t
  | E0 : u:Type0 -> (p : u -> poolcode_t) -> poolcode_t

let rec poolcode_up (c : poolcode_t) : vprop =
  match c with
  | Small v -> up v
  | Star p q -> poolcode_up p ** poolcode_up q
  | Emp -> emp
  | J p post h -> joinable p (poolcode_up post) h
  | E0 u p -> exists* (w:u). poolcode_up (p w)

let poolcode : vcode = {
  t = poolcode_t;
  up = poolcode_up;
  emp = Emp;
}

// FIXME: this file relies on this instance being here in order to apply last
// We need priorities or something similar.
instance codeable_small (v:vprop{is_small v}) : codeable poolcode v = {
  code_of = Small (down v);
  pf = ();
}

instance codeable_joinable (p:_) (post:_) (h:_) (d : codeable poolcode post)
: codeable poolcode (joinable p post h)
= {
  code_of = J p d.code_of h;
  pf = ();
}

instance codeable_exists (u:Type0) (pred : u -> vprop)
    (d : (x:u -> codeable poolcode (pred x)))
: codeable poolcode (exists* (w:u). pred w)
= {
  code_of = E0 u (fun w -> (d w).code_of);
  pf = admit();
}

instance codeable_star2 (p q : vprop)
  (dp : codeable poolcode p)
  (dq : codeable poolcode q)
: codeable poolcode (p ** q) = {
  code_of = Star dp.code_of dq.code_of;
  pf = ();
}

let test (p q r : vprop) 
  (d1 : codeable poolcode p)
  (d2 : codeable poolcode q)
  (pp : pool) (h : handle)
  (d3 : codeable poolcode r)
 : codeable poolcode (p ** joinable pp (joinable pp q h) h)
 = FStar.Tactics.Typeclasses.solve
