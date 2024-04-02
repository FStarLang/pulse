module Codeable

open Pulse.Lib.Pervasives

noeq
type vcode : Type u#3 = {
    t : Type u#2;
    up : t -> vprop;
}

class codeable (code:vcode) (v : vprop) = {
  code_of : code.t;
  pf : squash (code.up code_of == v);
}

let encode (#code:vcode) (v:vprop) {| d : codeable code v |} : code.t =
  d.code_of

let decode (#code:vcode) (c:code.t) : vprop =
  code.up c
  
let small_code : vcode = {
  t = Pulse.Lib.Core.small_vprop;
  up = Pulse.Lib.Core.up;
}

instance codeable_small (v:vprop) (_ : squash (is_small v)) : codeable small_code v = {
  code_of = down v;
  pf = ();
}
