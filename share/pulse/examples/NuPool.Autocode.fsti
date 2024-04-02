module NuPool.Autocode

open Pulse.Lib.Pervasives
open Pulse.Lib.Pledge
open Pulse.Lib.Codeable
open NuPool.Code

instance val codeable_base
  (base : vcode)
  (p : vprop)
  (d : codeable base p)
  : codeable (poolcode base) p

instance val codeable_star
  (base : vcode)
  (p q : vprop)
  (d1 : codeable (poolcode base) p)
  (d2 : codeable (poolcode base) q)
  : codeable (poolcode base) (p ** q)

instance val codeable_emp
  (base : vcode)
  : codeable (poolcode base) emp

instance val codeable_joinable
  (base : vcode) (p : pool' base)
  (post : vprop)
  (d : codeable (poolcode base) post)
  (h : handle)
  : codeable (poolcode base) (joinable p post h)

instance val codeable_alive_proxy
  (base : vcode) (p : pool' base)
  (f : perm)
  : codeable (poolcode base) (alive_proxy f p)

instance val codeable_done_proxy
  (base : vcode) (p : pool' base)
  : codeable (poolcode base) (done_proxy p)

instance val codeable_pledge
  (base : vcode)
  (is : inames)
  (pre  : vprop) (d1 : codeable (poolcode base) pre)
  (post : vprop) (d2 : codeable (poolcode base) post)
  : codeable (poolcode base) (pledge is pre post)

instance val codeable_exists
  (base : vcode)
  (ty : Type0)
  (f : ty -> vprop)
  (d : (x:ty -> codeable (poolcode base) (f x)))
  : codeable (poolcode base) (op_exists_Star #ty f)
