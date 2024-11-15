open Prims
let rec (while_ : (unit -> Prims.bool) -> (unit -> unit) -> unit) =
  fun cond ->
    fun body ->
      let uu___ = cond () in
      if uu___ then (body (); while_ cond body) else ()
let (par : (unit -> unit) -> (unit -> unit) -> unit) = fun f1 -> fun f2 -> ()
let rec unreachable : 't . unit -> 't = fun uu___ -> unreachable ()