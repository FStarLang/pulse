open Prims
type 'n nat_smaller = int
type ('s, 'lb) larger_than = unit
type ('s, 'rb) smaller_than = unit
type ('s, 'lb, 'rb) between_bounds = unit
type 's sorted = unit
let (to_nat : int -> int) = fun x -> x
type ('s1, 's2) permutation = unit
let op_Array_Access :
  't . 't array -> int -> int -> int -> unit -> unit -> 't =
  fun a -> fun i -> fun l -> fun r -> fun s -> fun p -> Array.get a i
let op_Array_Assignment :
  't . 't array -> int -> 't -> int -> int -> unit -> unit =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun a ->
                 fun i ->
                   fun v ->
                     fun l -> fun r -> fun s0 -> Obj.magic (Array.set a i v))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let rec (swap : int array -> int -> int -> int -> int -> unit -> unit) =
  fun a ->
    fun i ->
      fun j ->
        fun l ->
          fun r ->
            fun s0 ->
              let vi = op_Array_Access a i l r () () in
              let vj = op_Array_Access a j l r () () in
              op_Array_Assignment a i vj l r ();
              op_Array_Assignment a j vi l r ()
let rec (partition :
  int array -> int -> int -> unit -> unit -> unit -> (int * int * int)) =
  fun a ->
    fun lo ->
      fun hi ->
        fun lb ->
          fun rb ->
            fun s0 ->
              let pivot = op_Array_Access a (hi - Prims.int_one) lo hi () () in
              let i = Obj.magic (ref lo) in
              let j = Obj.magic (ref lo) in
              let k = Obj.magic (ref lo) in
              Pulse_Lib_Dv.while_
                (fun while_cond -> let vk = !k in vk < (hi - Prims.int_one))
                (fun while_body ->
                   let vk = !k in
                   let ak = op_Array_Access a vk lo hi () () in
                   if ak < pivot
                   then
                     let vi = !i in
                     let vj = !j in
                     (swap a vj vk lo hi ();
                      swap a vi vj lo hi ();
                      Obj.magic ((:=) i (vi + Prims.int_one));
                      Obj.magic ((:=) j (vj + Prims.int_one));
                      Obj.magic ((:=) k (vk + Prims.int_one)))
                   else
                     if ak = pivot
                     then
                       (let vj = !j in
                        swap a vj vk lo hi ();
                        Obj.magic ((:=) j (vj + Prims.int_one));
                        Obj.magic ((:=) k (vk + Prims.int_one)))
                     else Obj.magic ((:=) k (vk + Prims.int_one)));
              (let vi = !i in
               let vj = !j in
               let vj' = vj + Prims.int_one in
               swap a vj (hi - Prims.int_one) lo hi ();
               (let k1 = (vi, vj', pivot) in let j1 = k1 in let i1 = j1 in i1))
let rec (partition_wrapper :
  int array -> int -> int -> unit -> unit -> unit -> (int * int * int)) =
  fun a ->
    fun lo ->
      fun hi ->
        fun lb -> fun rb -> fun s0 -> let r = partition a lo hi () () () in r
type ('a, 'lo, 'hi, 'lb, 'rb, 's0) pure_pre_quicksort = unit
type ('a, 'lo, 'hi, 'lb, 'rb, 's0, 's) pure_post_quicksort = unit