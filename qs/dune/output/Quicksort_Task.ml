open Prims
let p31 : 'uuuuu 'uuuuu1 'uuuuu2 . ('uuuuu * 'uuuuu1 * 'uuuuu2) -> 'uuuuu =
  fun uu___ -> match uu___ with | (x, y, z) -> x
let p32 : 'uuuuu 'uuuuu1 'uuuuu2 . ('uuuuu * 'uuuuu1 * 'uuuuu2) -> 'uuuuu1 =
  fun uu___ -> match uu___ with | (x, y, z) -> y
let p33 : 'uuuuu 'uuuuu1 'uuuuu2 . ('uuuuu * 'uuuuu1 * 'uuuuu2) -> 'uuuuu2 =
  fun uu___ -> match uu___ with | (x, y, z) -> z
let rec (t_quicksort :
  Pulse_Lib_Task.pool ->
    unit -> int array -> int -> int -> unit -> unit -> unit -> unit)
  =
  fun p ->
    fun f ->
      fun a ->
        fun lo ->
          fun hi ->
            fun lb ->
              fun rb ->
                fun s0 ->
                  if lo < (hi - Prims.int_one)
                  then
                    let r = Quicksort_Base.partition_wrapper a lo hi () () () in
                    let pivot = p33 r in
                    (Pulse_Lib_Task.spawn_ p () () ()
                       (fun uu___1 -> t_quicksort p () a lo (p31 r) () () ());
                     t_quicksort p () a (p32 r) hi () () ())
                  else ()
let rec (quicksort :
  Prims.pos -> int array -> int -> int -> unit -> unit -> unit -> unit) =
  fun nthr ->
    fun a ->
      fun lo ->
        fun hi ->
          fun lb ->
            fun rb ->
              fun s0 ->
                let p = Pulse_Lib_Task.setup_pool nthr in
                t_quicksort p () a lo hi () () ();
                Pulse_Lib_Task.await_pool p () () ();
                Pulse_Lib_Task.teardown_pool p