module EverCrypt.AutoConfig2
open Pulse.Lib.Pervasives

/// See ANONYMIZED

noextract [@@noextract_to "krml"]
val initialized: slprop

val init: unit -> stt unit
  (requires emp)
  (ensures fun _ -> initialized)
