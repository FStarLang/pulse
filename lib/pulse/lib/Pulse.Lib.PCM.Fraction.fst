module Pulse.Lib.PCM.Fraction
open FStar.PCM
open FStar.Real
open PulseCore.FractionalPermission

(* Lifted from Steel.PCMFrac *)
let fractional (a:Type u#a) = option (a & perm)
let composable #a : symrel (fractional a) =
  fun (f0 f1:fractional a) ->
    match f0, f1 with
    | None, _
    | _, None -> True
    | Some (x0, p0), Some (x1, p1) -> x0==x1 /\ (sum_perm p0 p1).v <=. one
let compose #a (f0:fractional a) (f1:fractional a{composable f0 f1}) : fractional a =
  match f0, f1 with
  | None, f
  | f, None -> f
  | Some (x0, p0), Some (_, p1) -> Some (x0, sum_perm p0 p1)

let pcm_frac #a : pcm (fractional a) = {
  p = {
         composable = composable;
         op = compose;
         one = None
      };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun _ -> True)
}

let mk_frame_preserving_upd
  (#a: Type)
  (v0: Ghost.erased a)
  (v1: a)
: Tot (frame_preserving_upd pcm_frac (Some (Ghost.reveal v0, full_perm)) (Some (v1, full_perm)))
= fun _ -> Some (v1, full_perm)

let mk_frame_preserving_upd_none
  (#a: Type)
  (v0: Ghost.erased a)
: Tot (frame_preserving_upd pcm_frac (Some (Ghost.reveal v0, full_perm)) None)
= fun _ -> None

let perm_ok p : prop = (p.v <=. one == true)

let full_values_compatible (#a:Type u#a) (x:a)
: Lemma (compatible pcm_frac (Some (x, full_perm)) (Some (x, full_perm)))
= let v = Some (x, full_perm) in
  assert (FStar.PCM.composable pcm_frac v None)
