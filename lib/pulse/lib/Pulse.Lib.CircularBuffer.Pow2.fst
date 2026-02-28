module Pulse.Lib.CircularBuffer.Pow2

/// Power-of-2 arithmetic and doubling reachability lemmas.
/// Used by the circular buffer resize logic.

module ML = FStar.Math.Lemmas

/// Recursive definition: n is a power of 2
let rec is_pow2 (n:pos) : Tot bool (decreases n) =
  if n = 1 then true
  else if n % 2 <> 0 then false
  else is_pow2 (n / 2)

/// Doubling a power of 2 yields a power of 2
let rec doubling_stays_pow2 (n:pos)
  : Lemma (requires is_pow2 n)
          (ensures is_pow2 (n + n))
          (decreases n)
  = if n = 1 then ()
    else begin
      doubling_stays_pow2 (n / 2)
    end

/// Helper: if pow2 a < pow2 b, then 2*a ≤ b
let rec pow2_double_le (a:pos) (b:pos)
  : Lemma (requires is_pow2 a /\ is_pow2 b /\ a < b)
          (ensures a + a <= b)
          (decreases b)
  = if a = 1 then ()
    else begin
      // a >= 2 so a % 2 = 0, and b > a >= 2 so b % 2 = 0  
      pow2_double_le (a / 2) (b / 2)
    end

/// Full reachability: repeated doubling from start reaches some pow2 in [target, vlen]
let rec doubling_reaches_in_range (start:pos) (vlen:pos) (target:pos)
  : Lemma (requires
      is_pow2 start /\
      is_pow2 vlen /\
      start <= vlen /\
      target <= vlen /\
      target > 0)
    (ensures (exists (reached:pos).
      is_pow2 reached /\
      reached >= target /\
      reached <= vlen))
    (decreases (vlen - start))
  = if start >= target then ()
    else begin
      doubling_stays_pow2 start;
      pow2_double_le start vlen;
      doubling_reaches_in_range (start + start) vlen target
    end

/// Compute the smallest power-of-2 >= needed, by doubling base
let rec next_pow2_ge (base: pos) (needed: pos)
  : Pure pos
    (requires is_pow2 base)
    (ensures fun r -> is_pow2 r /\ r >= needed /\ r >= base)
    (decreases (if base >= needed then 0 else needed - base))
  = if base >= needed then base
    else begin
      doubling_stays_pow2 base;
      next_pow2_ge (base + base) needed
    end

/// next_pow2_ge never exceeds a power-of-2 bound that is >= both base and needed
let rec next_pow2_ge_le_bound (al: pos) (needed: pos) (bound: pos)
  : Lemma (requires is_pow2 al /\ is_pow2 bound /\ al <= bound /\ needed <= bound)
          (ensures next_pow2_ge al needed <= bound)
          (decreases (if al >= needed then 0 else needed - al))
  = if al >= needed then ()
    else begin
      doubling_stays_pow2 al;
      pow2_double_le al bound;
      next_pow2_ge_le_bound (al + al) needed bound
    end
