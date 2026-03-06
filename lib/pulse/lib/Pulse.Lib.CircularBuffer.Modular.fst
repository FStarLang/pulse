module Pulse.Lib.CircularBuffer.Modular

/// Modular/circular indexing lemmas for circular buffer operations.
/// All lemmas are pure, no Pulse dependency.

module ML = FStar.Math.Lemmas

/// Circular index is always in bounds
let circular_index_in_bounds (read_start:nat) (offset:nat) (cap:pos)
  : Lemma (ensures (read_start + offset) % cap < cap)
  = ML.lemma_mod_lt (read_start + offset) cap

/// Two different offsets within capacity map to different circular indices
let circular_index_injective (read_start:nat) (o1 o2:nat) (cap:pos)
  : Lemma (requires o1 < cap /\ o2 < cap /\ o1 <> o2)
          (ensures (read_start + o1) % cap <> (read_start + o2) % cap)
  = // (read_start + o1) % cap = (read_start % cap + o1) % cap (and same for o2)
    ML.lemma_mod_plus_distr_l read_start o1 cap;
    ML.lemma_mod_plus_distr_l read_start o2 cap;
    let r = read_start % cap in
    // Now we need (r + o1) % cap <> (r + o2) % cap
    // Since |o1 - o2| < cap, and r < cap, the difference (r+o1) - (r+o2) = o1 - o2
    // has absolute value < cap, so they can't be equal mod cap unless o1 = o2
    assert (r < cap);
    if (r + o1) % cap = (r + o2) % cap then begin
      // Derive contradiction: supposing equal, then o1 - o2 is divisible by cap
      // But |o1 - o2| < cap, so o1 = o2. Contradiction.
      ML.lemma_mod_plus_distr_l r o1 cap;
      ML.lemma_mod_plus_distr_l r o2 cap
    end else ()

/// Advancing read_start by n (mod cap) is equivalent to adding n to circular index
let advance_read_start (read_start:nat) (n:nat) (offset:nat) (cap:pos)
  : Lemma (requires read_start < cap)
          (ensures (
            let new_start = (read_start + n) % cap in
            (new_start + offset) % cap == (read_start + n + offset) % cap))
  = let new_start = (read_start + n) % cap in
    ML.lemma_mod_plus_distr_l (read_start + n) offset cap;
    ML.lemma_mod_plus_distr_l new_start offset cap
