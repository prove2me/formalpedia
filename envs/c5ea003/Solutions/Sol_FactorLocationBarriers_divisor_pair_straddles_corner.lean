-- Prove2me | solution 1 for FactorLocationBarriers.divisor_pair_straddles_corner
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:55:31.790222+00:00
-- url     : https://prove2.me/submissions/3e841f8b-b2e5-465d-a663-b2361ed01e4d

-- Sol generated from Tropical/FactorLocationBarriers.lean
import Mathlib
import Definitions.Def_Tropical_FactorLocationBarriers

/-!
# Counting is free, locating is hard: the semiprime witness barriers

This file formalises the arithmetic core of the round-4 closures `HOLOG-MARGIN`,
`SPARSEREC`, `MPS-PARENT` and `OPO-FAC`. All four hypotheses proposed an exotic
resource (holographic partition functions, compressed sensing, tensor-network
ground states, optical Ising machines) for factoring a semiprime `N = p q`, and
all four were closed by the same structural fact, which we prove here:

* the *counting* data attached to `N` (number of divisor pairs = partition
  function `Z = τ(N) = 4`) is **constant across all semiprimes**, hence carries
  zero information (`card_divisors_semiprime`, `tau_cannot_locate`);
* the *witness* data is a 2-spike vector: exactly two divisors lie in the search
  window `[1, √N]`, namely `1` and `p` (`divisors_below_corner`), so the search
  space that must be aggregated has size `√N` with exactly one nontrivial hit
  (`nontrivial_witness_below_corner`);
* the ground space of the tensor-network / Ising energy `E(a,b) = (N - ab)²` is
  the four-point divisor set `{(1,N),(p,q),(q,p),(N,1)}` with no intermediate
  structure (`energyGroundSet_eq`, `energyGroundSet_ncard`), so descent has no
  gradient and random search succeeds with density `4/N²`.

The min-plus (tropical) thread: in logarithmic coordinates the divisor hyperbola
`x · y = N` is the tropical line `X ⊙ Y = N`, whose corner is at `√N`; every
divisor pair straddles that corner (`divisor_pair_straddles_corner`). The
"free witness aggregation" barrier is precisely the statement that locating the
unique nontrivial lattice point on one side of the corner costs the whole
window.
-/

open FactorLocationBarriers

/-! ## 1. The divisor set of a semiprime -/




/-! ## 2. The tropical corner: every divisor pair straddles `√N` -/


/-! ## 3. SPARSEREC: the witness vector is a 2-spike -/




/-! ## 4. MPS-PARENT / OPO-FAC: the ground space is a four-point delta -/








open FactorLocationBarriers in
theorem solution(N d : ℕ) (hN : N ≠ 0) (hd : d ∣ N) :
    min d (N / d) ≤ Nat.sqrt N ∧ Nat.sqrt N ≤ max d (N / d) := by
  obtain ⟨e, he⟩ := hd
  have hd0 : d ≠ 0 := by rintro rfl; simp at he; exact hN he
  have hde : N / d = e := by rw [he]; exact Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero hd0)
  rw [hde]
  have key : ∀ u v : ℕ, N = u * v → u ≤ v → u ≤ Nat.sqrt N ∧ Nat.sqrt N ≤ v := by
    intro u v huv hle
    constructor
    · exact Nat.le_sqrt.mpr (by nlinarith [huv])
    · calc Nat.sqrt N ≤ Nat.sqrt (v * v) := Nat.sqrt_le_sqrt (by nlinarith [huv])
        _ = v := by simp
  rcases le_total d e with h | h
  · have := key d e he h
    simpa [min_eq_left h, max_eq_right h] using this
  · have := key e d (by rw [he]; ring) h
    simpa [min_eq_right h, max_eq_left h] using this
