-- Prove2me | solution 1 for FactorLocationBarriers.divisors_below_corner
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:56:53.729716+00:00
-- url     : https://prove2.me/submissions/5180e399-3ef7-490b-bc76-4e05eb304791

-- Sol generated from Tropical/FactorLocationBarriers.lean
import Mathlib
import Definitions.Def_Tropical_FactorLocationBarriers
import Theorems.Thm_FactorLocationBarriers_divisors_semiprime

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
theorem solution(p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    (p * q).divisors.filter (fun d => d * d ≤ p * q) = {1, p} := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  ext d
  simp only [Finset.mem_filter, divisors_semiprime p q hp hq, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨h | h | h | h, hle⟩ <;> subst h
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hle (by nlinarith)
    · have h4 : 4 ≤ p * q := by nlinarith
      exact absurd hle (by nlinarith)
  · rintro (h | h) <;> subst h
    · exact ⟨Or.inl rfl, by nlinarith⟩
    · exact ⟨Or.inr (Or.inl rfl), by nlinarith⟩
