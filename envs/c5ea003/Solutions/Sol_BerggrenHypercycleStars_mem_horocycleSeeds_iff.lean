-- Prove2me | solution 1 for BerggrenHypercycleStars.mem_horocycleSeeds_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:37:33.475158+00:00
-- url     : https://prove2.me/submissions/5d0091b5-ef48-4945-ba63-2d7624dfb80f

-- Sol generated from Cryptography/BerggrenStars/HorocycleCensus.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HorocycleCensus
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars

/-!
# The curves of the Berggren picture: horocycle census

Besides the *stars* of hypercycles studied in `Cryptography.BerggrenStars.HypercycleStars`,
a picture of the Berggren tree embedded in the Poincaré half-plane by `z(m,n) = (n+i)/m` shows a
second family of curves: the **horizontal lines**, which are the horocycles based at the boundary
point `∞`. The nodes at height `1/m` are exactly the Euclid seeds with first coordinate `m`.

## Main results

* `card_horocycleSeeds_even`, `card_horocycleSeeds_odd` : an exact census of each horocycle.
  The horocycle at height `1/m` carries exactly `φ(m)` nodes when `m` is even, and exactly
  `φ(m)/2` nodes when `m` is odd — Euler's totient is the *occupation number* of the horocycle.
* `horocycleSeeds_nonempty` : every horocycle at height `1/m` with `m ≥ 2` is occupied.
* `horocycle_pairwise_separated` : the nodes on one horocycle are uniformly separated, at
  pairwise hyperbolic distance at least `arcosh (3/2)`, however deep in the tree they lie. So
  the horizontal curves of the picture are *uniformly discrete* point sets, in sharp contrast
  with the hypercycle rays, along which the nodes accumulate (`step_along_spoke_tendsto_zero`).
-/

open BerggrenHypercycleStars

open Real UpperHalfPlane








open BerggrenHypercycleStars in
theorem solution(m n : ℕ) (hm : 2 ≤ m) :
    n ∈ horocycleSeeds m ↔ IsSeed m n := by
  rw [horocycleSeeds, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, hcop, hpar⟩
    refine ⟨?_, hlt, hcop, hpar⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [Nat.Coprime, Nat.gcd_zero_right] at hcop
      omega
    · exact hn
  · rintro ⟨-, hlt, hcop, hpar⟩
    exact ⟨hlt, hcop, hpar⟩
