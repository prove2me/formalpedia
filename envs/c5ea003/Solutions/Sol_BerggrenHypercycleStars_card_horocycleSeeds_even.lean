-- Prove2me | solution 1 for BerggrenHypercycleStars.card_horocycleSeeds_even
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:29:49.753411+00:00
-- url     : https://prove2.me/submissions/077eacbb-8457-4e85-a5f0-f34108c8993b

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
theorem solution(m : ℕ) (hm : m % 2 = 0) :
    (horocycleSeeds m).card = Nat.totient m := by
  classical
  rw [Nat.totient_eq_card_coprime]
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro n _
  constructor
  · rintro ⟨hcop, -⟩; exact hcop
  · intro hcop
    refine ⟨hcop, ?_⟩
    -- `m` even and `gcd m n = 1` force `n` odd
    rcases Nat.even_or_odd n with hn | hn
    · exfalso
      obtain ⟨k, hk⟩ := hn
      obtain ⟨j, hj⟩ : ∃ j, m = 2 * j := ⟨m / 2, by omega⟩
      have h2 : 2 ∣ Nat.gcd m n := Nat.dvd_gcd ⟨j, hj⟩ ⟨k, by omega⟩
      rw [Nat.Coprime] at hcop
      omega
    · obtain ⟨k, hk⟩ := hn
      omega
