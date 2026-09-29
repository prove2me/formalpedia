-- Prove2me | solution 1 for ThreeCubes.repCount_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:02:32.607426+00:00
-- url     : https://prove2.me/submissions/47d694c1-5a5e-4e1a-abe9-abf2bc7539f2

-- Sol generated from Probability/LowerBounds.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Definitions.Def_Probability_Density
import Definitions.Def_Probability_LowerBounds
import Definitions.Def_Probability_Rational
import Theorems.Thm_ThreeCubes_cube_pair_inj
import Theorems.Thm_ThreeCubes_le_of_mem_cubeValues

/-!
# Unconditional lower bounds for sums of three cubes

`Probability.ThreeCubes.Density` gives the *upper* bound: at most `7/9` of all integers are
sums of three cubes (`ThreeCubes.card_isSumOfThreeCubes_le`), and
`ThreeCubes.densitySevenNinths_iff_hasse` shows that the matching lower bound — i.e. density
exactly `7/9` — is *equivalent* to the Hasse principle for the affine cubic surface, hence
completely out of reach at present.

This file proves the strongest lower bound that is unconditional, namely a power-saving one.
Counting the values `k³ + m³` with `K³ ≤ k < 2K³` and `0 ≤ m ≤ K²`, the "small" cube `m³` is
always smaller than the gap `(k+1)³ - k³ = 3k² + 3k + 1`, so `k` is recoverable from the value
as `⌊n^{1/3}⌋` and the parametrisation is *injective*
(`ThreeCubes.cube_pair_inj`).  This produces `K³(K²+1)` distinct representable integers below
`9K⁹`, i.e.

* `ThreeCubes.repCount_ge` : `K⁵ ≤ repCount (9K⁹)`, an `≫ N^{5/9}` lower bound for the
  counting function `repCount N = #{n ≤ N : n is a sum of three cubes}`.

The exponent `5/9` is exactly the classical elementary bound: `3/9` comes from the cubes
themselves and the extra `2/9` from the `k^{2/3}`-many admissible small cubes.  Any improvement
beyond the trivial multiplicativity of this construction requires genuine control of the
representation multiplicity, which is the content of Conjecture 3 of `FUTURE_DIRECTIONS.md`.

The last section records the sharp contrast with the *rational* problem: four rational cubes
always suffice, by a one-line identity (`ThreeCubes.isSumOfFourRationalCubes`), whereas over
`ℤ` the analogous statement for four cubes is open.
-/

open ThreeCubes

open Finset

/-! ### An injective two-parameter family of sums of two cubes -/




/-- The family is injective, so it has exactly `K³(K²+1)` elements. -/
theorem card_cubeValues (K : ℕ) : (cubeValues K).card = K ^ 3 * (K ^ 2 + 1) := by
  rw [cubeValues, Finset.card_image_of_injOn, Finset.card_product, Finset.card_range,
    Nat.card_Ico]
  · congr 1
    omega
  · rintro ⟨k, m⟩ hp ⟨k', m'⟩ hq h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe,
      Finset.mem_Ico, Finset.mem_range] at hp hq
    have h' : k ^ 3 + m ^ 3 = k' ^ 3 + m' ^ 3 := h
    obtain ⟨hk, hm⟩ := cube_pair_inj hp.1.1 (by omega) hq.1.1 (by omega) h'
    simp [hk, hm]

/-- Every element of `cubeValues K` is a sum of three cubes (the third one being `0`). -/
theorem isSumOfThreeCubes_of_mem_cubeValues {K n : ℕ} (h : n ∈ cubeValues K) :
    IsSumOfThreeCubes (n : ℤ) := by
  rw [cubeValues, Finset.mem_image] at h
  obtain ⟨⟨k, m⟩, -, rfl⟩ := h
  exact ⟨(k : ℤ), (m : ℤ), 0, by push_cast; ring⟩







/-! ### Four rational cubes always suffice -/




open ThreeCubes in
open scoped Classical in
theorem solution(K : ℕ) : K ^ 5 ≤ repCount (9 * K ^ 9) := by
  have hsub : cubeValues K ⊆
      Finset.filter (fun i : ℕ => IsSumOfThreeCubes (i : ℤ)) (Finset.range (9 * K ^ 9 + 1)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := le_of_mem_cubeValues hn; omega,
      isSumOfThreeCubes_of_mem_cubeValues hn⟩
  have hcard := Finset.card_le_card hsub
  rw [card_cubeValues] at hcard
  rw [repCount]
  have h5 : K ^ 5 ≤ K ^ 3 * (K ^ 2 + 1) := by
    have : K ^ 3 * (K ^ 2 + 1) = K ^ 5 + K ^ 3 := by ring
    omega
  exact le_trans h5 hcard
