-- Prove2me | solution 1 for mme_released_116_integer_profile_frequency
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:08:34.172469+00:00
-- url     : https://prove2.me/submissions/820df373-604a-4f87-b766-06fa407dfbee

import Definitions.Def_mme_released_116_integer_profiles
open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed MME.RecursiveYZ MME.CompleteSplit
set_option autoImplicit false

/-- Every region has the prescribed positive number of parent occurrences. -/
theorem mme_released_116_regional_split_mass :
    ∀ r : Fin 6, 0 < regionalSize r ∧ ∑ c : Split, splitCount r c = regionalSize r := by
  decide +kernel

/-- The child profile has exactly one count for each physical occurrence of
its split or its complementary split. -/
theorem mme_released_116_integer_profile_mass :
    ∀ (i : Fin 3) (c : Cell 4 6 parent),
      ∑ w, integerProfile i c w =
        splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2) := by
  decide +kernel

/-- Positive child counts have the grade required by the integer-step interface. -/
theorem mme_released_116_integer_profile_support :
    ∀ (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteWord 2),
      0 < integerProfile i c w → ∑ h, (w h).val = (c.2.val i).val := by
  decide +kernel

/-- The three forced CW boundary reversals hold for the concrete child profiles. -/
theorem mme_released_116_integer_profile_boundary : BoundaryProfiles integerProfile := by
  unfold BoundaryProfiles
  decide +kernel

/-- The six regions exhaust the released joint-row scale. -/
theorem mme_released_116_regional_total :
    ∑ r, regionalSize r = denominator ^ 4 := by
  decide +kernel

/-- Normalization removes the integer scale and both complementary split
weights, leaving the seed's own child marginal. -/
theorem solution
    (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteWord 2) :
    RegionRealization.cellFrequency (integerProfile i) c w =
      (childMarginal c.1 c.2 i w : ℝ) / denominator := by
  let K := seed.region.getD c.1.val 0 *
    (splitWeight c.1 c.2 + splitWeight c.1 (complement (parent_total c.1) c.2)) *
    denominator
  have hpos : 0 < K := by
    exact (by decide +kernel : ∀ c : Cell 4 6 parent,
      0 < seed.region.getD c.1.val 0 *
        (splitWeight c.1 c.2 + splitWeight c.1 (complement (parent_total c.1) c.2)) *
        denominator) c
  have hmass : ∑ v, integerProfile i c v = K * denominator := by
    rw [mme_released_116_integer_profile_mass]
    dsimp [splitCount, K]
    ring
  unfold RegionRealization.cellFrequency
  rw [hmass]
  change ((K * childMarginal c.1 c.2 i w : ℕ) : ℝ) /
    ((K * denominator : ℕ) : ℝ) = _
  simp only [Nat.cast_mul]
  exact mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos))


#print axioms solution
