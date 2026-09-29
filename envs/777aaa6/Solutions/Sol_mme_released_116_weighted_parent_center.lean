-- Prove2me | solution 1 for mme_released_116_weighted_parent_center
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:13:05.873991+00:00
-- url     : https://prove2.me/submissions/90456b6a-5c9c-4354-91da-0e3aec6898e2

import Definitions.Def_mme_released_116_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ MME.CompleteSplit
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
theorem mme_released_116_integer_profile_frequency
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

/-- The parent mixture built from the integer profiles is exactly the
region's alpha-weighted product of its two seed child marginals. -/
theorem mme_released_116_integer_parent_mixture
    (i : Fin 3) (r : Fin 6) (w : Fin 2 → CompleteWord 2) :
    RegionRealization.parentMixture parent_total regionalSize splitCount
      (integerProfile i) r w =
      ∑ c : Split, ((splitWeight r c : ℝ) / denominator) *
        ((childMarginal r c i (w 0) : ℝ) / denominator) *
        ((childMarginal r (complement (parent_total r) c) i (w 1) : ℝ) /
          denominator) := by
  unfold RegionRealization.parentMixture
  simp_rw [mme_released_116_integer_profile_frequency]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  have hweight : (seed.region.getD r.val 0 : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt
      ((by decide +kernel : ∀ r : Fin 6, 0 < seed.region.getD r.val 0) r))
  have hd : (denominator : ℝ) ≠ 0 := by norm_num [denominator]
  dsimp [splitCount, regionalSize]
  push_cast
  field_simp
  simp [parent]

/-- Projecting the released joint row to one mode equals the sum of the
six regional products, before dividing by the common denominator d^4. -/
theorem mme_released_116_aggregate_parent_counts :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      ((ReleasedGlobal.jointRows 0 10).map
        (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
      ∑ r : Fin 6, seed.region.getD r.val 0 *
        ∑ c : Released116.Split, splitWeight r c *
          childMarginal r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
          childMarginal r (complement (parent_total r) c) i
            ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

/-- The released full-word frequency is the weighted mean of the six
parent mixtures constructed from the concrete integer profiles. -/
theorem solution
    (i : Fin 3) (w : CompleteWord 3) :
    (∑ r : Fin 6, ((regionalSize r : ℝ) / (denominator : ℝ) ^ 4) *
      RegionRealization.parentMixture parent_total regionalSize splitCount
        (integerProfile i) r
        ![((completeWordSplitEquiv 2 (by decide)) w).1,
          ((completeWordSplitEquiv 2 (by decide)) w).2]) =
      ((((ReleasedGlobal.jointRows 0 10).map
        (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
        (denominator : ℝ) ^ 4 := by
  rw [mme_released_116_aggregate_parent_counts i w]
  simp_rw [mme_released_116_integer_parent_mixture]
  simp only [Nat.cast_sum, Nat.cast_mul]
  simp_rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro c _
  dsimp [regionalSize]
  push_cast
  have hd : (denominator : ℝ) ≠ 0 := by norm_num [denominator]
  field_simp

#print axioms solution
