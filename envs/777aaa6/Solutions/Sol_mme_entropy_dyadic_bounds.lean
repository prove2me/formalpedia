-- Prove2me | solution 1 for mme_entropy_dyadic_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:55:55.301983+00:00
-- url     : https://prove2.me/submissions/0466ebba-c543-4ab1-8c88-034192166f4b

import Theorems.Thm_mme_dyadic_neg_log_bounds
import Definitions.Def_mme_regional_entropy_rate_data

open scoped BigOperators
open MME.RegionRate

/-- Atomwise dyadic logarithm estimates give finite entropy bounds using
only arithmetic and inverses. Zero atoms are included without special data. -/
theorem solution {W : Type*} [Fintype W]
    (p : W → ℝ) (hp : ∀ w, 0 ≤ p w) (k : W → ℕ) :
    (∑ w, p w * ((k w : ℝ) * (693147180 / 1000000000 : ℝ) + 1 -
      2 ^ k w * p w)) ≤ entropy p ∧
    entropy p ≤ ∑ w, p w * ((k w : ℝ) * (693147181 / 1000000000 : ℝ) - 1 +
      (2 ^ k w * p w)⁻¹) := by
  have hterm (w : W) :
      p w * ((k w : ℝ) * (693147180 / 1000000000 : ℝ) + 1 - 2 ^ k w * p w) ≤
        Real.negMulLog (p w) ∧
      Real.negMulLog (p w) ≤
        p w * ((k w : ℝ) * (693147181 / 1000000000 : ℝ) - 1 +
          (2 ^ k w * p w)⁻¹) := by
    by_cases hz : p w = 0
    · simp [hz]
    · have hx : 0 < p w := lt_of_le_of_ne (hp w) (Ne.symm hz)
      obtain ⟨hl, hu⟩ := mme_dyadic_neg_log_bounds (p w) hx (k w)
      constructor
      · simpa only [Real.negMulLog_def, mul_neg, neg_mul] using
          mul_le_mul_of_nonneg_left hl (hp w)
      · simpa only [Real.negMulLog_def, mul_neg, neg_mul] using
          mul_le_mul_of_nonneg_left hu (hp w)
  exact ⟨Finset.sum_le_sum (fun w _ => (hterm w).1),
    Finset.sum_le_sum (fun w _ => (hterm w).2)⟩


#print axioms solution
