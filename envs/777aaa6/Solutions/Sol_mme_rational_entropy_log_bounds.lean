-- Prove2me | solution 1 for mme_rational_entropy_log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:44:58.054985+00:00
-- url     : https://prove2.me/submissions/954a71d2-9e46-4f7c-9c71-1b4f9e2dad51

import Theorems.Thm_mme_entropy_dyadic_bounds

open scoped BigOperators
open MME.RegionRate

/-- Rational logarithm enclosures give entropy bounds without a normalization
hypothesis. Zero atoms contribute zero and need no logarithm certificate. -/
theorem solution
    {W : Type*} [Fintype W] (p : W → ℚ) (hp : ∀ w, 0 ≤ p w)
    (lower upper : W → ℚ)
    (hlog : ∀ w, 0 < p w →
      (lower w : ℝ) ≤ Real.log (p w : ℝ) ∧
        Real.log (p w : ℝ) ≤ (upper w : ℝ)) :
    ((-(∑ w, p w * upper w) : ℚ) : ℝ) ≤ entropy (fun w => (p w : ℝ)) ∧
      entropy (fun w => (p w : ℝ)) ≤ ((-(∑ w, p w * lower w) : ℚ) : ℝ) := by
  have hpR (w : W) : (0 : ℝ) ≤ p w := by exact_mod_cast hp w
  have hterm (w : W) :
      (p w : ℝ) * (lower w : ℝ) ≤ (p w : ℝ) * Real.log (p w : ℝ) ∧
        (p w : ℝ) * Real.log (p w : ℝ) ≤ (p w : ℝ) * (upper w : ℝ) := by
    by_cases hz : p w = 0
    · simp [hz]
    · have h := hlog w (lt_of_le_of_ne (hp w) (Ne.symm hz))
      exact ⟨mul_le_mul_of_nonneg_left h.1 (hpR w),
        mul_le_mul_of_nonneg_left h.2 (hpR w)⟩
  have hl := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => (hterm w).1)
  have hu := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => (hterm w).2)
  simp only [entropy, Real.negMulLog_def, neg_mul, Finset.sum_neg_distrib]
  push_cast
  exact ⟨neg_le_neg hu, neg_le_neg hl⟩


#print axioms solution
