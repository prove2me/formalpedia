-- Prove2me | solution 1 for mme_cross_entropy_dyadic_upper
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:55:55.891289+00:00
-- url     : https://prove2.me/submissions/9a44f90c-0e5c-4ada-9b69-7fcf3c1d45d5

import Theorems.Thm_mme_dyadic_neg_log_bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

/-- Positive reference weights give a rational upper bound on finite cross
entropy after dyadic rescaling. The multiplier weights need only be nonnegative. -/
theorem solution {W : Type*} [Fintype W]
    (p q : W → ℝ) (hp : ∀ w, 0 ≤ p w) (hq : ∀ w, 0 < q w) (k : W → ℕ) :
    -(∑ w, p w * Real.log (q w)) ≤
      ∑ w, p w * ((k w : ℝ) * (693147181 / 1000000000 : ℝ) - 1 +
        (2 ^ k w * q w)⁻¹) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro w _
  simpa only [mul_neg] using mul_le_mul_of_nonneg_left
    (mme_dyadic_neg_log_bounds (q w) (hq w) (k w)).2 (hp w)


#print axioms solution
