-- Prove2me | solution 1 for mme_dyadic_neg_log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:47:53.038569+00:00
-- url     : https://prove2.me/submissions/91840056-99de-4be0-bc24-af32ff2607b0

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-- Rescaling by a power of two gives rational lower and upper bounds for
the negative logarithm. The exponent is arbitrary; choosing the scaled
argument near one improves the bounds without adding a proof obligation. -/
theorem solution (x : ℝ) (hx : 0 < x) (k : ℕ) :
    (k : ℝ) * (693147180 / 1000000000 : ℝ) + 1 - 2 ^ k * x ≤ -Real.log x ∧
    -Real.log x ≤ (k : ℝ) * (693147181 / 1000000000 : ℝ) - 1 +
      (2 ^ k * x)⁻¹ := by
  have hscaled : 0 < (2 : ℝ) ^ k * x := mul_pos (by positivity) hx
  have hlog : Real.log ((2 : ℝ) ^ k * x) =
      (k : ℝ) * Real.log 2 + Real.log x := by
    rw [Real.log_mul (by positivity) hx.ne', Real.log_pow]
  have hu := Real.log_le_sub_one_of_pos hscaled
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hscaled)
  rw [Real.log_inv] at hl
  rw [hlog] at hu hl
  have htwo_lower : (693147180 / 1000000000 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have htwo_upper : Real.log 2 ≤ (693147181 / 1000000000 : ℝ) := by
    linarith [Real.log_two_lt_d9]
  have hk_lower := mul_le_mul_of_nonneg_left htwo_lower (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hk_upper := mul_le_mul_of_nonneg_left htwo_upper (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  constructor <;> linarith


#print axioms solution
