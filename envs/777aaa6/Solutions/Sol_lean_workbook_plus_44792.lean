-- Prove2me | solution 1 for lean_workbook_plus_44792
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:39:28.327745+00:00
-- url     : https://prove2.me/submissions/6b57f77b-e114-4fa8-b3b7-d040b6d3dd0d

import Mathlib
set_option autoImplicit false

theorem solution (h : ℕ) : (2^(2 * h) * Real.sqrt ((2^(2 * h))) : ℝ) = 2^(3 * h)   := by
  have hpow : (2 : ℝ) ^ (2 * h) = ((2 : ℝ) ^ h) ^ 2 := by
    rw [Nat.mul_comm 2 h, pow_mul]
  have hsqrt : Real.sqrt ((2 : ℝ) ^ (2 * h)) = (2 : ℝ) ^ h := by
    rw [hpow, Real.sqrt_sq (pow_nonneg (by norm_num) h)]
  rw [hsqrt, ← pow_add]
  congr 1
  omega

#print axioms solution
