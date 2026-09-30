-- Prove2me | solution 1 for lean_workbook_plus_66513
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:44.87077+00:00
-- url     : https://prove2.me/submissions/56054b04-6ff6-4aa8-b5a5-2dae721fd385

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) :
  x * (x^8 + 1) * (x^3 - 1) + 1 > 0   := by
  have h5 : x ^ 5 < 1 := pow_lt_one₀ hx.1.le hx.2 (by decide)
  have h9 : x ^ 9 < x ^ 4 := by
    calc
      x ^ 9 = x ^ 4 * x ^ 5 := by ring
      _ < x ^ 4 * 1 := mul_lt_mul_of_pos_left h5 (pow_pos hx.1 4)
      _ = x ^ 4 := mul_one _
  nlinarith [pow_nonneg hx.1.le 12]

#print axioms solution
