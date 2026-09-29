-- Prove2me | solution 1 for lean_workbook_plus_50580
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:20:19.086214+00:00
-- url     : https://prove2.me/submissions/f30672c1-4061-451b-bca3-3051a3cd4e4d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a ≥ b) (hbc : b ≥ c) (hca : 0 < c) :  (a - b) * (b - c) * (a - c) ≥ 0 ∧ a^2 * b + a * c^2 + b^2 * c ≥ a^2 * c + a * b^2 + b * c^2 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
