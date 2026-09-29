-- Prove2me | solution 1 for lean_workbook_plus_27542
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:29.392155+00:00
-- url     : https://prove2.me/submissions/5f9cf118-89a8-48bd-a9b0-38f72138c7c1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : a + b + c = 5) (h2 : a * b + b * c + a * c = 3) : -1 ≤ c ∧ c ≤ 13 / 3 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
