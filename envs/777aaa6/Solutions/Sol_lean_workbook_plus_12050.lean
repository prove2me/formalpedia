-- Prove2me | solution 1 for lean_workbook_plus_12050
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:08.223512+00:00
-- url     : https://prove2.me/submissions/18bcb6e1-6618-431d-add4-3e0f1914f031

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : y = 4.5 + x) (h₂ : 6 * x + 3 * y = 36) : y = 7 ∧ x = 2.5 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
