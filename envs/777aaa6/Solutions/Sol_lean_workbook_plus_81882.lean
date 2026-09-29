-- Prove2me | solution 1 for lean_workbook_plus_81882
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:35:08.399094+00:00
-- url     : https://prove2.me/submissions/d0e2b7ad-722f-4690-9f70-ede454f253e2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (4 / 3) * (a^2 + 2*b^2 + 6*a*c + 9*c^2) = (4 / 3) * (2 * b^2 + (a + 3 * c)^2) ∧ (4 / 3) * (2 * b^2 + (a + 3 * c)^2) ≥ 0 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
