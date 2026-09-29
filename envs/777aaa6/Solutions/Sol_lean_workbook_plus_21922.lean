-- Prove2me | solution 1 for lean_workbook_plus_21922
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:32.709123+00:00
-- url     : https://prove2.me/submissions/f3b3ceff-3bd3-4556-a3c2-4775ec0736dc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a + b + c = 0) : (a * b + b * c + c * a >= 3) → (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) <= 1) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
