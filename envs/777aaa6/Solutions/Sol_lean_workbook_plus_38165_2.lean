-- Prove2me | solution 2 for lean_workbook_plus_38165
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:34.734609+00:00
-- url     : https://prove2.me/submissions/f6c977cf-69b9-4777-992b-3eec25a31665

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^4 + b^4 + c^4 ≥ 1 / 2 * (a * b * (a^2 + b^2) + b * c * (b^2 + c^2) + c * a * (c^2 + a^2)) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
