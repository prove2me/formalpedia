-- Prove2me | solution 1 for lean_workbook_plus_27803
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:12.953061+00:00
-- url     : https://prove2.me/submissions/a81cc976-fe75-4454-857f-69aefddd72bf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  2 * (a^2 + b^2 + c^2)^2 ≥ 3 * (a^3 * b + b^3 * c + c^3 * a + a * b^3 + b * c^3 + c * a^3) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
