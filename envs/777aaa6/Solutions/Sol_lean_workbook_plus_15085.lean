-- Prove2me | solution 1 for lean_workbook_plus_15085
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:58.474651+00:00
-- url     : https://prove2.me/submissions/2e27ef7b-5663-4675-81bc-fc0c49e7b732

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  2 * 3 * (a^2 + b^2 + c^2)^2 ≥ (a + b + c)^2 * (a^2 + b^2 + c^2 + a * b + b * c + c * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
