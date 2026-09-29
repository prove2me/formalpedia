-- Prove2me | solution 1 for lean_workbook_plus_15822
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:51.979677+00:00
-- url     : https://prove2.me/submissions/45f6c155-477f-4a01-a37f-8dea3f2cbd3d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a > 0 ∧ b > 0) : (a + b) ^ 2 ≥ 4 * a * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
