-- Prove2me | solution 1 for lean_workbook_plus_62677
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:38.792284+00:00
-- url     : https://prove2.me/submissions/69489b93-2c51-465e-abc5-08ce1d4a3497

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x: ℝ) (Q: ℝ → ℝ) (h₁ : Q x = (x + 1/2)^2 + 8003/4): Q x >= 8003/4 := by
  (intros; nlinarith [sq_nonneg (x)])
