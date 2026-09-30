-- Prove2me | solution 1 for lean_workbook_plus_73882
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:09:27.683023+00:00
-- url     : https://prove2.me/submissions/15b3d38c-7f14-4e3f-8bb5-459f57507c2e

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ t : ℝ, t ≤ 1/4 → t^3 - 3 * t + 2 ≤ 4 := by
  intro t ht
  have hnonneg := mul_nonneg (show 0 ≤ 2 - t by linarith) (sq_nonneg (t + 1))
  nlinarith [hnonneg]
