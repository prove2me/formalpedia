-- Prove2me | solution 1 for lean_workbook_plus_36919
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:41:34.790693+00:00
-- url     : https://prove2.me/submissions/cb551a77-e465-46d1-84c5-46c2754e8ee5

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ x : ℝ, x^8 - x^5 + x^2 - x + 1 > 0 := by
  intro x
  nlinarith [sq_nonneg (x^4 - x/2), sq_nonneg (x - 2/3)]
