-- Prove2me | solution 1 for lean_workbook_plus_81088
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:56:47.946+00:00
-- url     : https://prove2.me/submissions/bcad3c03-3f0d-4eb8-90ee-860a8f794699

import Mathlib.Tactic

theorem solution (a b D : ℝ) (h₁ : D = -3 * (a - b) ^ 2) (h₂ : a > b) : D ≤ 0 := by
  rw [h₁]; nlinarith [sq_nonneg (a - b)]
