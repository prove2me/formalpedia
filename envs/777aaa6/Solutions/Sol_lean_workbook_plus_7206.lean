-- Prove2me | solution 1 for lean_workbook_plus_7206
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:40:42.575197+00:00
-- url     : https://prove2.me/submissions/688468cb-a355-47b9-a967-f4a042ea4282

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ x : ℝ, x^5 - x^2 + 3 ≥ x^3 + 2 ↔ (x - 1)^2 * (x + 1) * (x^2 + x + 1) ≥ 0 := by
  intro x
  have h : (x - 1)^2 * (x + 1) * (x^2 + x + 1) = (x^5 - x^2 + 3) - (x^3 + 2) := by ring
  rw [h]
  constructor
  · intro h1
    linarith
  · intro h1
    linarith
