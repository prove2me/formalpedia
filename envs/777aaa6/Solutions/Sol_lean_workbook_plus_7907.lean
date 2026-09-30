-- Prove2me | solution 1 for lean_workbook_plus_7907
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:38:01.930164+00:00
-- url     : https://prove2.me/submissions/5886bd20-1ff2-4847-b7b6-e6e03c462d63

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ x : ℝ, x^3 ≥ x ↔ x * (x^2 - 1) ≥ 0 := by
  intro x
  have hx : x * (x^2 - 1) = x^3 - x := by ring
  rw [hx]
  constructor
  · intro h
    linarith
  · intro h
    linarith
