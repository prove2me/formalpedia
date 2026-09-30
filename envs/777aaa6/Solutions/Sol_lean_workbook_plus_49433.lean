-- Prove2me | solution 1 for lean_workbook_plus_49433
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:09:06.955988+00:00
-- url     : https://prove2.me/submissions/4ab694c6-23ee-47c9-b923-bbb1fa9dc1a7

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx : 0 ≤ x) : x^5 - x^3 - x^2 + 1 ≥ 0 := by
  have h : x^5 - x^3 - x^2 + 1 = (x - 1)^2 * ((x + 1) * (x^2 + x + 1)) := by ring
  rw [h]
  apply mul_nonneg (sq_nonneg _)
  apply mul_nonneg
  · linarith
  · nlinarith [sq_nonneg x]
