-- Prove2me | solution 1 for lean_workbook_plus_18742
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:40:33.714158+00:00
-- url     : https://prove2.me/submissions/412c0aa1-8189-4640-91a3-f062b83807df

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : x^2 - 16 ≥ 0 ↔ x ≥ 4 ∨ x ≤ -4 := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    nlinarith [hcon.1, hcon.2]
  · rintro (h | h) <;> nlinarith
