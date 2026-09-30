-- Prove2me | solution 1 for lean_workbook_plus_4390
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T09:43:27.566974+00:00
-- url     : https://prove2.me/submissions/ad333c29-a518-48fc-9e26-598c0a8fcd81

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b : ℝ, a^2 + b^2 + (3 - a - b)^2 + 3 / 2 * a * b * (3 - a - b) - 9 / 2 ≥ 0) := by
  intro h
  have h10 := h 10 10
  have e : (10:ℝ)^2 + 10^2 + (3 - 10 - 10)^2 + 3 / 2 * 10 * 10 * (3 - 10 - 10) - 9 / 2 = -4131/2 := by ring
  rw [e] at h10
  norm_num at h10
