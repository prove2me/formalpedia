-- Prove2me | solution 1 for lean_workbook_plus_5215
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:04.857072+00:00
-- url     : https://prove2.me/submissions/a4340d2a-2924-4907-9e6f-8a73b2e11920

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ x : ℝ, x > 0 → x + 2 / x - 1 / (x + 1) ≥ Real.sqrt (9 + 6 * Real.sqrt 3)) := by
  intro h
  have h1 := h 1 (by norm_num)
  have e : (1 : ℝ) + 2 / 1 - 1 / (1 + 1) = 5 / 2 := by ring
  rw [e, ge_iff_le] at h1
  have h3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h4 : (5 / 2 : ℝ) < Real.sqrt (9 + 6 * Real.sqrt 3) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  exact absurd h1 (not_le.mpr h4)
