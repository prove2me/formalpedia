-- Prove2me | solution 1 for lean_workbook_plus_61520
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T19:56:20.54131+00:00
-- url     : https://prove2.me/submissions/6d8e8395-6dff-49ca-b1e6-764bf254e40f

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 + c^2 = 3 → a + b + c ≥ 3 * Real.sqrt 3) := by
  intro h
  have h1 := h 1 1 1 (by norm_num)
  have hs : (1:ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith
