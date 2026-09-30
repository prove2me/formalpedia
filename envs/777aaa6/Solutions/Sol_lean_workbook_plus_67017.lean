-- Prove2me | solution 1 for lean_workbook_plus_67017
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:54:52.509387+00:00
-- url     : https://prove2.me/submissions/5342f57e-49e9-48f1-902b-a6990989f3e9

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : a ≥ 4/3 ∧ b ≥ 4/3 ∧ c ≥ 4/3) : a + b + c ≥ 2/a + 1/b + 1/c + 1 := by
  obtain ⟨h1, h2, h3⟩ := ha
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  -- a - 2/a ≥ -1/6, b - 1/b ≥ 7/12, c - 1/c ≥ 7/12
  have e1 : 2 / a ≤ 3 / 2 := by
    rw [div_le_iff₀ ha0]; linarith
  have e2 : 1 / b ≤ 3 / 4 := by
    rw [div_le_iff₀ hb0]; linarith
  have e3 : 1 / c ≤ 3 / 4 := by
    rw [div_le_iff₀ hc0]; linarith
  linarith
