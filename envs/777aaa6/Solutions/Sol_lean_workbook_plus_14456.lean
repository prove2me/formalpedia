-- Prove2me | solution 1 for lean_workbook_plus_14456
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T09:14:30.307953+00:00
-- url     : https://prove2.me/submissions/422642c9-e8f9-45a5-bab0-a4a13d9919b7

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ (a b c : ℝ), a ≥ 0 → b ≥ 0 → c ≥ 0 → a^2 + c^2 = 1 → b^2 + 2 * b * (a + c) = 6 → b * (a - c) ≥ 4) := by
  intro h
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h7nn : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg 7
  have h7lt : Real.sqrt 7 < 4 := by nlinarith
  have h7gt : 1 ≤ Real.sqrt 7 := by nlinarith
  have := h 1 (Real.sqrt 7 - 1) 0 (by norm_num) (by linarith) (le_refl 0) (by norm_num) (by nlinarith)
  nlinarith
