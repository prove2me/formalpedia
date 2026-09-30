-- Prove2me | solution 1 for lean_workbook_plus_38561
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T19:56:22.589458+00:00
-- url     : https://prove2.me/submissions/c3f6c417-6bbe-4b1d-b15b-92a43c36e72a

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ (a b c : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ c → a^2 + c^2 = 1 → b^2 + 2 * b * (a + c) = 6 → b * (a - c) ≥ 4) := by
  intro h
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h7n : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg 7
  have hb : 0 ≤ Real.sqrt 7 - 1 := by nlinarith
  have := h 1 (Real.sqrt 7 - 1) 0 (by norm_num) hb (le_refl 0) (by norm_num) (by nlinarith)
  nlinarith
