-- Prove2me | solution 1 for lean_workbook_plus_40319
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T19:59:28.426015+00:00
-- url     : https://prove2.me/submissions/7dc82bf7-70df-4014-8897-28045be58b7b

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ x y : ℝ, (x ≠ 0 ∧ y ≠ 0) → 1 / x ^ 2 + 2 / y ^ 2 ≥ Real.sqrt 2 * (1 / x + 1 / y)) := by
  intro h
  have h12 := h 1 2 ⟨one_ne_zero, two_ne_zero⟩
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg 2
  norm_num at h12
