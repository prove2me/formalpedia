-- Prove2me | solution 1 for lean_workbook_plus_66553
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T09:14:17.413968+00:00
-- url     : https://prove2.me/submissions/6a7d4d6e-8b88-4b2e-ac6e-00989dad55d7

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b : ℝ, a^3 + a^3 * b^3 + 1 ≥ a^3 * b + a^2 * b^2 + a) := by
  intro h
  have := h (-1) 2
  norm_num at this
