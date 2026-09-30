-- Prove2me | solution 1 for lean_workbook_plus_9060
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:55.172286+00:00
-- url     : https://prove2.me/submissions/a07ac446-4a9e-4cb2-aaad-472979a14322

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a : ℝ, (-(27 / 392) * (a - 1 / 3) + 9 / 28) ≥ 1 / (a ^ 2 + 3)) := by
  intro h
  have := h 10
  norm_num at this
