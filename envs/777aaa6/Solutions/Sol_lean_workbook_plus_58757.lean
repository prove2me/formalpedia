-- Prove2me | solution 1 for lean_workbook_plus_58757
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:48:25.016581+00:00
-- url     : https://prove2.me/submissions/c23e52f6-0044-4780-8cac-745cbaeacdaa

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, (a / (b + c) + b / (c + a) + c / (a + b) < 2)) := by
  intro h
  have := h 100 1 1
  norm_num at this
