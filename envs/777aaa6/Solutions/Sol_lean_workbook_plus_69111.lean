-- Prove2me | solution 1 for lean_workbook_plus_69111
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:42:51.008297+00:00
-- url     : https://prove2.me/submissions/df405c84-7647-480c-955b-1fe49c21e714

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, (1 / (a * (b + c)) + 1 / (b * (a + c)) + 1 / (c * (a + b))) ≤ (18:ℝ) / 23) := by
  intro h
  have := h 1 1 1
  norm_num at this
