-- Prove2me | solution 1 for lean_workbook_plus_45269
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:42:26.266696+00:00
-- url     : https://prove2.me/submissions/48f0809b-9a87-4eda-b917-c8db97ef9520

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, (a + b + c) ^ 2 / (a * b + b * c + c * a) ≥ 9 / (a + b + c)) := by
  intro h
  have := h 1 1 (-1)
  norm_num at this
