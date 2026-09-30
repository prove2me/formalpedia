-- Prove2me | solution 1 for lean_workbook_plus_48252
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T09:43:58.383588+00:00
-- url     : https://prove2.me/submissions/08bbff42-45df-40b3-886b-f8cc696e3e44

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ (a b c : ℝ), 0 < a → 0 < b → 0 < c → (a^2 + a*c)/(2*b + a + c) + (b^2 + b*a)/(2*c + a + b) + (c^2 + c*b)/(2*a + b + c) ≥ 2*(a + b + c)) := by
  intro h
  have := h 1 1 1 one_pos one_pos one_pos
  norm_num at this
