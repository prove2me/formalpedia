-- Prove2me | solution 1 for lean_workbook_plus_77780
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:47:02.524827+00:00
-- url     : https://prove2.me/submissions/7869702c-1e0a-4cb7-a325-d7389fd88a6b

import Mathlib

theorem solution : ¬ (∀ a b c : ℝ,
    9 * (a + b) * (b + c) * (c + a) ≥
      8 * (a + b + c) * (a * b + b * c + c * a)) := by
  intro h
  have hh := h (-1) (-1) 0
  norm_num at hh
  all_goals
    change (18 : ℝ) ≤ 16 * (1 + 0 + 0) at hh
    exact (by norm_num : ¬ ((18 : ℝ) ≤ 16 * (1 + 0 + 0))) hh
