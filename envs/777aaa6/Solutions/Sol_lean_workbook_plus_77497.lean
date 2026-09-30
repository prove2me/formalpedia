-- Prove2me | solution 1 for lean_workbook_plus_77497
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:47:07.112262+00:00
-- url     : https://prove2.me/submissions/71136071-e678-45ca-bdce-27c747c59161

import Mathlib

theorem solution : ¬ (∀ a b c : ℝ,
    (b ^ 2 + c ^ 2) / (b + c) + (c ^ 2 + a ^ 2) / (c + a) +
      (a ^ 2 + b ^ 2) / (a + b) ≥ a + b + c) := by
  intro h
  have hh := h (-1) (-2) (-3)
  norm_num at hh
  all_goals
    change (-6 : ℝ) ≤ (4 + 9) / -5 + (9 + 1) / -4 + (1 + 4) / -3 at hh
    exact (by norm_num : ¬ ((-6 : ℝ) ≤
      (4 + 9) / -5 + (9 + 1) / -4 + (1 + 4) / -3)) hh
