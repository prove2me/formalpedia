-- Prove2me | solution 1 for lean_workbook_plus_76978
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:47:04.603842+00:00
-- url     : https://prove2.me/submissions/673d7554-f00c-47d7-ac66-b0f41b707d2a

import Mathlib

theorem solution : ¬ (∀ a : ℝ,
    (1 - 2 * a) ^ 2 * (3 * a * (a - 1) ^ 2 + 8 - 5 * a) ≥ 0) := by
  intro h
  have hh := h (-2)
  norm_num at hh
  all_goals
    change (0 : ℝ) ≤ (-900 : ℝ) at hh
    exact (by norm_num : ¬ ((0 : ℝ) ≤ (-900 : ℝ))) hh
