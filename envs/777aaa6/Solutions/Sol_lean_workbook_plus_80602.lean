-- Prove2me | solution 1 for lean_workbook_plus_80602
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:32:09.430468+00:00
-- url     : https://prove2.me/submissions/049cdd86-d944-4f15-915c-8f44066f5817

import Mathlib

theorem solution : ¬ (∀ a : ℝ, a / (a ^ 2 + 4) ≤ (2 + 3 * a) / 25) := by
  intro h
  have hbad := h (-4)
  norm_num at hbad
