-- Prove2me | solution 1 for lean_workbook_plus_82052
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:12:08.484679+00:00
-- url     : https://prove2.me/submissions/4b6f83b4-85c3-4a78-8314-89aae41070f9

import Mathlib

theorem solution : ¬ (∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 →
    1 / (a ^ 2 + 3) + 1 / (b ^ 2 + 3) + 1 / (c ^ 2 + 3) ≤ 3 / 4) := by
  intro h
  have hbad := h (1/2) (1/2) (1/2) (by norm_num)
  norm_num at hbad
