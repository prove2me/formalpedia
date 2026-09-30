-- Prove2me | solution 1 for lean_workbook_plus_82030
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:12:09.237657+00:00
-- url     : https://prove2.me/submissions/0a289e53-7e20-4d72-a851-dc1652733fb6

import Mathlib

theorem solution : ¬ (∀ a b c : ℝ,
    (a + b + c) * (a^2 / b + b^2 / c + c^2 / a) ≥ 3 * (a^2 + b^2 + c^2)) := by
  intro h
  have hbad := h 1 1 (-1)
  norm_num at hbad
  change (3 : ℝ) * (2 + 1) ≤ 1 * (0 + 1) at hbad
  norm_num at hbad
