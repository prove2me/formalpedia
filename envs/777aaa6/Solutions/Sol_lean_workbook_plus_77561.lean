-- Prove2me | solution 1 for lean_workbook_plus_77561
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:47:08.1726+00:00
-- url     : https://prove2.me/submissions/5ca76ed1-f6ff-45dd-a24e-8f5880e2b36a

import Mathlib

theorem solution : ¬ (∀ x y z : ℝ,
    (x / (y + z)) ^ 2 + (y / (x + z)) ^ 2 + (z / (x + y)) ^ 2 +
      6 * x * y * z / ((x + y) * (y + z) * (z + x)) ≥ 3 / 2) := by
  intro h
  have hh := h 0 0 0
  norm_num at hh
  all_goals
    change (3 : ℝ) / 2 ≤ 0 + 0 + 0 + 0 at hh
    exact (by norm_num : ¬ ((3 : ℝ) / 2 ≤ 0 + 0 + 0 + 0)) hh
