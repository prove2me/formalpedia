-- Prove2me | solution 1 for lean_workbook_plus_77606
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:47:06.206667+00:00
-- url     : https://prove2.me/submissions/502467e4-ca8d-4211-b83a-aa0d04c07635

import Mathlib

theorem solution : ¬ (∀ x y z : ℝ,
    (1 + x ^ 3) * (1 + y ^ 3) * (1 + z ^ 3) ≥ (1 + x * y * z) ^ 3) := by
  intro h
  have hh := h (-1) 0 0
  norm_num at hh
  all_goals
    change (1 : ℝ) ≤ (0 : ℝ) at hh
    exact (by norm_num : ¬ ((1 : ℝ) ≤ (0 : ℝ))) hh
