-- Prove2me | solution 1 for lean_workbook_plus_81683
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:16:54.839972+00:00
-- url     : https://prove2.me/submissions/cf0e0d2d-ab4e-4c55-bfb9-e1bd7c24658b

import Mathlib

theorem solution : ¬ (∀ a b c : ℝ,
    2 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 27 - 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a)) := by
  intro h
  have hbad := h 0 0 0
  norm_num at hbad
