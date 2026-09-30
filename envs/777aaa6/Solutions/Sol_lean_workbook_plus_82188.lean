-- Prove2me | solution 1 for lean_workbook_plus_82188
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:12:09.984474+00:00
-- url     : https://prove2.me/submissions/08fcb34a-db56-4f98-8ab1-a1c7385ea4e2

import Mathlib

theorem solution : ¬ (∀ a b c : ℝ,
    (3 * a - b - c) * (b - c) ^ 2 + (3 * b - c - a) * (c - a) ^ 2 +
      (3 * c - a - b) * (a - b) ^ 2 ≥ 0) := by
  intro h
  have hbad := h 0 (-1) (-2)
  norm_num at hbad
