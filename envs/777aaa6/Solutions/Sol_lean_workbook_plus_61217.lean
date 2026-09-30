-- Prove2me | solution 1 for lean_workbook_plus_61217
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:47:51.479548+00:00
-- url     : https://prove2.me/submissions/ccc8541d-aae3-4e49-8827-35d7b491d3fe

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ n : ℕ, 2 ≤ n → 32 * n^(2 * n) * (2 * n + 1) > 9 * (n + 1)^(2 * n + 1)) := by
  intro h
  have := h 13 (by norm_num)
  norm_num at this
