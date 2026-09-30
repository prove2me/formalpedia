-- Prove2me | solution 1 for lean_workbook_plus_47746
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:17:54.209808+00:00
-- url     : https://prove2.me/submissions/d65388a9-86fe-42f9-9de2-6edf01612e51

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ a b c : ℝ, (b + 2 * a) ^ 2 + (c + 2 * a) ^ 2 ≥ 0 := by
  intro a b c
  positivity
