-- Prove2me | solution 1 for lean_workbook_plus_68179
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:39:36.833418+00:00
-- url     : https://prove2.me/submissions/9c513cd3-2669-4702-b868-e87c4f57e7c1

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ α : ℝ, α ≠ 0 → α + 1/α ≥ 2) := by
  intro h
  have := h (-1) (by norm_num)
  norm_num at this
