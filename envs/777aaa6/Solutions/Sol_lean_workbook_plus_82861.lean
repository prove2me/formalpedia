-- Prove2me | solution 1 for lean_workbook_plus_82861
-- status  : ACCEPTED   (disprove)
-- author  : @Shuze Chen
-- created : 2026-08-27T02:17:17.805288+00:00
-- url     : https://prove2.me/submissions/d9f5f658-9231-4989-ab95-c24be0ae8de4

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, b * c * (b + c) + 4 * a ≥ (a + 2) * (b + c)) := by
  intro h
  have h1 := h 0 1 0
  norm_num at h1
