-- Prove2me | solution 1 for lean_workbook_plus_14369
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:40.733311+00:00
-- url     : https://prove2.me/submissions/fd2b905b-a8f6-4d29-b9f8-b742c224df6c

import Mathlib.Analysis.Complex.Basic

theorem solution : ∃ f : ℝ → ℝ, ∀ x : ℝ, x > 0 → f x > x := by
  refine ⟨fun x => x + 1, fun x _ => ?_⟩
  simp only [gt_iff_lt]
  linarith
