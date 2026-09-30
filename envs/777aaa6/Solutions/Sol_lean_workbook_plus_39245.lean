-- Prove2me | solution 1 for lean_workbook_plus_39245
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:30.041629+00:00
-- url     : https://prove2.me/submissions/f5d7e707-5940-4ccc-98a5-1ee598252272

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = -x := by
  aesop
