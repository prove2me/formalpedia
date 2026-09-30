-- Prove2me | solution 1 for lean_workbook_plus_2728
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:36.292501+00:00
-- url     : https://prove2.me/submissions/9e113f64-670d-468f-9084-8b2d567bec16

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = -1 := by
  aesop
