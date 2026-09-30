-- Prove2me | solution 1 for lean_workbook_plus_30026
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:31.899622+00:00
-- url     : https://prove2.me/submissions/08ee55b9-4e52-40b4-8f8e-1c7fd0d81f17

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = -x^2 := by
  aesop
