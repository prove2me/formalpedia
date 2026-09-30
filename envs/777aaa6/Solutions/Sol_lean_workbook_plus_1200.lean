-- Prove2me | solution 1 for lean_workbook_plus_1200
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:15.083164+00:00
-- url     : https://prove2.me/submissions/3b96bd86-aa89-40d1-84b4-75b7238b245f

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = 0 := by
  aesop
