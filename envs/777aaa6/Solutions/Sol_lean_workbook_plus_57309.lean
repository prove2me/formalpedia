-- Prove2me | solution 1 for lean_workbook_plus_57309
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:31.35339+00:00
-- url     : https://prove2.me/submissions/e95f242c-6dac-4635-8b80-5cf628a0ef16

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = 2 * x := by
  aesop
