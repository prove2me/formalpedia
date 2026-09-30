-- Prove2me | solution 1 for lean_workbook_plus_24616
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:21.432577+00:00
-- url     : https://prove2.me/submissions/a79a791e-cb21-4796-92e5-4b3bf5aa2c57

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = 3 := by
  aesop
