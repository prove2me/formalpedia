-- Prove2me | solution 1 for lean_workbook_plus_37622
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:38.964917+00:00
-- url     : https://prove2.me/submissions/d10656d0-29b5-42ed-95f8-957a7226a9c9

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = 1 - x := by
  aesop
