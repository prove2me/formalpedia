-- Prove2me | solution 1 for lean_workbook_plus_23424
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:36.905032+00:00
-- url     : https://prove2.me/submissions/8332113a-b0e8-48e4-b893-01db36872417

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = 1 := by
  aesop
