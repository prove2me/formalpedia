-- Prove2me | solution 1 for lean_workbook_plus_37605
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:22.876522+00:00
-- url     : https://prove2.me/submissions/4926ea23-50f2-4cf7-b5de-3236dc3efe83

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℚ → ℚ, ∀ x, f x = x := by
  aesop
