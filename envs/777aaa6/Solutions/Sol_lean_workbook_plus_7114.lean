-- Prove2me | solution 1 for lean_workbook_plus_7114
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:18.49767+00:00
-- url     : https://prove2.me/submissions/4515b8ab-f1bd-411c-852f-c867ae1ce36e

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = x := by
  aesop
