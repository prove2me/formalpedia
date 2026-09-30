-- Prove2me | solution 1 for lean_workbook_plus_8219
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:21.581108+00:00
-- url     : https://prove2.me/submissions/2f8e6251-696d-4e89-81f3-7f79c267ef41

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = x^2 := by
  aesop
