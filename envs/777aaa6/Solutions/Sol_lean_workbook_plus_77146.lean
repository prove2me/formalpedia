-- Prove2me | solution 1 for lean_workbook_plus_77146
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:09:49.173054+00:00
-- url     : https://prove2.me/submissions/a5282df6-4756-479a-b27b-2a7e2fc2a15d

import Mathlib

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x < 0) : 1 - x > 0 ∧ 2 * x ^ 7 < 0 := by
  constructor
  · linarith
  · have hp : x ^ 7 < 0 := by
      exact (show Odd (7 : ℕ) by decide).pow_neg hx
    linarith
