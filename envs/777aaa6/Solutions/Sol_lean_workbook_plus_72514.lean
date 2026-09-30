-- Prove2me | solution 1 for lean_workbook_plus_72514
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:11.063648+00:00
-- url     : https://prove2.me/submissions/d6d6830e-8206-4b93-8245-0e950b3a3ef9

import Mathlib

set_option autoImplicit false

theorem solution : ∀ a b : ℝ, a ^ 2 + b ^ 2 + a * b ≥ (3 / 4) * (a + b) ^ 2 := by
  intro a b
  nlinarith [sq_nonneg (a - b)]
