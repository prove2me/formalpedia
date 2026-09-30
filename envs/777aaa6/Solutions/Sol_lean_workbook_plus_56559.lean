-- Prove2me | solution 1 for lean_workbook_plus_56559
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:43.509957+00:00
-- url     : https://prove2.me/submissions/ccc48a61-3d5a-4175-9129-bc5cb4fbc21e

import Mathlib
set_option autoImplicit false

theorem solution : ∀ a b : ℝ, a^2 + a * b + b^2 ≥ (3 / 4) * (a + b)^2   := by
  intros a b
  nlinarith [sq_nonneg (a - b)]

#print axioms solution
