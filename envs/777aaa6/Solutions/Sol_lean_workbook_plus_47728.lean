-- Prove2me | solution 1 for lean_workbook_plus_47728
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:32.684666+00:00
-- url     : https://prove2.me/submissions/28c7c339-3f35-4abe-ab9d-f71d73f08c57

import Mathlib
set_option autoImplicit false

theorem solution : ∀ a b : ℝ, Real.sqrt (2 * (a ^ 2 + b ^ 2)) ≥ a + b   := by
  intros a b
  have := sq_nonneg (a - b)
  apply Real.le_sqrt_of_sq_le
  linarith

#print axioms solution
