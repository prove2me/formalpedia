-- Prove2me | solution 1 for lean_workbook_plus_64527
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:25.074104+00:00
-- url     : https://prove2.me/submissions/17fbb876-fcde-441c-8117-4a604ffeade0

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) :
  (x^2 * y^2 + y^2 * z^2) / 2 ≥ x * y^2 * z ∧
  (y^2 * z^2 + z^2 * x^2) / 2 ≥ x * y * z^2 ∧
  (x^2 * y^2 + z^2 * x^2) / 2 ≥ x^2 * y * z   := by
  constructor
  have := sq_nonneg (x * y - y * z)
  linarith
  constructor
  have := sq_nonneg (y * z - z * x)
  linarith
  have := sq_nonneg (x * y - z * x)
  linarith

#print axioms solution
