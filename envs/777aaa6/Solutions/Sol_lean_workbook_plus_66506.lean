-- Prove2me | solution 1 for lean_workbook_plus_66506
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:03:08.315002+00:00
-- url     : https://prove2.me/submissions/0d37f19e-cdf3-4818-b273-24d6d521cc24

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x^2 / (y + z)) ≥ (4 * x - y - z) / 4   := by
  apply (le_div_iff₀ (add_pos hy hz)).2
  nlinarith [sq_nonneg (2 * x - y - z)]

#print axioms solution
