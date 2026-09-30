-- Prove2me | solution 1 for lean_workbook_plus_22556
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:45.594734+00:00
-- url     : https://prove2.me/submissions/c4a76547-4816-4b60-a018-236ca6513907

import Mathlib
set_option autoImplicit false

theorem solution (α β x y : ℝ) : (2 * α ^ 2 + 2 * α * β + β ^ 2) * (2 * x ^ 2 + 2 * x * y + y ^ 2) ≥ (2 * α * x + α * y + β * x + β * y) ^ 2   := by
  nlinarith only [sq_nonneg (α*y-β*x)]

#print axioms solution
