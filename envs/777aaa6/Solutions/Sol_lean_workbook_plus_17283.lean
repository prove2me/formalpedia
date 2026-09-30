-- Prove2me | solution 1 for lean_workbook_plus_17283
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:28:02.086782+00:00
-- url     : https://prove2.me/submissions/70fdc3b2-5ba3-4a1f-8263-a360d732b071

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) : a^2 + b^2 + c^2 ≥ b * c + c * a + a * b + 3 * (a - b) * (b - c)   := by
  nlinarith only [sq_nonneg (a - 2 * b + c)]

#print axioms solution
