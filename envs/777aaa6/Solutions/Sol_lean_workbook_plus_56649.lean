-- Prove2me | solution 1 for lean_workbook_plus_56649
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:40.966668+00:00
-- url     : https://prove2.me/submissions/39609f7e-8e25-478c-9739-38d3461c76fa

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, (x ^ 2 / 4 + y ^ 2 + z ^ 2) ≥ x * y - x * z + 2 * y * z   := by
  rintro x y z
  nlinarith [sq_nonneg (x / 2 - y + z)]

#print axioms solution
