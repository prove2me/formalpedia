-- Prove2me | solution 1 for lean_workbook_plus_70282
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:29.551102+00:00
-- url     : https://prove2.me/submissions/5c3c8421-52bb-4a16-bd8e-e49816d591c7

import Mathlib
set_option autoImplicit false

theorem solution : ∀ t1 t2 : ℝ, (1 + t1^2) * (1 + t2^2) ≥ (t1 + t2)^2 := by
  intro t1 t2
  nlinarith [sq_nonneg (t1 * t2 - 1)]

#print axioms solution
