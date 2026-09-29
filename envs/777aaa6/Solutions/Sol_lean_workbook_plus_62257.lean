-- Prove2me | solution 1 for lean_workbook_plus_62257
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:16:22.705003+00:00
-- url     : https://prove2.me/submissions/f203943e-6149-434d-b231-05cd63e40331

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution :  ∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := by
  intro x y z
  nlinarith [sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x)]
