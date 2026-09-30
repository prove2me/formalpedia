-- Prove2me | solution 2 for lean_workbook_plus_56649
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:09.008093+00:00
-- url     : https://prove2.me/submissions/1c74acb5-853e-4ad0-b7d4-4b0a5c39df39

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x y z : ℝ, (x ^ 2 / 4 + y ^ 2 + z ^ 2) ≥ x * y - x * z + 2 * y * z := by
  intro x y z
  nlinarith [sq_nonneg (x/2-y+z)]
