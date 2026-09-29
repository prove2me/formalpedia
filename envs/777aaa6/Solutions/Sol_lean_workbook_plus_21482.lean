-- Prove2me | solution 1 for lean_workbook_plus_21482
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:32.711313+00:00
-- url     : https://prove2.me/submissions/e6dc745f-fa64-4448-a3b3-d2087aeff978

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x y : ℝ, 8 * x ^ 2 * y ^ 2 * (x ^ 4 + y ^ 4) ≤ (x ^ 2 + y ^ 2) ^ 4 := by
  intro x y
  nlinarith [sq_nonneg ((x^2-y^2)^2)]
