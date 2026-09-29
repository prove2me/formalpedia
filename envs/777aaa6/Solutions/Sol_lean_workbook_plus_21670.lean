-- Prove2me | solution 1 for lean_workbook_plus_21670
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:21.328153+00:00
-- url     : https://prove2.me/submissions/bf064e80-44a2-4100-aad7-2e01fb85bdf7

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∀ a b c : ℝ, 4 * a ^ 4 + 4 * b ^ 4 + 4 * c ^ 4 ≥ 4 * a ^ 2 * b ^ 2 + 4 * b ^ 2 * c ^ 2 + 4 * c ^ 2 * a ^ 2 := by
  intro a b c
  nlinarith [sq_nonneg (a^2-b^2), sq_nonneg (b^2-c^2), sq_nonneg (c^2-a^2)]
