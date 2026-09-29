-- Prove2me | solution 1 for lean_workbook_plus_43104
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:13:01.352801+00:00
-- url     : https://prove2.me/submissions/2553d296-ca72-4e3e-9d4b-2f6cb4afc5e5

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution : ∀ a b c : ℝ, (a^2 + b^2 + c^2)^2 ≥ 3 * a * b * c * (a + b + c) := by
  intro a b c
  nlinarith [sq_nonneg (a^2-b*c), sq_nonneg (b^2-c*a), sq_nonneg (c^2-a*b), sq_nonneg (a*b-b*c), sq_nonneg (b*c-c*a), sq_nonneg (c*a-a*b)]
