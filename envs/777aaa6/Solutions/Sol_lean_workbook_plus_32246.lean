-- Prove2me | solution 1 for lean_workbook_plus_32246
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:57:56.49621+00:00
-- url     : https://prove2.me/submissions/fd7435cd-1e00-4ce7-b220-2b81311c3895

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b) :
  a^100 + b^100 ≥ 2 * (a * b)^50 := by
  simp only [mul_pow]
  nlinarith [sq_nonneg (a^50-b^50)]
