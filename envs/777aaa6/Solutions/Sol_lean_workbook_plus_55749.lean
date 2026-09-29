-- Prove2me | solution 1 for lean_workbook_plus_55749
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:39.126129+00:00
-- url     : https://prove2.me/submissions/a7f69798-e41e-4b7d-9ad3-4f3d18ce0b99

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) ^ 3 + (2 * a + b) ^ 3 + (3 * a) ^ 3 ≤ 8 * (9 * a ^ 3 + b ^ 3) := by
  intros
  nlinarith [sq_nonneg (2*a-b), sq_nonneg (a-2*b), sq_nonneg (a+b)]
