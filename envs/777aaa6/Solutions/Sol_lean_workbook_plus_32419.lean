-- Prove2me | solution 1 for lean_workbook_plus_32419
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:27:56.793791+00:00
-- url     : https://prove2.me/submissions/cd3decb6-29d5-40d2-bb65-237c219708f5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : x * y * (x ^ 2 + y ^ 2) ≤ 2 + 2 * x * y * (x + y) * (x + y - 2) := by
  nlinarith [sq_nonneg (x*y-1), mul_nonneg (mul_nonneg hx hy) (sq_nonneg (x+y-2))]
