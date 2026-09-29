-- Prove2me | solution 1 for lean_workbook_plus_2788
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:21.166729+00:00
-- url     : https://prove2.me/submissions/172fb45d-c2fa-4276-a4f8-ad6037b05445

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : x ^ 3 + y ^ 3 + z ^ 3 ≥ 3 * x * y * z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz])
