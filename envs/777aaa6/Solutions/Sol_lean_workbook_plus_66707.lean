-- Prove2me | solution 1 for lean_workbook_plus_66707
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:17.849663+00:00
-- url     : https://prove2.me/submissions/fab2bff6-e076-44ee-8fe1-fb22ca8bb6b2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : 3 = x * y + y * z + z * x) : 3 * (x + y) * (x + z) * (y + z) * (x + y + z) ≥ 8 * (x ^ 2 + y ^ 2 + z ^ 2 + 6) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
