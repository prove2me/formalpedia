-- Prove2me | solution 1 for lean_workbook_plus_68217
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:05.379219+00:00
-- url     : https://prove2.me/submissions/e476812a-eb7e-4ba2-a0e4-dcc78a051db6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (hx1 : x + y + z = 1) : x * y + y * z + z * x ≤ 1 / 3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
