-- Prove2me | solution 1 for lean_workbook_plus_40109
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:40:57.046581+00:00
-- url     : https://prove2.me/submissions/69a00bea-4d6e-4a81-a542-fa78fd9142ae

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : (x + 1) * (y + z) = 4) : x*y*z + x*y + y*z + z*x ≤ 4 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
