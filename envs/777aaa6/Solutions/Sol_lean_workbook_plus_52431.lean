-- Prove2me | solution 1 for lean_workbook_plus_52431
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:31.200131+00:00
-- url     : https://prove2.me/submissions/f9869388-a75d-470a-b51e-f88232da1b1b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z t : ℝ) : x * y + y * z + z * t + t * x ≥ -(x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (t), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - t), sq_nonneg (y - z), sq_nonneg (y - t), sq_nonneg (z - t), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (x + t), sq_nonneg (y + z), sq_nonneg (y + t), sq_nonneg (z + t)])
