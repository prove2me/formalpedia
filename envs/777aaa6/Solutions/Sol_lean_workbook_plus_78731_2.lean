-- Prove2me | solution 2 for lean_workbook_plus_78731
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:26:07.154144+00:00
-- url     : https://prove2.me/submissions/5ba06ca7-4c23-4e56-a74e-0b7420071e71

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z: ℝ) : (x + y + z) ^ 4 + 3 * (x * y + y * z + z * x) ^ 2 ≥ 4 * (x + y + z) ^ 2 * (x * y + y * z + z * x) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
