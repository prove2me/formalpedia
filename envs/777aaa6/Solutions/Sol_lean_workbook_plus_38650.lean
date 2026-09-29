-- Prove2me | solution 1 for lean_workbook_plus_38650
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:35.701801+00:00
-- url     : https://prove2.me/submissions/d756a0ff-200c-4883-b182-0e90c7efee7e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : 3 * x * y * z * (x + y + z) ≤ (x * y + y * z + z * x)^2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
