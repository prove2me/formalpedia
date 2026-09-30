-- Prove2me | solution 2 for lean_workbook_plus_39090
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:45.020453+00:00
-- url     : https://prove2.me/submissions/6c5db8e4-685c-45a9-ae45-15290f07a790

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x + y + z) ^ 2 * (21 * (x ^ 2 + y ^ 2 + z ^ 2) + 946 * (x ^ 2 - y * z + y ^ 2 - z * x + z ^ 2 - x * y)) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
