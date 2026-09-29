-- Prove2me | solution 1 for lean_workbook_plus_79982
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:00:20.497521+00:00
-- url     : https://prove2.me/submissions/77033b60-b686-426f-a9cd-fda5cf49d4e5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x > 0 ∧ y > 0 ∧ z > 0 ∧ x * (y * y + y * z + z * z) = 3 * y + 10 * z ∧ y * (z * z + z * x + x * x) = 21 * z + 24 * x ∧ z * (x * x + x * y + y * y) = 7 * x + 28 * y) → x * y + y * z + z * x = 31 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
