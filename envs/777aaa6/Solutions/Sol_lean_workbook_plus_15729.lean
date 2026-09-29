-- Prove2me | solution 1 for lean_workbook_plus_15729
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:54.671846+00:00
-- url     : https://prove2.me/submissions/2c9f3689-4b8d-4efc-b4fc-3fee7624ddb1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : 3 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ (x + y + z) ^ 2 ∧ (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
