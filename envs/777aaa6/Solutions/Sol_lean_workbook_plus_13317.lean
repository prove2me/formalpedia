-- Prove2me | solution 1 for lean_workbook_plus_13317
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:39.143041+00:00
-- url     : https://prove2.me/submissions/bf60cccd-d0b0-4e69-aa5e-0a7006d484fb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : 3 = x * y + y * z + z * x) : 3 * (x + y) * (x + z) * (y + z) * (x + y + z) ≥ 2 * (x ^ 2 + y ^ 2 + z ^ 2 + 6) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
