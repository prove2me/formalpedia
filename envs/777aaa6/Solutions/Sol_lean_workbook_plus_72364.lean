-- Prove2me | solution 1 for lean_workbook_plus_72364
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:44.517959+00:00
-- url     : https://prove2.me/submissions/3a65b2b4-f380-4507-95bd-844b9bfbfa43

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z: ℝ) : x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + x ^ 2 * z ^ 2 ≥ x * y * z * (x + y + z) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
