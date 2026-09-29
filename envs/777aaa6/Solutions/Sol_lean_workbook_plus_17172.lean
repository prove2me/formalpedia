-- Prove2me | solution 1 for lean_workbook_plus_17172
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:32.423422+00:00
-- url     : https://prove2.me/submissions/a0c8a356-9b12-4f8b-bda3-ec26b12dee08

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (1 + x ^ 2) * (1 + y ^ 2) ≥ (1 + x * y) ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
