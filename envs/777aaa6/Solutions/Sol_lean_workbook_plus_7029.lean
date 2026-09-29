-- Prove2me | solution 1 for lean_workbook_plus_7029
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:03.901087+00:00
-- url     : https://prove2.me/submissions/e1856851-a54e-4eea-984a-c16f344407ee

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x ^ 3 + y ^ 3) * (x + y) ≥ (x ^ 2 + y ^ 2) ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
