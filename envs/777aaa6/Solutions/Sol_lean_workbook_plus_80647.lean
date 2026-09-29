-- Prove2me | solution 1 for lean_workbook_plus_80647
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:01:22.025527+00:00
-- url     : https://prove2.me/submissions/1ddbfaa3-e1e2-44e5-9851-2da3cc0cfd3f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 3 ≤ x ^ 3 + y ^ 3 + 3 * ((x + y) / 2) ^ 2 * (x + y) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_nonneg hx hy])
