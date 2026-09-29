-- Prove2me | solution 1 for lean_workbook_plus_1427
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:28.52185+00:00
-- url     : https://prove2.me/submissions/5a0a7ea2-416a-45c1-8bc2-f2eb258b2093

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : 2 * (x + y) ≥ x * y + 1) : x ^ 2 + y ^ 2 ≥ 1 / 7 * (x ^ 2 * y ^ 2 + 1) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
