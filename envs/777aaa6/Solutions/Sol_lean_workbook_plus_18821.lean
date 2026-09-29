-- Prove2me | solution 1 for lean_workbook_plus_18821
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:57:18.017863+00:00
-- url     : https://prove2.me/submissions/711beb01-5791-4231-8da0-639272e35a59

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ y) (h3 : 0 ≤ z) (h4 : x ≤ y) (h5 : y ≤ z) (h6 : z ≤ x + y) (h7 : 0 ≤ y - x) (h8 : 0 ≤ z - x) (h9 : 0 ≤ z - y) : 2 * (y - x) * (z - x) * (145 * (y - x) * (z - x) + 59 * (z - y) ^ 2) + 2 * x * (z + y - 2 * x) * (461 * (y - x) * (z - x) + 98 * (z - y) ^ 2) + 204 * x ^ 2 * (21 * (y - x) * (z - x) + 5 * (z - y) ^ 2) + 2176 * x ^ 3 * (z + y - 2 * x) + 10 * (z - y) ^ 4 + 1632 * x ^ 4 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_nonneg h1 h2, mul_nonneg h1 h3, mul_nonneg h2 h3])
