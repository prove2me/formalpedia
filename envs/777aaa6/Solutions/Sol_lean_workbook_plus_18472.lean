-- Prove2me | solution 1 for lean_workbook_plus_18472
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:49.948339+00:00
-- url     : https://prove2.me/submissions/40bc4a12-dfc3-45b9-b453-22d6bce858cf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (l_a l_b l_c : ℝ) : (l_a * l_b + l_b * l_c + l_c * l_a) ^ 2 ≤ 3 * (l_a ^ 2 * l_b ^ 2 + l_b ^ 2 * l_c ^ 2 + l_c ^ 2 * l_a ^ 2) := by
  (intros; nlinarith [sq_nonneg (l_a), sq_nonneg (l_b), sq_nonneg (l_c), sq_nonneg (l_a - l_b), sq_nonneg (l_a - l_c), sq_nonneg (l_b - l_c), sq_nonneg (l_a + l_b), sq_nonneg (l_a + l_c), sq_nonneg (l_b + l_c)])
