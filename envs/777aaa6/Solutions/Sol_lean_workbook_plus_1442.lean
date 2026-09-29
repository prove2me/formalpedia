-- Prove2me | solution 1 for lean_workbook_plus_1442
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:23.673466+00:00
-- url     : https://prove2.me/submissions/eb22e85b-2ab1-4fac-8da7-fcdfcb233ab3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (m n : ℝ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : 1 ≤ m * n) : 1 / m ^ 2 + 1 / n ^ 2 ≥ 16 / (1 + 8 * m * n) := by
  (intros; field_simp; nlinarith [sq_nonneg (m), sq_nonneg (n), sq_nonneg (m - n), sq_nonneg (m + n)])
