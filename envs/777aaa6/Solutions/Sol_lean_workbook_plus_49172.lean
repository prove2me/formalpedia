-- Prove2me | solution 1 for lean_workbook_plus_49172
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:59.411543+00:00
-- url     : https://prove2.me/submissions/cdbb8fcd-7b74-4924-87f0-34e40997e7e1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a ^ 3 * b + b ^ 3 * c + c ^ 3 * a = 2 / 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 4 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
