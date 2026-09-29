-- Prove2me | solution 1 for lean_workbook_plus_7570
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:59:38.010772+00:00
-- url     : https://prove2.me/submissions/cdaa89b0-bccf-4684-b1e5-0c4478e9d1a4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) : 1 ≤ x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2 ∧ x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2 ≤ 3 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
