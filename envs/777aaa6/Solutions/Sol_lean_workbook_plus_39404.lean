-- Prove2me | solution 1 for lean_workbook_plus_39404
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:36.838277+00:00
-- url     : https://prove2.me/submissions/0261d74a-10d5-42a2-b935-b4c6c0e28739

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
  -1 ≤ x * y * (y ^ 2 - x ^ 2) ∧ x * y * (y ^ 2 - x ^ 2) ≤ 1 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
