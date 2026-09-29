-- Prove2me | solution 1 for lean_workbook_plus_50358
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:20:47.24377+00:00
-- url     : https://prove2.me/submissions/c8594299-5e01-4d41-9b2b-1af7f843bb29

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z = 1) :
  5 * x * (y + z) ^ 2 + 5 * x * y * z ≥ 4 * x * (y + z) ^ 2 + 9 * x * y * z ∧
  4 * x * (y + z) ^ 2 + 9 * x * y * z ≥ 3 * x * (y + z) ^ 2 + 13 * x * y * z := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
