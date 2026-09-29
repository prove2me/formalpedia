-- Prove2me | solution 1 for lean_workbook_plus_6524
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:27.133488+00:00
-- url     : https://prove2.me/submissions/ed3351e0-dc8b-496e-95cc-4d51d0a031be

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h1 : 3 ≤ a ^ 2 + b ^ 2 + a * b) (h2 : a ^ 2 + b ^ 2 + a * b ≤ 6) : 2 ≤ a ^ 4 + b ^ 4 ∧ a ^ 4 + b ^ 4 ≤ 72 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
