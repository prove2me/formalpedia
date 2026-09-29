-- Prove2me | solution 1 for lean_workbook_plus_37346
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:55.341277+00:00
-- url     : https://prove2.me/submissions/97b41591-2cf6-41b9-8262-a83beddd80be

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h₁ : x + y + z = 5) (h₂ : x * y + y * z + z * x = 3) : -1 ≤ z ∧ z ≤ 13 / 3 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
