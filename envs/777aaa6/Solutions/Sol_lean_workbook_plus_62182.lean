-- Prove2me | solution 1 for lean_workbook_plus_62182
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:09.910006+00:00
-- url     : https://prove2.me/submissions/331a18c5-f56a-4ba5-a471-07e85c19c9d0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z t : ℝ) (h₀ : x = 2 * t + 1) (h₁ : y = 4 - 2 * t) (h₂ : z = 3 * t + 6) (h₃ : 0 < x ∧ 0 < y ∧ 0 < z) : -(1 / 2) < t ∧ t < 2 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (t), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - t), sq_nonneg (y - z), sq_nonneg (y - t), sq_nonneg (z - t), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (x + t), sq_nonneg (y + z), sq_nonneg (y + t), sq_nonneg (z + t)])
