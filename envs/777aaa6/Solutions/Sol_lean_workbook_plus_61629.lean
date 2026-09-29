-- Prove2me | solution 1 for lean_workbook_plus_61629
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:20:08.579964+00:00
-- url     : https://prove2.me/submissions/3c87909d-48c4-483f-98a1-a01c2ce21a91

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ)
  (h₀ : a * b = 9 / 4)
  (h₁ : a + b = 3) :
  a = 3 / 2 ∧ b = 3 / 2 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
