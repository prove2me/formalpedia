-- Prove2me | solution 1 for lean_workbook_plus_4332
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:07:56.896109+00:00
-- url     : https://prove2.me/submissions/55d2553b-3703-4bb7-b32b-0980a8fd11c7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : x + y = 7)
  (h₁ : x^2 - y^2 = 21) :
  x = 5 ∧ y = 2 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
