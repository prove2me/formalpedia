-- Prove2me | solution 1 for lean_workbook_plus_62911
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:07.340417+00:00
-- url     : https://prove2.me/submissions/4ab4d9a7-dbb5-45d0-bc66-d8914776356f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a * b = 6)
  (h₂ : a^3 + b^3 = 22)
  (h₃ : x = a + b) :
  x^3 + 18 * x = 22 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (a), sq_nonneg (b), sq_nonneg (x - a), sq_nonneg (x - b), sq_nonneg (a - b), sq_nonneg (x + a), sq_nonneg (x + b), sq_nonneg (a + b)])
