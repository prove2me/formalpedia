-- Prove2me | solution 1 for lean_workbook_plus_11047
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:47:37.773262+00:00
-- url     : https://prove2.me/submissions/7ac02f96-153d-473d-aad8-d4c6aaded771

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b + c ≥ 1 / a + 1 / b + 1 / c) :
  a^3 + b^3 + c^3 ≥ (a + b + c)^3 / 9 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
