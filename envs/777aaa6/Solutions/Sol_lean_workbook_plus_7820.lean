-- Prove2me | solution 1 for lean_workbook_plus_7820
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:00.713163+00:00
-- url     : https://prove2.me/submissions/c3747a66-709a-4147-a24c-01da4a54c60d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c) :
  a^3 + b^3 + c^3 ≥ a^2 + b^2 + c^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
