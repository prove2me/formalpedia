-- Prove2me | solution 1 for lean_workbook_plus_31735
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:44:37.01855+00:00
-- url     : https://prove2.me/submissions/43557313-7761-4542-ae61-2c093b320272

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a ≥ b ∧ b ≥ c) :
  (a - b) * (b - c) * (c - a) ≤ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
