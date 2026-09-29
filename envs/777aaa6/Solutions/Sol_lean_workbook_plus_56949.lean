-- Prove2me | solution 1 for lean_workbook_plus_56949
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:24:03.091839+00:00
-- url     : https://prove2.me/submissions/2014d602-da51-4249-9a3f-d7fa0a990a77

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : 2 ≥ a ∧ a ≥ b ∧ b ≥ c) :
  a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
