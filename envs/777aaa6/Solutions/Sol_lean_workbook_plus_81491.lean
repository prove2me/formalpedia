-- Prove2me | solution 1 for lean_workbook_plus_81491
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:37:50.417611+00:00
-- url     : https://prove2.me/submissions/055da52d-424b-4417-925f-03a74c4f5dbc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 1 / 2 ≤ a ∧ a ≤ 1) (hb : 1 / 2 ≤ b ∧ b ≤ 1) (hc : 1 / 2 ≤ c ∧ c ≤ 1) : a * b + b * c + c * a + 3 / 4 ≥ a + b + c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
