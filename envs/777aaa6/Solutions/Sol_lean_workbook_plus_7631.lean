-- Prove2me | solution 1 for lean_workbook_plus_7631
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:53.61013+00:00
-- url     : https://prove2.me/submissions/2e7d6690-e9b5-4a5b-85cd-d6a3c0229240

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 1 ≤ a ∧ a ≤ 2) (hb : 1 ≤ b ∧ b ≤ 2) (hc : 1 ≤ c ∧ c ≤ 2): 2 * (a * b + b * c + c * a) ≥ a^2 + b^2 + c^2 + a + b + c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
