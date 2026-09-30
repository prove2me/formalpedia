-- Prove2me | solution 2 for lean_workbook_plus_75005
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:52:55.204975+00:00
-- url     : https://prove2.me/submissions/9d3f415b-3ece-4faf-a399-640b68ded8e9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a * b * c = 1) :
  (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) ≥ (1 + a) * (1 + b) * (1 + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
