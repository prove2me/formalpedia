-- Prove2me | solution 1 for lean_workbook_plus_58618
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:49.96203+00:00
-- url     : https://prove2.me/submissions/11ac43cb-6ec0-47eb-9d03-9884995eb8b8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) : a^3 + b^3 + c^3 - 3*a*b*c ≥ 2 * ((b + c) / 2 - a)^3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
