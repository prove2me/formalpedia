-- Prove2me | solution 1 for lean_workbook_plus_18990
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:57:28.106723+00:00
-- url     : https://prove2.me/submissions/9f7fdeab-9f31-403b-88fa-42c4e0bdb17d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hc : c ≥ b ∧ b ≥ a ∧ a ≥ 0) :
  (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
