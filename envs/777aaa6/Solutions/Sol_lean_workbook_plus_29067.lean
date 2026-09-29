-- Prove2me | solution 1 for lean_workbook_plus_29067
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:48.077446+00:00
-- url     : https://prove2.me/submissions/1c6eb3c7-5af2-4962-9755-ab5be00c3494

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1: 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) (h2: a ≤ b ∧ b ≤ c) : (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
