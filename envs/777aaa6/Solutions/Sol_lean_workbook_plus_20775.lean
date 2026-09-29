-- Prove2me | solution 1 for lean_workbook_plus_20775
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:37:03.546381+00:00
-- url     : https://prove2.me/submissions/e9580d92-d4f8-446e-841d-de4f8a28060e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a ≤ 2 * b) (h3 : 2 * b ≤ 5 * a) : a^2 + b^2 ≤ (29 / 10) * a * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
