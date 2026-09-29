-- Prove2me | solution 1 for lean_workbook_plus_19517
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:23.384911+00:00
-- url     : https://prove2.me/submissions/18b91b30-01d4-4849-b33b-485685dc4686

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a ≥ 0 ∧ b ≥ 0) : a^2 + a*b + b^2 ≥ 3/4 * (a + b)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
