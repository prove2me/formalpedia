-- Prove2me | solution 1 for lean_workbook_plus_56716
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:45.214765+00:00
-- url     : https://prove2.me/submissions/fda1f7c5-0028-40ca-b234-608499e45c05

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ)
  (h₀ : a + b + c = 1) :
  a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
