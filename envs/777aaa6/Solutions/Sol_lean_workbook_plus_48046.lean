-- Prove2me | solution 1 for lean_workbook_plus_48046
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:50:27.918125+00:00
-- url     : https://prove2.me/submissions/b5547d74-1bcb-41a9-bc2a-0ca84134d3d3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h : a^3 * b + a * b^3 = 2 / 9) : a^2 + b^2 + a * b ≥ 1 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
