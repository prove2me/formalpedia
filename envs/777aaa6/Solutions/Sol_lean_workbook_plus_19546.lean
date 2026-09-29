-- Prove2me | solution 1 for lean_workbook_plus_19546
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:25.80471+00:00
-- url     : https://prove2.me/submissions/425ee715-5f94-4203-a07b-b88c135d0048

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x d : ℝ) (hx : 0 < x) (hd : 0 < d) : -((27 * d)/4 * x * (d * x - 1)^2) ≤ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (d), sq_nonneg (x - d), sq_nonneg (x + d), mul_pos hx hd])
