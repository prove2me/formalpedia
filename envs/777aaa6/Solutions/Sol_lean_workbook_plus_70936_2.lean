-- Prove2me | solution 2 for lean_workbook_plus_70936
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:35.162511+00:00
-- url     : https://prove2.me/submissions/50092bbe-7827-42f6-a898-24a3fc713f21

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (habc : a * b * c = 3) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) : (a + 1) * (b + 1) * (c + 1) ≥ 8 * (a - 1) * (b - 1) * (c - 1) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
