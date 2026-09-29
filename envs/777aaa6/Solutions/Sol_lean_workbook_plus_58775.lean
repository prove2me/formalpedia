-- Prove2me | solution 1 for lean_workbook_plus_58775
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:32.323633+00:00
-- url     : https://prove2.me/submissions/88f12e5d-fafe-4752-beaf-142e3d317ede

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) : (a + 1) / (b + 1) + (3 * a + b + 1) / (a + 3 * b + 1) + (6 * a + b + 1) / (a + 6 * b + 1) ≥ 1 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
