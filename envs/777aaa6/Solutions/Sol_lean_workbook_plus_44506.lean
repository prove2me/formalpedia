-- Prove2me | solution 1 for lean_workbook_plus_44506
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:27:49.885576+00:00
-- url     : https://prove2.me/submissions/903da66a-76f0-4a1b-ba1e-20ca8b8ad98e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) : a^2 / (a^2 + a + 1) + b^2 / (b^2 + b + 1) + c^2 / (c^2 + c + 1) ≥ 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
