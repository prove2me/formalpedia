-- Prove2me | solution 2 for lean_workbook_plus_487
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:54.076191+00:00
-- url     : https://prove2.me/submissions/661e337e-cab5-41dd-a7a7-6f80e2d04471

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) (h : a^9 + b^9 = 2) : a^2 / b + b^2 / a ≥ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
