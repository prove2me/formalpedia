-- Prove2me | solution 1 for lean_workbook_plus_26298
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:05.679912+00:00
-- url     : https://prove2.me/submissions/36d6dc09-1973-40ae-a630-23fac37ea049

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^2 / b^2) + (b^2 / a^2) ≥ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
