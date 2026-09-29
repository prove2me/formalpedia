-- Prove2me | solution 1 for lean_workbook_plus_21142
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:23.381574+00:00
-- url     : https://prove2.me/submissions/a14059de-1dce-471f-8110-6b70e7ec067c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / (1 + a) - 1 / (1 + b) + a / (a + b) < 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
