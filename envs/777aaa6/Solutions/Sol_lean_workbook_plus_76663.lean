-- Prove2me | solution 1 for lean_workbook_plus_76663
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:27:46.488094+00:00
-- url     : https://prove2.me/submissions/96ae968b-e58a-40a1-9a25-71993c310ef9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a * b = 1) (ha : 0 < a) (hb : 0 < b) : 1 / (a ^ 2 + b) + 1 / (b + 1) ≤ 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
