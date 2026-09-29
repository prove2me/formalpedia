-- Prove2me | solution 1 for lean_workbook_plus_66382
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:32:15.965458+00:00
-- url     : https://prove2.me/submissions/d8945b48-2727-4766-92f0-8884ed1e643c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (a + c) + c / (a + b)) ≥ 3 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
