-- Prove2me | solution 1 for lean_workbook_plus_8906
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:08.51998+00:00
-- url     : https://prove2.me/submissions/805bc6ae-5755-4492-b037-a65a281c4fe1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a * b + b * c + c * a = a * b * c + 2) : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c ≥ 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
