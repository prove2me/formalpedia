-- Prove2me | solution 1 for lean_workbook_plus_65338
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:11.866488+00:00
-- url     : https://prove2.me/submissions/1d003108-5f2e-4296-9416-909848666840

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c) : a^4 + b^4 + c^4 >= (a+b+c)*a*b*c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
