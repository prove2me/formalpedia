-- Prove2me | solution 1 for lean_workbook_plus_67538
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:57.026508+00:00
-- url     : https://prove2.me/submissions/f30d54b2-1712-4187-9e67-d8eb6ca19c67

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) : (a / (a + 1) * b + 1) + (b / (b + 1) * c + 1) + (c / (c + 1) * a + 1) ≥ 3 / 4 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
