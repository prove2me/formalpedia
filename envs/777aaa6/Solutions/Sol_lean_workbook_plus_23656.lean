-- Prove2me | solution 1 for lean_workbook_plus_23656
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:46:46.77765+00:00
-- url     : https://prove2.me/submissions/9217b3c2-de5b-4722-a5d5-2542c1420fc5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / a + (c + a) / b + (a + b) / c ≥ 3 + (a^2 + b^2 + c^2) * (a * b + b * c + c * a) / (a * b * c * (a + b + c)) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
