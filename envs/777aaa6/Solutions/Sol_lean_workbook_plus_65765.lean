-- Prove2me | solution 1 for lean_workbook_plus_65765
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:50:32.053465+00:00
-- url     : https://prove2.me/submissions/1c72b665-e875-46f6-90c0-0f752e214644

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (4*a + 11*b) / (6*a + 13*b + c) + (4*b + 11*c) / (a + 6*b + 13*c) + (4*c + 11*a) / (13*a + b + 6*c) ≤ 9 / 4 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
